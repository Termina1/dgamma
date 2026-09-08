#!/usr/bin/env python3
"""Persist R185 exact per-attempt evidence and verify serialized intervals."""
import datetime
import hashlib
import json
import pathlib
import re
import subprocess
import tarfile
ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = pathlib.Path('/tmp/dgamma-r185')
records = [json.loads(line) for line in (OUT/'ledger.jsonl').read_text().splitlines()]
records.sort(key=lambda r:r['start'])
assert all(a['end'] <= b['start'] for a,b in zip(records,records[1:]))
accepted_names = {}
for r in records:
    snapshot = (OUT/(r['unit']+'.source')).read_bytes()
    assert hashlib.sha256(snapshot).hexdigest() == r['sourceSHA256']
    if r['path'] != 'package':
        names = set(re.findall(r'^(?:0 )?([A-Za-z_]\w*)\s*:',snapshot.decode(),re.M))
        names.update(re.findall(r'^(?:record|data) ([A-Za-z_]\w*)',snapshot.decode(),re.M))
        if r['path'] not in accepted_names:
            baseline = subprocess.run(['git','show','324dc4ae:'+r['path']],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.DEVNULL)
            base_text = baseline.stdout.decode() if baseline.returncode == 0 else ''
            base_names = set(re.findall(r'^(?:0 )?([A-Za-z_]\w*)\s*:',base_text,re.M))
            base_names.update(re.findall(r'^(?:record|data) ([A-Za-z_]\w*)',base_text,re.M))
            accepted_names[r['path']] = base_names
            if base_names:
                r['baselineDeclarationSource'] = '324dc4ae:'+r['path']
        prior = accepted_names[r['path']]
        assert not prior - names, (r['unit'],'removed accepted declaration')
        added = sorted(names - prior)
        assert len(added) <= 1, (r['unit'], added)
        r['newTopLevelDeclarations'] = added
        if r['passed']:
            accepted_names[r['path']] = names
    assert (OUT/(r['unit']+'.log')).read_text() == r['transcript']
    # Unchanged frozen regression fixtures/package belong to the authenticated
    # baseline, not to a nonexistent change commit inside 324dc4ae..HEAD.
    baseline_commit = subprocess.check_output(['git','rev-parse','324dc4ae'],cwd=ROOT,text=True).strip()
    tracked_path = 'dgamma.ipkg' if r['path'] == 'package' else r['path']
    history = [baseline_commit] + subprocess.check_output(['git','log','--reverse','--format=%H','324dc4ae..HEAD','--',tracked_path],cwd=ROOT,text=True).splitlines()
    r['matchingSourceCommits'] = []
    for commit in history:
        result = subprocess.run(['git','show',commit+':'+tracked_path],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.DEVNULL)
        if result.returncode == 0 and hashlib.sha256(result.stdout).hexdigest() == r['sourceSHA256']:
            r['matchingSourceCommits'].append(commit)
# Check every committed Idris source change, not just the final file hashes.
# Git timestamps have one-second resolution; the compiler end has fractions.
proof_commits = []
commits = subprocess.check_output(['git','log','--reverse','--format=%H','324dc4ae..HEAD','--',
    'research/','research-tests/DGamma/'],cwd=ROOT,text=True).splitlines()
for commit in commits:
    stamp = int(subprocess.check_output(['git','show','-s','--format=%ct',commit],cwd=ROOT,text=True))
    paths = subprocess.check_output(['git','diff-tree','--no-commit-id','--name-only','-r',commit,
        '--','research/','research-tests/DGamma/'],cwd=ROOT,text=True).splitlines()
    for path in paths:
        if not path.endswith('.idr'):
            continue
        blob = subprocess.run(['git','show',commit+':'+path],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.DEVNULL)
        if blob.returncode:
            continue
        digest = hashlib.sha256(blob.stdout).hexdigest()
        candidates = [r for r in records if r['path']==path and r['sourceSHA256']==digest
            and r['passed'] and r['fresh'] and not r['expectedDiagnostic']
            and datetime.datetime.fromisoformat(r['end']).timestamp() < stamp+1]
        assert candidates, ('source commit lacks a prior fresh ordinary PASS',commit,path)
        proof_commits.append(dict(commit=commit,path=path,check=candidates[0]['unit'],
            passedAt=candidates[0]['end'],sourceSHA256=digest))
assert all(not r['matchingSourceCommits'] for r in records if not r['passed']), 'rejected source committed'
attempts = {}
for r in records:
    match = re.fullmatch(r'((?:A|AO|OO|B|C|D|E|F)\d+)-(\d+)',r['unit'])
    if match:
        attempts.setdefault(match[1],[]).append(int(match[2]))
assert all(len(v)<=3 and v==list(range(1,len(v)+1)) for v in attempts.values()), attempts
for prefix, limit in [('A',16),('AO',10),('OO',10),('B',14),('D',16),('E',12),('F',8),('C',8)]:
    assert sum(bool(re.fullmatch(prefix+r'\d+',k)) for k in attempts) <= limit
(ROOT/'research-tests/O6-R185-COMPILER-LEDGER.json').write_text(json.dumps(records,indent=2)+'\n')
with tarfile.open(ROOT/'research-tests/O6-R185-COMPILER-EVIDENCE.tar.gz','w:gz') as archive:
    for r in records:
        for suffix in ['.source','.log','.json','.runner']:
            path = OUT/(r['unit']+suffix)
            if path.exists():
                archive.add(path,arcname=path.name)
    for path in [OUT/'ledger.jsonl'] + sorted(OUT.glob('*frozen.json')):
        if path.exists():
            archive.add(path,arcname=path.name)
    for name in ['final-regressions.py', 'final-regressions.json']:
        path = OUT/name
        if path.exists():
            archive.add(path,arcname=name)
summary = dict(checks=len(records),ordinaryPasses=sum(r['passed'] and not r['expectedDiagnostic'] for r in records),
    intendedNegativePasses=sum(r['passed'] and bool(r['expectedDiagnostic']) for r in records),
    rejectedOrInterrupted=sum(not r['passed'] for r in records),
    compilerRejections=sum(not r['passed'] and not r['interrupted'] for r in records),
    interruptions=sum(r['interrupted'] for r in records),serialized=True,
    oneNewDeclarationPerInvocation=all(len(r.get('newTopLevelDeclarations', [])) <= 1 for r in records),
    workflowViolations=[dict(unit=r['unit'],detail=r['workflowViolation']) for r in records if 'workflowViolation' in r],
    seededPackageBuilds=sum(r['path']=='package' for r in records),
    attemptCapsVerified=attempts,priorFreshPassForEverySourceCommit=proof_commits,
    rejectedSourcesAbsentFromRetainedHistory=True,protocolCommitOnlyFreshPassSatisfied=False,
    droppedMislabeledCommit='8d553e00',dropAuthorizedLocalOnly=True,
    monitorInterruption='D3-1: foreground timeout killed wrapper; isolated compiler reconciled/terminated, peak not fully retained',
    retainedNewDeclarations=sum(len(r.get('newTopLevelDeclarations',[])) for r in records if r['passed'] and not r['expectedDiagnostic']),
    ledgerSHA256=hashlib.sha256((ROOT/'research-tests/O6-R185-COMPILER-LEDGER.json').read_bytes()).hexdigest(),
    archiveSHA256=hashlib.sha256((ROOT/'research-tests/O6-R185-COMPILER-EVIDENCE.tar.gz').read_bytes()).hexdigest(),
    units=[dict(unit=r['unit'],passed=r['passed'],fresh=r['fresh'],seconds=r['seconds'],commits=r['matchingSourceCommits']) for r in records])
(OUT/'evidence-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
