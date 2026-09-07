#!/usr/bin/env python3
"""Persist R183 exact per-attempt evidence and verify serialized intervals."""
import datetime
import hashlib
import json
import pathlib
import re
import subprocess
import tarfile
ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = pathlib.Path('/tmp/dgamma-r183')
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
            baseline = subprocess.run(['git','show','973a81a:'+r['path']],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.DEVNULL)
            base_text = baseline.stdout.decode() if baseline.returncode == 0 else ''
            base_names = set(re.findall(r'^(?:0 )?([A-Za-z_]\w*)\s*:',base_text,re.M))
            base_names.update(re.findall(r'^(?:record|data) ([A-Za-z_]\w*)',base_text,re.M))
            accepted_names[r['path']] = base_names
            if base_names:
                r['baselineDeclarationSource'] = '973a81a:'+r['path']
        prior = accepted_names[r['path']]
        assert not prior - names, (r['unit'],'removed accepted declaration')
        added = sorted(names - prior)
        assert len(added) <= 1, (r['unit'], added)
        r['newTopLevelDeclarations'] = added
        if r['passed']:
            accepted_names[r['path']] = names
    assert (OUT/(r['unit']+'.log')).read_text() == r['transcript']
    # Unchanged frozen regression fixtures/package belong to the authenticated
    # baseline, not to a nonexistent change commit inside 973a81a..HEAD.
    baseline_commit = subprocess.check_output(['git','rev-parse','973a81a'],cwd=ROOT,text=True).strip()
    tracked_path = 'dgamma.ipkg' if r['path'] == 'package' else r['path']
    history = [baseline_commit] + subprocess.check_output(['git','log','--reverse','--format=%H','973a81a..HEAD','--',tracked_path],cwd=ROOT,text=True).splitlines()
    r['matchingSourceCommits'] = []
    for commit in history:
        result = subprocess.run(['git','show',commit+':'+tracked_path],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.DEVNULL)
        if result.returncode == 0 and hashlib.sha256(result.stdout).hexdigest() == r['sourceSHA256']:
            r['matchingSourceCommits'].append(commit)
# Check every committed Idris source change, not just the final file hashes.
# Git timestamps have one-second resolution; the compiler end has fractions.
proof_commits = []
commits = subprocess.check_output(['git','log','--reverse','--format=%H','973a81a..HEAD','--',
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
    match = re.fullmatch(r'([ABC]\d+)-(\d+)',r['unit'])
    if match:
        attempts.setdefault(match[1],[]).append(int(match[2]))
assert all(len(v)<=3 and v==list(range(1,len(v)+1)) for v in attempts.values()), attempts
assert sum(k.startswith('A') for k in attempts)<=30
assert sum(k.startswith('B') for k in attempts)==1 and len(attempts['B1'])<=3
assert sum(k.startswith('C') for k in attempts)<=8
assert not (ROOT/'research-tests/DGamma/R183O20SelectorProbe.idr').exists(), 'disposable probe retained'
actual_domain = (ROOT/'research/DGamma/CP5O19ActualCommutedDomainSpike.idr').read_text()
assert 'o19PairEarlyEffectRunObserved' not in actual_domain, 'exhausted A25 consumer retained'
assert set(re.findall(r'^0 ([A-Za-z_]\w*)\s*:',actual_domain,re.M)) == {
    'o19ActualForwardMapAt','o19ActualPairMapCommutes','o19ActualFrameRelated'}
(ROOT/'research-tests/O6-R183-COMPILER-LEDGER.json').write_text(json.dumps(records,indent=2)+'\n')
with tarfile.open(ROOT/'research-tests/O6-R183-COMPILER-EVIDENCE.tar.gz','w:gz') as archive:
    for r in records:
        for suffix in ['.source','.log','.json','.runner']:
            path = OUT/(r['unit']+suffix)
            if path.exists():
                archive.add(path,arcname=path.name)
    for name in ['run-regressions.py','regressions.runner','A-stop-frozen.json','C-stop-frozen.json']:
        path=OUT/name
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
    rejectedSourcesNotCommitted=True,exhaustedA25ConsumerAbsent=True,disposableO20ProbeAbsent=True,
    retainedNewDeclarations=sum(len(r.get('newTopLevelDeclarations',[])) for r in records if r['passed'] and not r['expectedDiagnostic']),
    ledgerSHA256=hashlib.sha256((ROOT/'research-tests/O6-R183-COMPILER-LEDGER.json').read_bytes()).hexdigest(),
    archiveSHA256=hashlib.sha256((ROOT/'research-tests/O6-R183-COMPILER-EVIDENCE.tar.gz').read_bytes()).hexdigest(),
    units=[dict(unit=r['unit'],passed=r['passed'],fresh=r['fresh'],seconds=r['seconds'],commits=r['matchingSourceCommits']) for r in records])
(OUT/'evidence-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
