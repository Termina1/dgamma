#!/usr/bin/env python3
"""Persist R181 exact per-attempt evidence and verify serialized intervals."""
import hashlib
import json
import pathlib
import re
import subprocess
import tarfile
ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = pathlib.Path('/tmp/dgamma-r181')
records = [json.loads(line) for line in (OUT/'ledger.jsonl').read_text().splitlines()]
records.sort(key=lambda r:r['start'])
assert all(a['end'] <= b['start'] for a,b in zip(records,records[1:]))
accepted_names = {}
for r in records:
    snapshot = (OUT/(r['unit']+'.source')).read_bytes()
    assert hashlib.sha256(snapshot).hexdigest() == r['sourceSHA256']
    if r['path'] != 'package':
        names = set(re.findall(r'^(?:0 )?([A-Za-z_]\w*)\s*:',snapshot.decode(),re.M))
        names.update(re.findall(r'^record ([A-Za-z_]\w*)',snapshot.decode(),re.M))
        if r['path'] not in accepted_names:
            baseline = subprocess.run(['git','show','5871236:'+r['path']],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.DEVNULL)
            base_text = baseline.stdout.decode() if baseline.returncode == 0 else ''
            base_names = set(re.findall(r'^(?:0 )?([A-Za-z_]\w*)\s*:',base_text,re.M))
            base_names.update(re.findall(r'^record ([A-Za-z_]\w*)',base_text,re.M))
            accepted_names[r['path']] = base_names
            if base_names:
                r['baselineDeclarationSource'] = '5871236:'+r['path']
        prior = accepted_names[r['path']]
        assert not prior - names, (r['unit'],'removed accepted declaration')
        added = sorted(names - prior)
        assert len(added) <= 1, (r['unit'],added)
        r['newTopLevelDeclarations'] = added
        if r['passed']:
            accepted_names[r['path']] = names
    assert (OUT/(r['unit']+'.log')).read_text() == r['transcript']
    history = subprocess.check_output(['git','log','--reverse','--format=%H','5871236..HEAD','--',r['path']],cwd=ROOT,text=True).splitlines()
    r['matchingSourceCommits'] = []
    for commit in history:
        result = subprocess.run(['git','show',commit+':'+r['path']],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.DEVNULL)
        if result.returncode == 0 and hashlib.sha256(result.stdout).hexdigest() == r['sourceSHA256']:
            r['matchingSourceCommits'].append(commit)
(ROOT/'research-tests/O6-R181-COMPILER-LEDGER.json').write_text(json.dumps(records,indent=2)+'\n')
with tarfile.open(ROOT/'research-tests/O6-R181-COMPILER-EVIDENCE.tar.gz','w:gz') as archive:
    for r in records:
        for suffix in ['.source','.log','.json','.runner']:
            path = OUT/(r['unit']+suffix)
            if path.exists():
                archive.add(path,arcname=path.name)
summary = dict(checks=len(records),ordinaryPasses=sum(r['passed'] and not r['expectedDiagnostic'] for r in records),
    intendedNegativePasses=sum(r['passed'] and bool(r['expectedDiagnostic']) for r in records),
    rejectedOrInterrupted=sum(not r['passed'] for r in records),serialized=True,oneNewDeclarationPerInvocation=True,
    seededPackageBuilds=sum(r['path']=='package' for r in records),
    units=[dict(unit=r['unit'],passed=r['passed'],fresh=r['fresh'],seconds=r['seconds'],commits=r['matchingSourceCommits']) for r in records])
(OUT/'evidence-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
