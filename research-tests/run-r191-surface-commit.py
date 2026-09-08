#!/usr/bin/env python3
"""ONE supervisor-authorized R191 four-module argument-plumbing commit.
Own fresh serial source checks SUR1..SUR4 are mandatory; no blanket bypass.
"""
import datetime, hashlib, json, pathlib, re, subprocess
ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = pathlib.Path('/tmp/dgamma-r191')
paths = ['research/DGamma/CP5O20'+n+'Spike.idr' for n in ['LinearExtension','OperationalProgress','OperationalDescent','ReferenceDescent']]
units = ['SUR1','SUR2','SUR3','SUR4']
records = [json.loads((OUT/(u+'.json')).read_text()) for u in units]
ledger = [json.loads(s) for s in (OUT/'ledger.jsonl').read_text().splitlines()]
assert [r['unit'] for r in ledger[-4:]] == units
assert len([s for s in (OUT/'commit-receipts.jsonl').read_text().splitlines() if 'GUARDED SURFACE COMMIT' in s]) == 0
for path,r in zip(paths,records):
    assert r['path'] == path and r['passed'] and r['fresh'] and r['exit'] == 0 and not r['interrupted'] and not r['expectedDiagnostic']
    assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == r['sourceSHA256']
for a,b in zip(records,records[1:]): assert a['end'] <= b['start']
def git(*args): return subprocess.check_output(['git',*args],cwd=ROOT,text=True)
assert not git('diff','--cached','--name-only')
assert set(git('diff','--name-only','--','research/','src/','dgamma.ipkg').splitlines()) == set(paths)
assert not git('diff','5ae5266f','--','research/DGamma/CP5ConfluenceCrossTraceSpike.idr','research/DGamma/CP5ConfluenceLocalDiamondSpike.idr','research/DGamma/CP5O19SurfaceSpike.idr')
assert not git('diff','34b21c9','--','src/','dgamma.ipkg')
assert not re.search(r'/idris2_app/idris2(?:\.so)?(?:\s|$)',subprocess.check_output(['ps','-axo','pid,ppid,command'],text=True))
subprocess.run(['git','diff','--check'],cwd=ROOT,check=True)
extra = ['research-tests/run-r191-surface-commit.py','research-tests/O6-R191-GRIND-SHIFT-AUDIT.md']
subprocess.run(['git','add','--',*paths,*extra],cwd=ROOT,check=True)
subprocess.run(['git','commit','-m','R191 C surface: thread exact goal uniqueness instead of unused full-path state'],cwd=ROOT,check=True)
assert not git('diff','--cached','--name-only')
receipt=dict(event='GUARDED SURFACE COMMIT',unit='C-surface',invocations=units,resultingCommitHash=git('rev-parse','HEAD').strip(),timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),sourceHashes={r['path']:r['sourceSHA256'] for r in records},guardChecksPassed=['ONE explicitly supervisor-approved exception','all four exact own-Building fresh PASS','four serial invocations latest in ledger','exact source hashes','exact four source paths','no protected/production delta','no pre-staged files','no compiler','git diff --check','git commit success','no post-staged files'])
with (OUT/'commit-receipts.jsonl').open('a') as f:f.write(json.dumps(receipt)+'\n')
print('GUARDED SURFACE COMMIT',json.dumps(receipt),flush=True)
