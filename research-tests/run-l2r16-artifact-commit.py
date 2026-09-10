#!/usr/bin/env python3
"""Copied from L2R15: guarded L2R16 NON-IDRIS artifact publication following
an exact source PASS. No predecessor, protected document or source edits.
Usage: python3 -I research-tests/run-l2r16-artifact-commit.py UNIT MESSAGE PATH...
"""
import datetime,hashlib,json,pathlib,re,subprocess,sys
ROOT=pathlib.Path('/Users/vyacheslavshebanov/Work/dgamma-lane2');OUT=pathlib.Path('/tmp/dgamma-l2r16')
def git(*a):return subprocess.check_output(['git',*a],cwd=ROOT)
def sha(b):return hashlib.sha256(b).hexdigest()
assert pathlib.Path.cwd()==ROOT
unit,message,*paths=sys.argv[1:]
r=json.loads((OUT/(unit+'.json')).read_text())
assert r['passed'] and r['fresh'] and r['exit']==0 and not r['interrupted'] and not r['sourceMutationObserved']
assert json.loads((OUT/'ledger.jsonl').read_text().splitlines()[-1])['unit']==unit
assert sha((ROOT/r['path']).read_bytes())==r['sourceSHA256']
assert paths and len(paths)==len(set(paths))
assert all(p.startswith(('research-tests/O6-L2R16-','research-tests/run-l2r16-')) and not p.endswith('.idr') and (ROOT/p).is_file() for p in paths)
assert not git('diff','--cached','--name-only').strip()
assert set(git('diff','--name-only').decode().splitlines())<=set(paths)
processes=subprocess.check_output(['ps','-axo','pid,ppid,command'],text=True)
assert not any('/idris2_app/idris2' in row and str(ROOT)+'/' in row and re.match(r'^\s*\d+\s+\d+\s+(?:\S*/)?(?:chez|scheme|chezscheme|idris2(?:\.so)?)(?:\s|$)',row) for row in processes.splitlines())
assert git('branch','--show-current').decode().strip()=='cp5-thm73-lane-a8a10'
subprocess.run(['git','diff','--check'],check=True)
hashes={p:sha((ROOT/p).read_bytes()) for p in paths}
subprocess.run(['git','add','--',*paths],check=True)
assert set(git('diff','--cached','--name-only').decode().splitlines())<=set(paths)
subprocess.run(['git','commit','-m',message],check=True)
assert not git('diff','--cached','--name-only').strip()
receipt=dict(event='GUARDED ARTIFACT COMMIT',unit=unit,invocation=unit,sourceHash=r['sourceSHA256'],resultingCommitHash=git('rev-parse','HEAD').decode().strip(),timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),paths=paths,artifactHashes=hashes,guardChecksPassed=['exact fresh PASS','no intervening compiler','artifact paths only','no staged files before/after','no own compiler','git diff --check'])
with (OUT/'commit-receipts.jsonl').open('a') as f:f.write(json.dumps(receipt)+'\n')
print(json.dumps(receipt),flush=True)
