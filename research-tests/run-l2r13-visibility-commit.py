#!/usr/bin/env python3
"""Supervisor-authorized L2R13 B10 visibility-only commit after exact V0 PASS.
No type/body/multiplicity changes; exact hash/text ruling checked before stage.
Usage: python3 -I research-tests/run-l2r13-visibility-commit.py V0 MESSAGE
"""
import datetime
import hashlib
import json
import pathlib
import re
import subprocess
import sys
ROOT = pathlib.Path('/Users/vyacheslavshebanov/Work/dgamma-lane2')
unit, message = sys.argv[1:3]
record = json.loads((pathlib.Path('/tmp/dgamma-l2r13')/(unit+'.json')).read_text())
assert record['passed'] and record['fresh'] and not record['interrupted'] and not record['sourceMutationObserved']
assert record['exit'] == 0 and not record['expectedDiagnostic']
assert json.loads(pathlib.Path('/tmp/dgamma-l2r13/ledger.jsonl').read_text().splitlines()[-1])['unit'] == unit, 'No intervening compiler invocation'
source_attempt = unit
assert unit == 'V0'
authority=json.loads(pathlib.Path('/tmp/dgamma-l2r13/VISIBILITY-RULING.json').read_text())
assert record['path']==authority['path']
assert record['sourceSHA256']==authority['afterSHA256']
assert record['buildingCount'] == 1
assert record['maxSampleRSSKiB'] <= 18*1024*1024, 'Light-only shift runner; heavy requires prior declared ledger and separate guarded authority'
old = subprocess.run(['git','show','HEAD:'+record['path']],cwd=ROOT,capture_output=True)
def declarations(data):
    text = data.decode()
    return set(re.findall(r'^(?:[01] )?([A-Za-z_]\w*)\s*:',text,re.M) + re.findall(r'^(?:record|data)\s+([A-Za-z_]\w*)',text,re.M))
assert old.returncode==0
assert hashlib.sha256(old.stdout).hexdigest()==authority['beforeSHA256']
assert old.stdout.count(authority['old'].encode())==1
assert old.stdout.replace(authority['old'].encode(),authority['new'].encode())==(ROOT/record['path']).read_bytes()
assert declarations((ROOT/record['path']).read_bytes())==declarations(old.stdout)
assert record['path'].startswith(('research-tests/O6-L2R13-Sources/',)), 'Lane-owned source only'
source = ROOT/record['path']
commitPaths=[record['path']]
assert not record.get('bundleSources'), 'No companion bundle authorized'
if record.get('bundleSources'):
 assert record['bundleFresh']
 for extra in record['bundleSources']:
  assert hashlib.sha256((ROOT/extra['path']).read_bytes()).hexdigest()==extra['sourceSHA256']
  commitPaths.append(extra['path'])
assert hashlib.sha256(source.read_bytes()).hexdigest() == record['sourceSHA256']
assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=ROOT,text=True).strip()
processes = subprocess.check_output(['ps','-axo','pid,ppid,command'],text=True)
assert not any('/idris2_app/idris2' in row and str(ROOT)+'/' in row and re.match(r'^\s*\d+\s+\d+\s+(?:\S*/)?(?:chez|scheme|chezscheme|idris2(?:\.so)?)(?:\s|$)',row) for row in processes.splitlines()), 'Own compiler running; main-lane compilers are separate'
assert subprocess.check_output(['git','branch','--show-current'],cwd=ROOT,text=True).strip() == 'cp5-thm73-lane-a8a10'
subprocess.run(['git','diff','--check'],cwd=ROOT,check=True)
subprocess.run(['git','add','--',*commitPaths],cwd=ROOT,check=True)
subprocess.run(['git','commit','-m',message],cwd=ROOT,check=True)
assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=ROOT,text=True).strip()
receipt = dict(paths=commitPaths,sourceHashes={record['path']:record['sourceSHA256'],**{x['path']:x['sourceSHA256'] for x in record.get('bundleSources',[])}},event='GUARDED VISIBILITY COMMIT', authority=authority, unit='B10-visibility', attempt='V0', invocation=unit, sourceAttempt=source_attempt, rstripOnlyRevalidation=False, sourceHash=record['sourceSHA256'], resultingCommitHash=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(), timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(), guardChecksPassed=['fresh PASS','exit 0','not interrupted','no expected diagnostic','exact source SHA256','exact authorized visibility-only correction; zero declaration delta','no intervening compiler invocation','no pre-staged files','no compiler','git diff --check','git commit success','no post-staged files'])
with pathlib.Path('/tmp/dgamma-l2r13/commit-receipts.jsonl').open('a') as ledger:
    ledger.write(json.dumps(receipt)+'\n')
print('GUARDED COMMIT',json.dumps(receipt),flush=True)
