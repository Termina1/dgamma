#!/usr/bin/env python3
"""Commit exactly one source only after an authenticated fresh PASS.
Usage: python3 -I research-tests/run-r199-commit.py UNIT MESSAGE
All checks and git commands share one exception-stopping process.
"""
import datetime
import hashlib
import json
import pathlib
import re
import subprocess
import sys
ROOT = pathlib.Path(__file__).resolve().parents[1]
def compiler_scopes():
    owned, lane2, unknown = [], [], []
    for row in subprocess.check_output(['ps','-axo','pid,ppid,command'], text=True).splitlines():
        cells = row.strip().split(None, 2)
        if len(cells) != 3 or not re.search(r'/idris2_app/idris2(?:\.so)?(?:\s|$)', cells[2]):
            continue
        cwd_probe = subprocess.run(['lsof','-a','-p',cells[0],'-d','cwd','-Fn'],capture_output=True,text=True)
        directories = [line[1:] for line in cwd_probe.stdout.splitlines() if line.startswith('n')]
        if str(ROOT)+'/' in cells[2] or str(ROOT) in directories:
            owned.append(row)
        elif '/Users/vyacheslavshebanov/Work/dgamma-lane2/' in cells[2] or '/Users/vyacheslavshebanov/Work/dgamma-lane2' in directories:
            lane2.append(row)
        else:
            unknown.append(row)
    return owned, lane2, unknown

unit, message = sys.argv[1:3]
record = json.loads((pathlib.Path('/tmp/dgamma-r199')/(unit+'.json')).read_text())
assert record['passed'] and record['fresh'] and not record['interrupted']
assert record['exit'] == 0 and not record['expectedDiagnostic']
assert json.loads(pathlib.Path('/tmp/dgamma-r199/ledger.jsonl').read_text().splitlines()[-1])['unit'] == unit, 'No intervening compiler invocation'
old = subprocess.run(['git','show','HEAD:'+record['path']],cwd=ROOT,capture_output=True)
def declarations(data):
    text = data.decode()
    return set(re.findall(r'^(?:[01] )?([A-Za-z_]\w*)\s*:',text,re.M) + re.findall(r'^(?:record|data)\s+([A-Za-z_]\w*)',text,re.M))
assert len(declarations((ROOT/record['path']).read_bytes())-declarations(old.stdout if old.returncode == 0 else b'')) == 1
assert not record.get('targetMutationDetected') and not record.get('unexpectedBuilding')
assert not subprocess.check_output(['git','diff','34b21c9','--','src/','dgamma.ipkg'],cwd=ROOT)
source = ROOT/record['path']
assert hashlib.sha256(source.read_bytes()).hexdigest() == record['sourceSHA256']
assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=ROOT,text=True).strip()
owned_compilers, lane2_compilers, unknown_compilers = compiler_scopes()
assert not owned_compilers and not unknown_compilers, 'Own/unknown compiler active; lane2 is not an orphan'
if lane2_compilers: print('lane-2 compiler (separate worktree)',lane2_compilers,flush=True)
subprocess.run(['git','diff','--check'],cwd=ROOT,check=True)
subprocess.run(['git','add','--',record['path']],cwd=ROOT,check=True)
subprocess.run(['git','commit','-m',message],cwd=ROOT,check=True)
assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=ROOT,text=True).strip()
receipt = dict(event='GUARDED COMMIT', unit=unit.rsplit('-',1)[0], attempt=unit.rsplit('-',1)[1], invocation=unit, sourceHash=record['sourceSHA256'], resultingCommitHash=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(), timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(), guardChecksPassed=['fresh PASS','exit 0','not interrupted','no expected diagnostic','exact source SHA256','one declaration OR exact owner-gated field/constructor delta','no intervening compiler invocation','no pre-staged files','no own-worktree compiler (lane2 excluded)','git diff --check','git commit success','no post-staged files'])
with pathlib.Path('/tmp/dgamma-r199/commit-receipts.jsonl').open('a') as ledger:
    ledger.write(json.dumps(receipt)+'\n')
print('GUARDED COMMIT',json.dumps(receipt),flush=True)
