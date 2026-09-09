#!/usr/bin/env python3
"""Copied from L2R14; L2R15 D3 validation-only coordinator: committed plan, unchanged targets, one check
at a time. No proof attempts, source edits, dependency touches, shared locks,
windows or foreign compiler signals. Run detached; results remain append-only.
"""
from pathlib import Path
import datetime, hashlib, json, subprocess, time
ROOT=Path('/Users/vyacheslavshebanov/Work/dgamma-lane2')
OUT=Path('/tmp/dgamma-l2r15')
PLAN=ROOT/'research-tests/O6-L2R15-FINAL-VALIDATION-PLAN.json'
assert Path.cwd()==ROOT
plan=json.loads(PLAN.read_text())
assert subprocess.check_output(['git','show','HEAD:'+str(PLAN.relative_to(ROOT))],cwd=ROOT)==PLAN.read_bytes(), 'Plan must be committed before first final validation'
assert (OUT/'source-closed.json').is_file()
results=[]
for task in plan['validations']:
 p=ROOT/task['path'];assert hashlib.sha256(p.read_bytes()).hexdigest()==task['sourceSHA256']
 subprocess.run(['python3','-I',str(ROOT/'research-tests/run-l2r15-launch.py'),task['unit'],task['path']],cwd=ROOT,check=True)
 while not (OUT/(task['unit']+'.json')).exists():time.sleep(1)
 r=json.loads((OUT/(task['unit']+'.json')).read_text());assert r['passed'] and r['fresh'] and r['exit']==0 and not r['interrupted'] and not r['sourceMutationObserved']
 assert r['sourceSHA256']==task['sourceSHA256'] and r['buildingCount']==1
 results.append(dict(unit=task['unit'],path=task['path'],seconds=r['seconds'],maxSampleRSSKiB=r['maxSampleRSSKiB']))
 print('FINAL FRESH PASS',json.dumps(results[-1]),flush=True)
report=dict(passed=True,endUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),validations=results)
(OUT/'final-validation-result.json').write_text(json.dumps(report,indent=2)+'\n')
print('FINAL VALIDATION COMPLETE',len(results),flush=True)
