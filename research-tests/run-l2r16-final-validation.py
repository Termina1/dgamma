#!/usr/bin/env python3
"""L2R16 final dependency-ordered target checks, adapted from L2R15.
Requires a committed source boundary/plan. Rechecks every new module and any
remaining changed-source dependent invalidation; never runs a package/cold build.
Deferred/external inherited obligations stay explicit, not silently accepted.
"""
from pathlib import Path
import datetime,hashlib,json,re,subprocess,time
ROOT=Path('/Users/vyacheslavshebanov/Work/dgamma-lane2');OUT=Path('/tmp/dgamma-l2r16')
assert Path.cwd()==ROOT
plan=json.loads((ROOT/'research-tests/O6-L2R16-FINAL-VALIDATION-PLAN.json').read_text())
assert (OUT/'source-closed.json').exists()
checks=[]
for target in plan['targets']:
 path=target['path'];assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==target['sourceSHA256']
 cutoff=json.loads((OUT/'FINISH-TIMING-PLAN.json').read_text())['allChecksStopUTC']
 if datetime.datetime.now(datetime.timezone.utc).isoformat()>=cutoff:
  checks.append(dict(path=path,passed=False,status='UNCHECKED at cutoff'));break
 nums=[int(p.name.split('.')[0][1:]) for p in OUT.glob('V*.wrapper.log') if re.fullmatch(r'V\d+\.wrapper\.log',p.name)]
 unit='V'+str(max(nums,default=0)+1)
 subprocess.run(['python3','-I',str(ROOT/'research-tests/run-l2r16-launch.py'),unit,path],check=True,cwd=ROOT)
 while not (OUT/(unit+'.json')).exists():
  time.sleep(.5)
  if 'Traceback (most recent call last)' in (OUT/(unit+'.wrapper.log')).read_text():raise RuntimeError((OUT/(unit+'.wrapper.log')).read_text())
 r=json.loads((OUT/(unit+'.json')).read_text())
 checks.append(dict(path=path,invocation=unit,passed=r['passed'],sourceSHA256=r['sourceSHA256'],seconds=r['seconds']))
 print(json.dumps(checks[-1]),flush=True)
 if not r['passed']:break
result=dict(passed=len(checks)==len(plan['targets']) and all(c['passed'] for c in checks),validations=checks,expected=len(plan['targets']),inheritedClosurePolicy=plan['inheritedClosurePolicy'],completedUTC=datetime.datetime.now(datetime.timezone.utc).isoformat())
(OUT/'final-validation-result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2),flush=True)
raise SystemExit(0 if result['passed'] else 1)
