#!/usr/bin/env python3
"""L2R16 bounded sequential qualification-only repairs of unambiguous research
availability references. Stops for any other diagnostic or after its requested
number of units. Uses detached check/guarded-commit runners; no proof rewriting.
"""
from pathlib import Path
import json,subprocess,sys,time
ROOT=Path('/Users/vyacheslavshebanov/Work/dgamma-lane2');OUT=Path('/tmp/dgamma-l2r16')
assert Path.cwd()==ROOT
for _ in range(int(sys.argv[1])):
 subprocess.run(['python3','-I','research-tests/run-l2r16-recheck.py','--state-only'],check=True)
 state=json.loads((ROOT/'research-tests/O6-L2R16-RECHECK-STATE.json').read_text())
 pending=[x for x in state['modules'] if x['status']=='NEEDS-CLASSIFICATION']
 if len(pending)!=1:print('STOP: no sole qualification candidate',flush=True);break
 r=pending[0];text=r['exactErrors']
 if 'DGamma.CP5AvailabilityAwarePlacement.' not in text or 'Ambiguous elaboration.' not in text or 'Mismatch between:' in text or 'Unsolved holes' in text:
  print('STOP: non-availability diagnostic',r['path'],flush=True);break
 decisions=json.loads((OUT/'RECHECK-DECISIONS.json').read_text())
 if r['path'] in decisions:print('STOP: existing repair unit',flush=True);break
 nums=[int(d['repairUnit'][1:]) for d in decisions.values() if d.get('repairUnit')]
 unit='R'+str(max(nums,default=0)+1)
 assert (OUT/'QUALIFICATION-RULING.json').exists()
 args=['python3','-I','research-tests/run-l2r16-qualify.py',unit,r['path'],r['lastReceipt'],'DGamma.CP5AvailabilityAwarePlacement','AvailabilityTrace','AvailabilityStep','AvailabilityEnd','rootCutCompatible','rootInputAtSource','rootDeclaredProvisionsFree','EarliestAvailableRootBirth','MkEarliestAvailableRootBirth']
 with (OUT/(unit+'-preparation.log')).open('w') as log:subprocess.run(args,stdout=log,stderr=subprocess.STDOUT,check=True)
 attempt=unit+'-1'
 subprocess.run(['python3','-I','research-tests/run-l2r16-launch.py',attempt,r['path']],check=True)
 while not (OUT/(attempt+'.json')).exists():
  time.sleep(1)
  if 'Traceback (most recent call last)' in (OUT/(attempt+'.wrapper.log')).read_text():raise RuntimeError('wrapper rejection')
 checked=json.loads((OUT/(attempt+'.json')).read_text())
 if not checked['passed']:print('STOP: repair failed',attempt,flush=True);break
 subprocess.run(['python3','-I','research-tests/run-l2r16-commit.py',attempt,'L2R16 '+unit+': qualify research availability references in '+Path(r['path']).stem],check=True)
 subprocess.run(['python3','-I','research-tests/run-l2r16-recheck.py'],check=True)
