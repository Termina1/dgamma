#!/usr/bin/env python3
"""L2R16 closure coordinator, adapted from run-l2r15-final-validation.py.
Validation only; one detached monitored check at a time. A failed target stops
this coordinator for an explicit lexical/semantic classification. Known R205
untrusted TTCs cannot certify imports. Source contents never changed here.
RSS = maximum sampled RSS over command-matching idris2 processes.
"""
from pathlib import Path
import datetime, hashlib, json, re, subprocess, time, functools
ROOT=Path('/Users/vyacheslavshebanov/Work/dgamma-lane2')
OUT=Path('/tmp/dgamma-l2r16')
STATE=ROOT/'research-tests/O6-L2R16-RECHECK-STATE.json'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def readrecords():return [json.loads(s) for s in (OUT/'ledger.jsonl').read_text().splitlines()] if (OUT/'ledger.jsonl').exists() else []
assert Path.cwd()==ROOT
mods=json.loads((OUT/'IMPORT-GRAPH.json').read_text())
targets=(OUT/'TARGETS.txt').read_text().splitlines()
roots={m for m,r in mods.items() if r['path'] in targets}
old=json.loads((ROOT/'research-tests/O6-R205-REBUILD-STATE.json').read_text())
mstate={x['module']:x for x in old['modules']}
longs=set(json.loads((OUT/'HEAVY-TARGETS.json').read_text())['longFixturesLast'])
@functools.lru_cache(None)
def external_blockers(m):
 if m not in mods:return ()
 if m not in roots and m in mstate and not mstate[m]['usableAsImport']:
  if mstate[m]['status'].startswith('unchecked'):
   return tuple(sorted(set(b for d in mods[m]['imports'] for b in external_blockers(d)))) or (m,)
  return (m,)
 if m not in roots and not (ROOT/('build/ttc/2025081600/'+m.replace('.','/')+'.ttc')).is_file():return (m,)
 return tuple(sorted(set(b for d in mods[m]['imports'] for b in external_blockers(d))))
@functools.lru_cache(None)
def own_deps(m):
 return tuple(sorted(set(d for d in mods[m]['imports'] if d in roots)|set(b for d in mods[m]['imports'] if d in mods for b in own_deps(d))))
# Direct graph closure retains blockers through non-lane intermediary modules.
rows=[];done=set()
while len(done)<len(roots):
 candidates=[m for m in roots-done if set(own_deps(m))<=done]
 assert candidates, 'Cycle in lane closure'
 m=min(candidates,key=lambda m:(m.split('.')[-1] in longs, len(own_deps(m)), m))
 done.add(m);b=external_blockers(m)
 rows.append(dict(module=m,path=mods[m]['path'],sourceSHA256=sha(ROOT/mods[m]['path']),ownDependencies=list(own_deps(m)),externalBlockers=list(b),status='BLOCKED-ON-R206' if b else 'UNCHECKED',invocations=[],exactErrors=[dict(module=x,status=mstate.get(x,{}).get('status','missing seeded TTC'),error=mstate.get(x,{}).get('exactErrors'),reason=mstate.get(x,{}).get('reason')) for x in b]))
plan=dict(timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),total=len(rows),repairCap=40,attemptsPerRepair=3,capAuthority='CAP-RULING.txt + PREREQUISITE-RULING.txt',targets=rows)
if not (OUT/'RECHECK-PLAN.json').exists():(OUT/'RECHECK-PLAN.json').write_text(json.dumps(plan,indent=2)+'\n')
elif json.loads((OUT/'RECHECK-PLAN.json').read_text())['total']!=len(rows):
 assert (OUT/'V19-MERGE-AUTHORITY.json').exists()
 if not (OUT/'RECHECK-PLAN-V19.json').exists():(OUT/'RECHECK-PLAN-V19.json').write_text(json.dumps(plan,indent=2)+'\n')
# Explicit classifications are separate from compiler success and from TYPE inhabitance.
def refresh():
 records=readrecords();decisions=json.loads((OUT/'RECHECK-DECISIONS.json').read_text()) if (OUT/'RECHECK-DECISIONS.json').exists() else {}
 current=[];byname={}
 for original in rows:
  r=dict(original);r['sourceSHA256']=sha(ROOT/r['path']);recs=[x for x in records if x['path']==r['path']]
  r['invocations']=[x['unit'] for x in recs]
  applicable=[x for x in recs if x['sourceSHA256']==r['sourceSHA256']]
  if applicable and applicable[-1]['passed']:
   last=applicable[-1];r.update(status='REPAIRED' if r['path'] in decisions and decisions[r['path']]['kind'] in ['lexical','authorized-semantic'] else 'PASSED',lastReceipt=last['unit'],freshOwnBuilding=last['fresh'])
  elif r['path'] in decisions and decisions[r['path']]['kind'] in ['semantic','repair-exhausted']:
   r.update(status='BROKEN-BY-UNFREEZE',decision=decisions[r['path']],exactErrors=decisions[r['path']]['exactErrors'])
  elif applicable and not applicable[-1]['passed']:
   r.update(status='NEEDS-CLASSIFICATION',lastReceipt=applicable[-1]['unit'],exactErrors=applicable[-1]['transcript'])
  elif not r['externalBlockers']:
   bad=[d for d in r['ownDependencies'] if byname[d]['status'] not in ['PASSED','REPAIRED']]
   if bad:r.update(status='BLOCKED-DEPENDENCY',blockedOwn=bad)
  byname[r['module']]=r;current.append(r)
 counts={s:sum(r['status']==s for r in current) for s in sorted({r['status'] for r in current})}
 report=dict(timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),total=len(current),counts=counts,checked=sum(bool(r['invocations']) for r in current),passed=counts.get('PASSED',0),repaired=counts.get('REPAIRED',0),broken=counts.get('BROKEN-BY-UNFREEZE',0),blocked=sum(n for s,n in counts.items() if s.startswith('BLOCKED')),fullyGreen=all(r['status'] in ['PASSED','REPAIRED'] for r in current),modules=current)
 STATE.write_text(json.dumps(report,indent=2)+'\n');return report
if __import__('sys').argv[-1:] == ['--state-only']:
 print(json.dumps(refresh()['counts']));raise SystemExit(0)
for original in rows:
 state=refresh();r=next(x for x in state['modules'] if x['module']==original['module'])
 if r['status'] in ['PASSED','REPAIRED','BROKEN-BY-UNFREEZE','BLOCKED-ON-R206','BLOCKED-DEPENDENCY']:continue
 if r['status']=='NEEDS-CLASSIFICATION':
  print('STOP: needs lexical/semantic decision',r['path'],r['lastReceipt'],flush=True);break
 if r['module'].split('.')[-1] in longs and '--include-long' not in __import__('sys').argv:
  print('LONG TARGET DEFERRED UNTIL LIGHT/T2 BOUNDARY',r['path'],flush=True);break
 cutoff=json.loads((OUT/'shift.json').read_text())['validationCutoff']
 if datetime.datetime.now(datetime.timezone.utc).isoformat()>=cutoff:print('VALIDATION CUTOFF',flush=True);break
 nums=[int(x.name.split('.')[0][1:]) for x in OUT.glob('V*.wrapper.log') if re.fullmatch(r'V\d+\.wrapper\.log',x.name)]
 unit='V'+str(max(nums,default=0)+1)
 subprocess.run(['python3','-I',str(ROOT/'research-tests/run-l2r16-launch.py'),unit,r['path']],cwd=ROOT,check=True)
 while not (OUT/(unit+'.json')).exists():
  time.sleep(1)
  wrapper=(OUT/(unit+'.wrapper.log')).read_text()
  if 'Traceback (most recent call last)' in wrapper:raise RuntimeError(wrapper)
 result=json.loads((OUT/(unit+'.json')).read_text());refresh()
 print('RECHECK',unit,r['path'],result['passed'],result['seconds'],flush=True)
 if not result['passed']:break
print('STATE',json.dumps(refresh()['counts']),flush=True)
