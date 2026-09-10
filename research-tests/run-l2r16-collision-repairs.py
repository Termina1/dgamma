#!/usr/bin/env python3
"""L2R16 bounded mechanical CP3/research qualification class, authorized by
QUALIFICATION-RULING.json. Adapted from availability-repairs coordinator.
Every module gets one target-only detached check and one guarded commit; stop
at first failed repair, unknown diagnostic, preflight rejection or requested
unit count. Never changes production types or repoints a name to CP3.
"""
from pathlib import Path
import json,re,subprocess,sys,time
ROOT=Path('/Users/vyacheslavshebanov/Work/dgamma-lane2');OUT=Path('/tmp/dgamma-l2r16')
NAMES={
 'DGamma.CP5AvailabilityAwarePlacement':['AvailabilityTrace','AvailabilityStep','AvailabilityEnd','rootCutCompatible','rootInputAtSource','rootDeclaredProvisionsFree','EarliestAvailableRootBirth','MkEarliestAvailableRootBirth','rootAvailabilityTrail','rootCurrentCutAvailable','noEarlierCompatibleRootCut'],
 'DGamma.L2R3Attached':['AttachedRelease','MkAttachedRelease','AttachedReason','KeyReleased','EarlierForcedRoot','OrderedForcedRootBundle','ForcedBundleEnd','releasedChild','releasedFiber','releaseOccurrence','releaseFound','releaseParent','sharedProvision','childDeclares','rootDeclares'],
 'DGamma.L2R3AttachedGap':['AttachedBundleOccurrence','MkAttachedBundleOccurrence','AttachedNormalForm','MkAttachedNormalForm','bundleActor','containingBlock','coreEnd','memberCore','memberExtended','memberBundle','memberForced','memberSplit','bundleOccurrence','bundleOffset','offsetExact','memberOrdinal','memberLowerBound','memberUpperBound','rootInBundle'],
 'DGamma.L2R3ForcedClosure':['ForcedRootInput','KeyForces','OrderForces','forcedRootLeast']}
# Avoid capturing local binders that share a projection's lowercase spelling.
NAMES={ns:[n for n in names if n[0].isupper() or n in ['rootCutCompatible','rootInputAtSource','rootDeclaredProvisionsFree','forcedRootLeast']] for ns,names in NAMES.items()}
assert Path.cwd()==ROOT and (OUT/'QUALIFICATION-RULING.json').exists()
def prepare(path,receipt,unit):
 p=ROOT/path;old=p.read_text();s=old;changes=[]
 assert not subprocess.check_output(['git','diff','--',path],text=True)
 for namespace,names in NAMES.items():
  if 'import '+namespace not in old and 'module '+namespace+'\n' not in old:continue
  lines=s.splitlines(keepends=True)
  for i,line in enumerate(lines):
   if line.lstrip().startswith(('|||','--')):continue
   for n in names:
    # Preserve defining names; only qualify use sites.
    if re.match(r'^\s*(?:(?:record|data)\s+)?(?:[01] )?'+n+r'\s*(?::|$)',line):continue
    if re.match(r'^\s*constructor\s+'+n+r'\s*$',line):continue
    code,sep,comment=line.partition('--')
    parts=re.split(r'("(?:\\.|[^"\\])*")',code)
    count=0
    for k in range(0,len(parts),2):
     parts[k],nsubs=re.subn(r'(?<![.\w])'+n+r'\b',namespace+'.'+n,parts[k]);count+=nsubs
    if count:changes.append(dict(name=n,qualified=namespace+'.'+n,line=i+1,occurrences=count))
    line=''.join(parts)+sep+comment
   lines[i]=line
  s=''.join(lines)
 assert s!=old and changes
 # The AST-level name-set guard in the fresh-check runner independently verifies zero new declarations.
 p.write_text(s)
 q=OUT/'RECHECK-DECISIONS.json';d=json.loads(q.read_text());assert path not in d
 r=json.loads((OUT/(receipt+'.json')).read_text());assert r['path']==path and not r['passed']
 d[path]=dict(kind='lexical',repairClass='qualification-only',repairUnit=unit,attemptCap=2,changes=changes,originalReceipt=receipt,exactErrors=r['transcript'])
 q.write_text(json.dumps(d,indent=2)+'\n')
 (OUT/(unit+'-preparation.json')).write_text(json.dumps(d[path],indent=2)+'\n')
for _ in range(int(sys.argv[1])):
 subprocess.run(['python3','-I','research-tests/run-l2r16-recheck.py','--state-only'],check=True)
 state=json.loads((ROOT/'research-tests/O6-L2R16-RECHECK-STATE.json').read_text())
 pending=[x for x in state['modules'] if x['status']=='NEEDS-CLASSIFICATION']
 if len(pending)!=1:print('STOP: no sole qualification candidate',flush=True);break
 r=pending[0];text=r['exactErrors']
 if not any(ns+'.' in text for ns in NAMES) or 'Ambiguous elaboration.' not in text or any(x in text for x in ['Mismatch between:','Unsolved holes','not total']):
  print('STOP: non-qualification diagnostic',r['path'],flush=True);break
 decisions=json.loads((OUT/'RECHECK-DECISIONS.json').read_text())
 if r['path'] in decisions:print('STOP: existing repair unit',flush=True);break
 nums=[int(d['repairUnit'][1:]) for d in decisions.values() if d.get('repairUnit')]
 unit='R'+str(max(nums,default=0)+1);prepare(r['path'],r['lastReceipt'],unit)
 attempt=unit+'-1'
 subprocess.run(['python3','-I','research-tests/run-l2r16-launch.py',attempt,r['path']],check=True)
 while not (OUT/(attempt+'.json')).exists():
  time.sleep(1)
  if 'Traceback (most recent call last)' in (OUT/(attempt+'.wrapper.log')).read_text():raise RuntimeError('wrapper rejection')
 checked=json.loads((OUT/(attempt+'.json')).read_text())
 if not checked['passed']:print('STOP: repair failed',attempt,flush=True);break
 subprocess.run(['python3','-I','research-tests/run-l2r16-commit.py',attempt,'L2R16 '+unit+': qualify research names in '+Path(r['path']).stem],check=True)
 subprocess.run(['python3','-I','research-tests/run-l2r16-recheck.py'],check=True)
