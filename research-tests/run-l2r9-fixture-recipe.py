#!/usr/bin/env python3
"""Copied from run-l2r8-fixture-recipe.py: pure one-origin contiguity recipes.
No compiler/git/source IO. New native schedules cross an own-child Remove,
then restore the exact B core action word; this is not general move existence.
"""
ACTIONS={'I':('OInsert 5 (ChildOf 2) (smallComponent False)','OInsertTag'),
 'B':('LBegin 2','LBeginTag'),'F':('LAdvance 2','LFinishTag'),
 'T':('ORetire 5','ORetireTag'),'D':('ORemove 5','ORemoveTag'),
 'R':('OInsert 3 Root (smallComponent True)','OInsertTag'),
 'S':('OInsert 4 Root (smallComponent False)','OInsertTag')}
WORDS=['IBFTDRS','IBFTRDS','RIBFTDS']
REGISTRIES=['(registry (smallState 4))']; PATHS=[]; EDGES=[]

def update(c,reg):
 if c in 'IRS':
  actor,parent,component={'I':('5','(ChildOf 2)','False'),'R':('3','Root','True'),'S':('4','Root','False')}[c]
  return f'(insertBinding @{{%search}} {actor} (freshFiber (smallComponent {component}) {parent}) {reg} Refl)'
 if c=='D':return f'(deleteBinding @{{%search}} 5 {reg})'
 if c=='T':return f'(replaceBinding @{{%search}} 5 (retireFiber (freshFiber (smallComponent False) (ChildOf 2))) {reg})'
 life='Reloading [] id EmptyView' if c=='B' else 'Active id EmptyView'
 return f'(replaceBinding @{{%search}} 2 (setFiberLifecycle (freshFiber (smallComponent False) Root) ({life})) {reg})'
for word in WORDS:
 reg=REGISTRIES[0];path=[0]
 for c in word:
  reg=update(c,reg)
  if reg not in REGISTRIES:REGISTRIES.append(reg)
  after=REGISTRIES.index(reg);edge=(path[-1],after,c)
  if edge not in EDGES:EDGES.append(edge)
  path.append(after)
 PATHS.append(path)

def nat(n,tail='Z'):
 for _ in range(n):tail='(S '+tail+')'
 return tail

def step(schedule,index):
 word=WORDS[schedule];p=PATHS[schedule];e=(p[index],p[index+1],word[index]);j=EDGES.index(e)
 action,tag=ACTIONS[word[index]]
 return f'(Fired {{before = contiguityState {p[index]}}} {{afterState = contiguityState {p[index+1]}}} %search %search ({action}) {tag} (contiguityEdge{j} contiguityNativeExecutionL2R9))'

def trace(schedule,start,end):
 t='NoTransitions'
 for i in reversed(range(start,end)):t=f'(MoreTransitions {step(schedule,i)} {t})'
 return t

def trail(schedule,start,end):
 t=f'(AvailabilityEnd (contiguityState {PATHS[schedule][end]}))'
 for i in reversed(range(start,end)):t=f'(AvailabilityStep (contiguityState {PATHS[schedule][i]}) {step(schedule,i)} _ {t})'
 return t

def prefix_step(i):
 a,tag,field=[('LBegin 0','LBeginTag','smallBegin0'),('LAdvance 0','LFinishTag','smallFinish0'),('ORetire 1','ORetireTag','smallRetire1'),('ORemove 1','ORemoveTag','smallRemove1')][i]
 return f'(Fired {{before = smallState {i}}} {{afterState = smallState {i+1}}} %search %search ({a}) {tag} ({field} smallNativeExecution))'

def full_trace(schedule):
 t=trace(schedule,0,7)
 for i in reversed(range(4)):t=f'(MoreTransitions {prefix_step(i)} {t})'
 return t

def full_trail(schedule):
 t=trail(schedule,0,7)
 for i in reversed(range(4)):t=f'(AvailabilityStep (smallState {i}) {prefix_step(i)} _ {t})'
 return t

def extended(schedule,start,end):
 t='ExtendedLifecycleEnd';word=WORDS[schedule]
 for i in reversed(range(start,end)):
  c=word[i];st=step(schedule,i);rest=trace(schedule,i+1,end)
  if c in 'BF':t=f'(ExtendedLifecycleStep {st} {rest} Refl Refl {t})'
  elif c=='I':t=f'(ExtendedYieldedRegistrationStep {st} {rest} Refl {t})'
  elif c in 'TD':
   ctor='ExtendedChildRetireStep' if c=='T' else 'ExtendedChildRemoveStep'
   fiber='(freshFiber (smallComponent False) (ChildOf 2))'
   if c=='D':fiber=f'(retireFiber {fiber})'
   t=f'({ctor} {st} {rest} 5 {fiber} Refl Refl Refl {t})'
  else:raise ValueError('Root is NOT an extended core action')
 return t
