#!/usr/bin/env python3
"""Pure recipe adapted from run-l2r8-fixture-recipe.py via the L2R9 copy.
Uses ONLY retained original/restored per-path native packets, not the missing
split-path packet or whole17-edge producer. No compiler/git/source writes.
"""
import importlib.util,pathlib,sys
sys.dont_write_bytecode=True
ROOT=pathlib.Path('/Users/vyacheslavshebanov/Work/dgamma-lane2')
spec=importlib.util.spec_from_file_location('native',ROOT/'research-tests/run-l2r9-fixture-recipe.py')
native=importlib.util.module_from_spec(spec);spec.loader.exec_module(native)
def projection(packet,index,count):
 p=packet
 for _ in range(index):p='(snd '+p+')'
 return p if index==count-1 else '(fst '+p+')'
def step(schedule,index):
 word=native.WORDS[schedule];p=native.PATHS[schedule];edge=(p[index],p[index+1],word[index]);j=native.EDGES.index(edge)
 if j<5:proof=projection('contiguityOriginalFirst',j,5)
 elif j<7:proof=projection('contiguityOriginalLast',j-5,2)
 elif j<10:raise ValueError('B4 split-path producer stopped3/3; cannot create a native edge')
 else:proof=f'(restoredEdge{j} '+('contiguityRestoredFirst' if j<=12 else 'contiguityRestoredLast')+')'
 action,tag=native.ACTIONS[word[index]]
 return f'(Fired {{before = contiguityState {p[index]}}} {{afterState = contiguityState {p[index+1]}}} %search %search ({action}) {tag} {proof})'
native.step=step

def before_core(schedule):
 t=native.trace(schedule,0,0 if schedule==0 else 1)
 for i in reversed(range(4)):t=f'(MoreTransitions {native.prefix_step(i)} {t})'
 return t

def before_trail(schedule):
 t=native.trail(schedule,0,0 if schedule==0 else 1)
 for i in reversed(range(4)):t=f'(AvailabilityStep (smallState {i}) {native.prefix_step(i)} _ {t})'
 return t

def extended(schedule,start,end):
 t=f'(ExtendedLifecycleEnd {{name = Nat}} {{key = Bool}} {{world = Unit}} {{error = String}} {{value = \\key => Unit}} {{nameEq = %search}} {{selected = 2}} {{state = contiguityState {native.PATHS[schedule][end]}}})'
 for i in reversed(range(start,end)):
  c=native.WORDS[schedule][i];st=step(schedule,i);rest=native.trace(schedule,i+1,end)
  inst=f'{{name = Nat}} {{key = Bool}} {{world = Unit}} {{error = String}} {{value = \\key => Unit}} {{nameEq = %search}} {{selected = 2}} {{first = contiguityState {native.PATHS[schedule][i]}}} {{middle = contiguityState {native.PATHS[schedule][i+1]}}} {{finalState = contiguityState {native.PATHS[schedule][end]}}}'
  if c in 'BF':t=f'(ExtendedLifecycleStep {inst} {st} {rest} Refl Refl {t})'
  elif c=='I':t=f'(ExtendedYieldedRegistrationStep {inst} {{child = 5}} {{component = smallComponent False}} {st} {rest} Refl {t})'
  elif c in 'TD':
   ctor='ExtendedChildRetireStep' if c=='T' else 'ExtendedChildRemoveStep'
   fiber='(freshFiber (smallComponent False) (ChildOf 2))'
   if c=='D':fiber=f'(retireFiber {fiber})'
   t=f'({ctor} {inst} {st} {rest} 5 {fiber} Refl Refl Refl {t})'
  else:raise ValueError('No root action in extended core')
 return t

def core(schedule):
 a,b=(0,5) if schedule==0 else (1,6)
 return f'''(MkLocatedExtendedCore {{name = Nat}} {{key = Bool}} {{world = Unit}} {{error = String}} {{value = \\key => Unit}} {{nameEq = %search}} {{actor = 2}} {{initial = smallState 0}} {{finalState = contiguityState {native.PATHS[schedule][7]}}} {{global = {native.full_trace(schedule)}}} (contiguityState {native.PATHS[schedule][a]}) (contiguityState {native.PATHS[schedule][b]})
    {before_core(schedule)}
    {native.trace(schedule,a,b)}
    {native.trace(schedule,b,7)}
    {before_trail(schedule)}
    {native.trail(schedule,a,b)}
    {native.trail(schedule,b,7)}
    {extended(schedule,a,b)} Refl)'''

def declaration():
 return '''
||| CONCRETE native coreContiguityRestored instance: R passes from just after
||| B's extended core to just before it; SAME contiguous action word and
||| source-aware grammar on both sides, physical core position4->5, and
||| RegistryExtensional WHOLE-run endpoints. Intermediate split path and the
||| universally quantified restoration theorem remain OPEN.
public export
0 coreContiguityRestored : CoreRestorationFixture
coreContiguityRestored = MkCoreRestorationFixture
  '''+native.full_trace(0)+'\n  '+native.full_trace(2)+'\n  '+native.full_trail(0)+'\n  '+native.full_trail(2)+'\n  '+core(0)+'\n  '+core(2)+'''
  (smallSourceValid smallNativeExecution) (\\same => case same of Refl impossible)
  Refl Refl Refl Refl
  (snapshotIntoExtensional %search (contiguityState 7) (contiguityState 17) (snd contiguityEndpoints))
'''
