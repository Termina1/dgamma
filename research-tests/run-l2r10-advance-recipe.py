#!/usr/bin/env python3
"""L2R10 all-tag LAdvance observed-helper recipe, derived from L2R9 lifecycle recipe.
Generates ONE new declaration per requested unit, never checks or commits it.
Native source/retirement observations only; no assumed alternate edge equation.
Absolute lane2 paths; no retained predecessor edits or main-tree access.
"""
from pathlib import Path
import sys
ROOT = Path('/Users/vyacheslavshebanov/Work/dgamma-lane2')
p = ROOT / 'research-tests/O6-L2R10-Sources/DGamma/L2R10AdvanceReplay.idr'
unit = sys.argv[1]
native = '{name} {key} {value} {world} {error}'
component = '(fiberComponent actorFiber)'
provision = f'(componentProvisions {component})'
deps = f'(dependencies (componentDependencies {component}))'
local = f'(LocalState key value world {provision})'
stepType = f'(StepEffect key value world error {deps} {provision})'
oldLocal = f'(MkLocalState ambient (restrictOwnedPreservingOrder {provision} (ownedValues (fiberTable actorFiber))))'
capNative = f'resolveCommittedValues {native} @{{nameEq}} @{{keyEq}} {deps} view source'
matchNative = f'targetMatches @{{nameEq}} (targetFiber {native} @{{nameEq}} @{{keyEq}} actorFiber source) view'
base = '''  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child, parent, actor : name) ->
  (childFiber, actorFiber : Fiber name key value world error) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (frame : RetirementProviderFrame name key world error value nameEq keyEq child parent actor childFiber actorFiber source) ->
  (0 distinct : Not (child = actor)) ->
'''
args = 'nameEq keyEq child parent actor childFiber actorFiber ambient source frame distinct'
imp = '{name} {key} {world} {error} {value}'
result = '  RetirementAdvanceEquation nameEq keyEq child actor childFiber ambient source\n'
stepArgs = f'''  (step : {stepType}) -> (rest : List {stepType}) ->
  (accumulator : {local} -> {local}) -> (view : View name {deps}) ->
  (0 lifeEquation : fiberLifecycle actorFiber = Reloading (step :: rest) accumulator view) ->
'''
capArgs = f'''  (capability : DepValues key value {deps}) ->
  (0 capEquation : {capNative} = Just capability) ->
'''
yieldArgs = f'''  (localAfter : {local}) -> (undo : {local} -> {local}) ->
  (0 outcomeEquation : runStepEffect step capability {oldLocal} = Right (localAfter, undo)) ->
'''
def rewrites(cap=False, outcome=False, match=False):
 s=f'''  rewrite lookupReplaceOther {{key = name}} {{value = FiberAt name key value world error}} @{{nameEq}}
    actor child (\\same => distinct (sym same)) (retireFiber childFiber) source in
  rewrite frameActorFound frame in
  rewrite lifeEquation in
'''
 if cap:
  s+=f'''  rewrite resolveCommittedValuesRetireRegistry {native} nameEq keyEq {deps} view
    child childFiber source (frameChildFound frame) in
  rewrite capEquation in
'''
 if outcome:s+='  rewrite outcomeEquation in\n'
 if match:
  s+='''  rewrite retirementTargetSame nameEq keyEq child parent actor childFiber actorFiber source frame in
  rewrite matchEquation in
'''
 return s

def snapshot(tag, nextFiber, ambient='ambient'):
 return f'''  cong (\\snapshot => Just ({tag}, snapshot))
    (retirementUpdateSnapshot nameEq child actor childFiber
      {nextFiber} {ambient} source distinct)
'''
nextAcc=f'(pushLocalUndo @{{keyEq}} {provision} accumulator undo)'
text=''
if unit=='B6':
 name='advanceYieldAtRest'
 text='''\n||| Successful original iterator outcome and True target observation. Only
||| the remaining-list constructor is eliminated; updates commute natively.
export
0 advanceYieldAtRest :
'''+base+stepArgs+capArgs+yieldArgs+f'  (0 matchEquation : {matchNative} = True) ->\n'+result
 for pat,tag,life in [('[]','LFinishTag',f'(Active {nextAcc} view)'),('(next :: later)','LIterTag',f'(Reloading (next :: later) {nextAcc} view)')]:
  text+=f'{name} {imp}\n  {args}\n  step {pat} accumulator view lifeEquation capability capEquation localAfter undo outcomeEquation matchEquation =\n'
  text+=rewrites(cap=True,outcome=True,match=True)+snapshot(tag,f'(setFiberRuntime actorFiber (localTable localAfter) {life})','(localWorld localAfter)')
else:
 raise SystemExit('Unknown recipe unit')
s=p.read_text()
assert name+' :' not in s, 'One declaration only, no implicit source rewrite'
p.write_text(s+text)
print(unit,name,p)
