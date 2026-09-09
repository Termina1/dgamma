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
elif unit=='B7':
 name='advanceYieldAtMatch'
 text='''\n||| Consume the explicitly observed native target Bool after a successful
||| yield. False is LDivert; True delegates to the checked remaining-list step.
export
0 advanceYieldAtMatch :
'''+base+stepArgs+capArgs+yieldArgs+f'  (seen : Bool) -> (0 matchEquation : {matchNative} = seen) ->\n'+result
 text+=f'{name} {imp}\n  {args}\n  step rest accumulator view lifeEquation capability capEquation localAfter undo outcomeEquation False matchEquation =\n'
 text+=rewrites(cap=True,outcome=True,match=True)+snapshot('LDivertTag',f'(setFiberRuntime actorFiber (localTable localAfter) (Unloading {nextAcc} view Nothing))','(localWorld localAfter)')
 text+=f'''{name} {imp}
  {args}
  step rest accumulator view lifeEquation capability capEquation localAfter undo outcomeEquation True matchEquation =
  advanceYieldAtRest {args} step rest accumulator view lifeEquation capability capEquation localAfter undo outcomeEquation matchEquation
'''
elif unit=='B8':
 name='advanceEmptyAtMatch'
 text='''\n||| Empty-program native Finish/Divert observation, with the Bool explicitly
||| supplied at its own equation. No iterator outcome or late edge is assumed.
export
0 advanceEmptyAtMatch :
'''+base+f'''  (accumulator : {local} -> {local}) -> (view : View name {deps}) ->
  (0 lifeEquation : fiberLifecycle actorFiber = Reloading [] accumulator view) ->
  (seen : Bool) -> (0 matchEquation : {matchNative} = seen) ->
'''+result
 for seen,tag,life in [('False','LDivertTag','(Unloading accumulator view Nothing)'),('True','LFinishTag','(Active accumulator view)')]:
  text+=f'{name} {imp}\n  {args}\n  accumulator view lifeEquation {seen} matchEquation =\n'
  text+=rewrites(match=True)+snapshot(tag,f'(setFiberLifecycle actorFiber {life})')
elif unit=='B9':
 name='advanceAtYield'
 text='''\n||| Split ONLY the already observed yielded pair, then observe the native
||| target-match Bool at its actual call site. No inferred local view.
export
0 advanceAtYield :
'''+base+stepArgs+capArgs+f'''  (yielded : ({local}, {local} -> {local})) ->
  (0 outcomeEquation : runStepEffect step capability {oldLocal} = Right yielded) ->
'''+result
 text+=f'''{name} {imp}
  {args}
  step rest accumulator view lifeEquation capability capEquation (localAfter, undo) outcomeEquation =
  advanceYieldAtMatch {args}
    step rest accumulator view lifeEquation capability capEquation localAfter undo outcomeEquation
    ({matchNative}) Refl
'''
elif unit=='B10':
 name='advanceAtOutcome'
 text='''\n||| Eliminate the observed native iterator Either once. Failure reproduces
||| LRaise; success uses a separate yielded-pair consumer.
export
0 advanceAtOutcome :
'''+base+stepArgs+capArgs+f'''  (outcome : Either error ({local}, {local} -> {local})) ->
  (0 outcomeEquation : runStepEffect step capability {oldLocal} = outcome) ->
'''+result
 text+=f'{name} {imp}\n  {args}\n  step rest accumulator view lifeEquation capability capEquation (Left failure) outcomeEquation =\n'
 text+=rewrites(cap=True,outcome=True)+snapshot('LRaiseTag','(setFiberLifecycle actorFiber (Unloading accumulator view (Just failure)))')
 text+=f'''{name} {imp}
  {args}
  step rest accumulator view lifeEquation capability capEquation (Right yielded) outcomeEquation =
  advanceAtYield {args}
    step rest accumulator view lifeEquation capability capEquation yielded outcomeEquation
'''
elif unit=='B11':
 name='advanceAtCapability'
 text='''\n||| Observe the native committed-capability Maybe, whose retirement
||| invariance is the existing Calculus theorem. Nothing remains undefined.
export
0 advanceAtCapability :
'''+base+stepArgs+f'''  (capability : Maybe (DepValues key value {deps})) ->
  (0 capEquation : {capNative} = capability) ->
'''+result
 text+=f'{name} {imp}\n  {args}\n  step rest accumulator view lifeEquation Nothing capEquation =\n'+rewrites(cap=True)+'  Refl\n'
 text+=f'''{name} {imp}
  {args}
  step rest accumulator view lifeEquation (Just capability) capEquation =
  advanceAtOutcome {args}
    step rest accumulator view lifeEquation capability capEquation
    (runStepEffect step capability {oldLocal}) Refl
'''
elif unit=='B12':
 name='advanceAtRemaining'
 text='''\n||| Eliminate only the actual reloading program list. Library resolver and
||| target Bool are observed HERE with equations, never reconstructed views.
export
0 advanceAtRemaining :
'''+base+f'''  (remaining : List {stepType}) ->
  (accumulator : {local} -> {local}) -> (view : View name {deps}) ->
  (0 lifeEquation : fiberLifecycle actorFiber = Reloading remaining accumulator view) ->
'''+result
 text+=f'''{name} {imp}
  {args} [] accumulator view lifeEquation =
  advanceEmptyAtMatch {args} accumulator view lifeEquation
    ({matchNative}) Refl
{name} {imp}
  {args} (step :: rest) accumulator view lifeEquation =
  advanceAtCapability {args} step rest accumulator view lifeEquation
    ({capNative}) Refl
'''
elif unit=='B13':
 name='advanceAtLifecycle'
 text='''\n||| Single native lifecycle elimination. Non-reloading actions remain
||| undefined on BOTH sides; reloading is handled by the observed pipeline.
export
0 advanceAtLifecycle :
'''+base+f'''  (lifecycle : Lifecycle key value world error name {deps} {provision}) ->
  (0 lifeEquation : fiberLifecycle actorFiber = lifecycle) ->
'''+result
 for pat in ['(Inactive outcome)','(Active accumulator view)','(Unloading accumulator view outcome)']:
  text+=f'{name} {imp}\n  {args} {pat} lifeEquation =\n'+rewrites()+'  Refl\n'
 text+=f'''{name} {imp}
  {args} (Reloading remaining accumulator view) lifeEquation =
  advanceAtRemaining {args} remaining accumulator view lifeEquation
'''
elif unit=='B14':
 name='retirementAdvanceNative'
 text='''\n||| GENERAL all-tag native LAdvance observation producer from the ACTUAL
||| frame. Iter, Finish, Raise, Divert and undefined results are all covered.
||| No iterator outcome, target truth, or alternate edge is a premise.
export
0 retirementAdvanceNative :
'''+base+result
 text+=f'''{name} {imp}
  {args} =
  advanceAtLifecycle {args} (fiberLifecycle actorFiber) Refl
'''
else:
 raise SystemExit('Unknown recipe unit')
s=p.read_text()
assert name+' :' not in s, 'One declaration only, no implicit source rewrite'
p.write_text(s+text)
print(unit,name,p)
