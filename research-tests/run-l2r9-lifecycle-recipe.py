#!/usr/bin/env python3
"""D14 bounded three-role native-observation attempt; not a proof/receipt.
Generate one declaration only, with original native edge + actual frame inputs.
"""
from pathlib import Path
root = Path('/Users/vyacheslavshebanov/Work/dgamma-lane2')
p = root / 'research-tests/O6-L2R9-Sources/DGamma/L2R9LifecycleRoles.idr'
s = p.read_text()
assert 'replayRetirementLifecycle :' not in s
native = '{name} {key} {value} {world} {error}'
mapper = f'\\out => (fst out, runtimeSnapshot {native} (MkSystemState (worldState (snd out)) (replaceBinding @{{nameEq}} child (retireFiber childFiber) (registry (snd out)))))'
early = '(MkSystemState (worldState before) (replaceBinding @{nameEq} child (retireFiber childFiber) (registry before)))'
expected = f'(runtimeSnapshot {native} (MkSystemState (worldState afterState) (replaceBinding @{{nameEq}} child (retireFiber childFiber) (registry afterState))))'
text = '''
||| Attempt: use the actual replay evaluator observation, the proved native
||| resolver frame, native foreign lookup, and the ORIGINAL checked edge.
||| The remaining first equation is native evaluator/update commutation; it
||| is NOT supplied as a premise. Failed attempts are reverted completely.
export
0 replayRetirementLifecycle :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child, parent, actor : name) ->
  (childFiber, actorFiber : Fiber name key value world error) ->
  (before : SystemState name key value world error) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  NativeLifecycleRetirementRole nameEq keyEq child parent actor childFiber actorFiber before action tag
'''
for action, tag, role in [('LBegin actor', 'LBeginTag', 'Here'), ('LAdvance actor', 'LIterTag', '(There Here)'), ('LAdvance actor', 'LFinishTag', '(There (There Here))')]:
    raw = f'(applyAction @{{nameEq}} @{{keyEq}} ({action}) {early})'
    orig = f'(applyAction @{{nameEq}} @{{keyEq}} ({action}) before)'
    text += f'''replayRetirementLifecycle {{name}} {{key}} {{world}} {{error}} {{value}} nameEq keyEq child parent actor childFiber actorFiber before _ _
  {role} frame distinct valid afterState original =
  checkedSnapshotObserved nameEq keyEq ({action}) {early} {tag}
    {expected}
    {raw} Refl
    (trans
      (the (observeActionResult {raw} = map ({mapper}) {orig})
        (rewrite lookupReplaceOther {{key = name}} {{value = FiberAt name key value world error}} @{{nameEq}}
          actor child (\\same => distinct (sym same)) (retireFiber childFiber) (registry before) in
         rewrite frameActorFound frame in
         rewrite sym (fst (retirementFrameResolverSame nameEq keyEq child parent actor childFiber actorFiber (registry before) frame)) in Refl))
      (cong (map ({mapper}))
        (checkedActionProjects nameEq keyEq ({action}) before afterState {tag} original)))
    (checkedActionTargetValid nameEq keyEq (ORetire child) before {early} ORetireTag
      (childRetireAtFound nameEq keyEq child childFiber before (frameChildFound frame) valid))
'''
text += '''replayRetirementLifecycle nameEq keyEq child parent actor childFiber actorFiber before action tag
  (There (There (There impossibleRole))) frame distinct valid afterState original = absurd impossibleRole
'''
p.write_text(s + text)
