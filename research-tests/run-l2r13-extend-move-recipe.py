#!/usr/bin/env python3
"""L2R13 B13-1 first-attempt one-declaration extension recipe; no compiler or git operations.
Only creates the absolute lane-owned new source; no legacy source changes.
"""
from pathlib import Path
ROOT=Path('/Users/vyacheslavshebanov/Work/dgamma-lane2')
assert Path.cwd()==ROOT
p=ROOT/'research-tests/O6-L2R13-Sources/DGamma/L2R13ExtendMove.idr'
h=(ROOT/'research-tests/O6-L2R13-Sources/DGamma/L2R13TerminalMove.idr').read_text().split('||| Executable two-edge')[0].replace('module DGamma.L2R13TerminalMove','module DGamma.L2R13ExtendMove').replace('import DGamma.L2R8NativeWords','import DGamma.L2R8RegionEmbedding\nimport DGamma.L2R8NativeWords')
a='(OInsert following Root component)'
os=f'(Fired {{before = oldFinal}} {{afterState = oldSuccessor}} nameEq keyEq {a} OInsertTag oldRoot)'
ns=f'(Fired {{before = newFinal}} {{afterState = newSuccessor}} nameEq keyEq {a} OInsertTag newRoot)'
ot=f'(AvailabilityStep oldFinal {os} NoTransitions (AvailabilityEnd oldSuccessor))'
nt=f'(AvailabilityStep newFinal {ns} NoTransitions (AvailabilityEnd newSuccessor))'
ox=f'(appendAvailability oldTrail {ot})';nx=f'(appendAvailability newTrail {nt})'
packet=f'''(checkedRootAcrossExtensional nameEq keyEq following component oldFinal oldSuccessor newFinal OInsertTag
        oldRoot (moveEndpoints move) valid
        (provisionsDisjointFrom {{name}} {{key}} {{world}} {{error}} {{value}} @{{keyEq}}
          (componentProvisions component) (bindings (registry oldFinal))) Refl frame)'''
s=f'''
||| Extend a produced move by the same following root, deriving its WHOLE
||| endpoint from native extensional root transport. The given new-root edge
||| selects an already checked desired endpoint; B7 independently PRODUCES a
||| successful successor and determinism identifies it. No endpoint relation
||| is supplied. Forcing and the new global distance frames remain explicit.
||| This is not arbitrary suffix replay or a phase-preserving move oracle.
export
0 extendAdmittedMoveByRoot : {{name, key, world, error : Type}} -> {{value : key -> Type}} ->
  {{initial, oldFinal, newFinal : SystemState name key value world error}} ->
  {{oldTrace : Transitions initial oldFinal}} -> {{newTrace : Transitions initial newFinal}} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (oldTrail : AvailabilityTrace name key world error value oldTrace) ->
  (newTrail : AvailabilityTrace name key world error value newTrace) ->
  (move : AdmittedDistanceMove name key world error value nameEq keyEq oldTrail newTrail) ->
  (following : name) -> (component : Component key value world error) ->
  (oldSuccessor, newSuccessor : SystemState name key value world error) ->
  (0 oldRoot : checkedApplyAction @{{nameEq}} @{{keyEq}} {a} oldFinal = Just (OInsertTag, oldSuccessor)) ->
  (0 newRoot : checkedApplyAction @{{nameEq}} @{{keyEq}} {a} newFinal = Just (OInsertTag, newSuccessor)) ->
  (0 valid : registryWellFormed @{{nameEq}} @{{keyEq}} newFinal = True) ->
  (0 frame : provisionsDisjointFrom {{name}} {{key}} {{world}} {{error}} {{value}} @{{keyEq}}
    (componentProvisions component) (bindings (registry newFinal)) =
    provisionsDisjointFrom {{name}} {{key}} {{world}} {{error}} {{value}} @{{keyEq}}
      (componentProvisions component) (bindings (registry oldFinal))) ->
  (0 forced : ForcedOnTrace nameEq keyEq {ox} (S (length (prefixWord move)))) ->
  (target, untouched : Nat) -> (0 bounded : LTE target (length (prefixWord move))) ->
  (0 oldFrame : totalDistance nameEq keyEq {ox} = minus (S (length (prefixWord move))) target + untouched) ->
  (0 newFrame : totalDistance nameEq keyEq {nx} = minus (length (prefixWord move)) target + untouched) ->
  AdmittedDistanceMove name key world error value nameEq keyEq {ox} {nx}
extendAdmittedMoveByRoot {{name}} {{key}} {{world}} {{error}} {{value}} {{oldFinal}} {{newFinal}} {{oldTrace}} {{newTrace}}
  nameEq keyEq oldTrail newTrail move following component oldSuccessor newSuccessor oldRoot newRoot valid frame
  forced target untouched bounded oldFrame newFrame =
  MkAdmittedDistanceMove (movedRoot move) (movedComponent move) (prefixWord move) (crossedAction move)
    (suffixWord move ++ [{a}])
    (extendOccurrence oldTrace (MoreTransitions {os} NoTransitions) (crossedOccurrence move))
    (extendOccurrence newTrace (MoreTransitions {ns} NoTransitions) (movedBirthOccurrence move))
    (crossedOrdinalExact move) (movedBirthOrdinalExact move) (crossingAdmitted move) forced
    (trans (nativeWordAppend oldTrail {ot})
      (trans (cong (\\word => word ++ [{a}]) (oldWordExact move))
        (sym (appendAssociative (prefixWord move)
          (crossedAction move :: OInsert (movedRoot move) Root (movedComponent move) :: suffixWord move) [{a}]))))
    (trans (nativeWordAppend newTrail {nt})
      (trans (cong (\\word => word ++ [{a}]) (newWordExact move))
        (sym (appendAssociative (prefixWord move)
          (OInsert (movedRoot move) Root (movedComponent move) :: crossedAction move :: suffixWord move) [{a}]))))
    (oldCurrentCut move) (newCurrentCut move)
    (totalDistance nameEq keyEq {ox}) (totalDistance nameEq keyEq {nx}) Refl Refl
    (totalDistanceOneLeftFromFrame nameEq keyEq {ox} {nx}
      (length (prefixWord move)) target untouched bounded oldFrame newFrame)
    (replace {{p = \\next => RegistryExtensional name key world error value nameEq oldSuccessor next}}
      (cong snd (justInjective (trans (sym (extensionalChecked {packet})) newRoot)))
      (extensionalAfterSame {packet}))
'''
assert not p.exists()
p.write_text(h+s)
