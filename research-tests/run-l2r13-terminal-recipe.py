#!/usr/bin/env python3
"""L2R13 B10 one-declaration source recipe, lane-owned absolute path only.
Does not launch a compiler or commit. No predecessor source edits.
"""
from pathlib import Path
ROOT=Path('/Users/vyacheslavshebanov/Work/dgamma-lane2')
p=ROOT/'research-tests/O6-L2R13-Sources/DGamma/L2R13TerminalMove.idr'
assert Path.cwd()==ROOT
root='(OInsert root Root component)'
old=f'(nativePairTrail nameEq keyEq source oldMiddle oldFinal action {root} crossTag OInsertTag oldChecked oldRoot)'
new=f'(nativePairTrail nameEq keyEq source (squareMiddle square) (squareFinal square) {root} action OInsertTag crossTag (earlyChecked square) (laterChecked square))'
ot=f'(appendAvailability prefixTrail {old})';nt=f'(appendAvailability prefixTrail {new})'
os='(Fired {before = source} {afterState = oldMiddle} nameEq keyEq action crossTag oldChecked)'
orr=f'(Fired {{before = oldMiddle}} {{afterState = oldFinal}} nameEq keyEq {root} OInsertTag oldRoot)'
nr=f'(Fired {{before = source}} {{afterState = squareMiddle square}} nameEq keyEq {root} OInsertTag (earlyChecked square))'
ns='(Fired {before = squareMiddle square} {afterState = squareFinal square} nameEq keyEq action crossTag (laterChecked square))'
s=f'''
||| GENUINE local terminal-square move producer. Both whole native traces,
||| physical occurrences/adjacency, action words, current cuts, endpoint and
||| exact decrement are DERIVED from the square and native scan frames.
||| This local theorem has NO suffix. It is not GeneralAdmittedMoveExistence:
||| phase/NeverRetired/uniqueness and global frame existence remain its domain
||| obligations; none is silently dropped from that unchanged global type.
export
0 terminalSquareAdmittedMove : {{name, key, world, error : Type}} -> {{value : key -> Type}} ->
  {{initial : SystemState name key value world error}} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (root : name) ->
  (component : Component key value world error) ->
  (source, oldMiddle, oldFinal : SystemState name key value world error) ->
  (action : Action name key value world error) -> (crossTag : RuleTag) ->
  (before : Transitions initial source) ->
  (prefixTrail : AvailabilityTrace name key world error value before) ->
  (0 oldChecked : checkedApplyAction @{{nameEq}} @{{keyEq}} action source = Just (crossTag, oldMiddle)) ->
  (0 oldRoot : checkedApplyAction @{{nameEq}} @{{keyEq}} {root} oldMiddle = Just (OInsertTag, oldFinal)) ->
  (square : ClassifierSquare name key world error value nameEq keyEq root component source action crossTag oldFinal) ->
  (0 forced : ForcedOnTrace nameEq keyEq {ot} (S (length (nativeActionWord prefixTrail)))) ->
  (target, untouched : Nat) -> (0 bounded : LTE target (length (nativeActionWord prefixTrail))) ->
  (0 oldFrame : totalDistance nameEq keyEq {ot} = minus (S (length (nativeActionWord prefixTrail))) target + untouched) ->
  (0 newFrame : totalDistance nameEq keyEq {nt} = minus (length (nativeActionWord prefixTrail)) target + untouched) ->
  AdmittedDistanceMove name key world error value nameEq keyEq {ot} {nt}
terminalSquareAdmittedMove nameEq keyEq root component source oldMiddle oldFinal action crossTag
  before prefixTrail oldChecked oldRoot square forced target untouched bounded oldFrame newFrame =
  MkAdmittedDistanceMove root component (nativeActionWord prefixTrail) action []
    (MkLocatedActionOccurrence source oldMiddle before {os} (MoreTransitions {orr} NoTransitions) Refl Refl)
    (MkLocatedActionOccurrence source (squareMiddle square) before {nr} (MoreTransitions {ns} NoTransitions) Refl Refl)
    (sym (nativeWordCount prefixTrail)) (sym (nativeWordCount prefixTrail)) (squareAdmitted square)
    forced (nativeWordAppend prefixTrail {old}) (nativeWordAppend prefixTrail {new})
    (checkedRootCurrentAvailable nameEq keyEq root component oldMiddle oldFinal OInsertTag oldRoot)
    (squareCurrentCut square)
    (totalDistance nameEq keyEq {ot}) (totalDistance nameEq keyEq {nt}) Refl Refl
    (totalDistanceOneLeftFromFrame nameEq keyEq {ot} {nt}
      (length (nativeActionWord prefixTrail)) target untouched bounded oldFrame newFrame)
    (squareEndpoint square)
'''
assert '0 terminalSquareAdmittedMove :' not in p.read_text()
p.write_text(p.read_text()+s)
