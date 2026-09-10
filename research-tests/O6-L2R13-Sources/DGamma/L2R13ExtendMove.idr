module DGamma.L2R13ExtendMove

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
import DGamma.CP4DeletionSelectedForeignOrchestration
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.CP5L2R1ChildRelocation
import DGamma.L2R5CurrentCut
import DGamma.L2R6ForcedScan
import DGamma.L2R6Anchors
import DGamma.L2R6Iteration
import DGamma.L2R8RegionEmbedding
import DGamma.L2R8NativeWords
import DGamma.L2R12DistanceFrame
import Data.Nat
import DGamma.L2R11ClassifierSquare
import DGamma.L2R13InsertExtensional
import DGamma.L2R2CheckedSnapshot
import DGamma.L2R4InsertReplay
import DGamma.L2R5Extensional
import DGamma.L2R5ExtensionalRetire
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off


||| Extend a produced move by the same following root, deriving its WHOLE
||| endpoint from native extensional root transport. The given new-root edge
||| selects an already checked desired endpoint; B7 independently PRODUCES a
||| successful successor and determinism identifies it. No endpoint relation
||| is supplied. Forcing and the new global distance frames remain explicit.
||| This is not arbitrary suffix replay or a phase-preserving move oracle.
export
0 extendAdmittedMoveByRoot : {name, key, world, error : Type} -> {value : key -> Type} ->
  {initial, oldFinal, newFinal : SystemState name key value world error} ->
  {oldTrace : Transitions initial oldFinal} -> {newTrace : Transitions initial newFinal} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (oldTrail : DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace name key world error value oldTrace) ->
  (newTrail : DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace name key world error value newTrace) ->
  (move : AdmittedDistanceMove name key world error value nameEq keyEq oldTrail newTrail) ->
  (following : name) -> (component : Component key value world error) ->
  (oldSuccessor, newSuccessor : SystemState name key value world error) ->
  (0 oldRoot : checkedApplyAction @{nameEq} @{keyEq} (OInsert following Root component) oldFinal = Just (OInsertTag, oldSuccessor)) ->
  (0 newRoot : checkedApplyAction @{nameEq} @{keyEq} (OInsert following Root component) newFinal = Just (OInsertTag, newSuccessor)) ->
  (0 valid : registryWellFormed @{nameEq} @{keyEq} newFinal = True) ->
  (0 frame : provisionsDisjointFrom {name} {key} {world} {error} {value} @{keyEq}
    (componentProvisions component) (bindings (registry newFinal)) =
    provisionsDisjointFrom {name} {key} {world} {error} {value} @{keyEq}
      (componentProvisions component) (bindings (registry oldFinal))) ->
  (0 forced : ForcedOnTrace nameEq keyEq (appendAvailability oldTrail (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep oldFinal (Fired {before = oldFinal} {afterState = oldSuccessor} nameEq keyEq (OInsert following Root component) OInsertTag oldRoot) NoTransitions (DGamma.CP5AvailabilityAwarePlacement.AvailabilityEnd oldSuccessor))) (S (length (prefixWord move)))) ->
  (target, untouched : Nat) -> (0 bounded : LTE target (length (prefixWord move))) ->
  (0 oldFrame : totalDistance nameEq keyEq (appendAvailability oldTrail (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep oldFinal (Fired {before = oldFinal} {afterState = oldSuccessor} nameEq keyEq (OInsert following Root component) OInsertTag oldRoot) NoTransitions (DGamma.CP5AvailabilityAwarePlacement.AvailabilityEnd oldSuccessor))) = minus (S (length (prefixWord move))) target + untouched) ->
  (0 newFrame : totalDistance nameEq keyEq (appendAvailability newTrail (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep newFinal (Fired {before = newFinal} {afterState = newSuccessor} nameEq keyEq (OInsert following Root component) OInsertTag newRoot) NoTransitions (DGamma.CP5AvailabilityAwarePlacement.AvailabilityEnd newSuccessor))) = minus (length (prefixWord move)) target + untouched) ->
  AdmittedDistanceMove name key world error value nameEq keyEq (appendAvailability oldTrail (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep oldFinal (Fired {before = oldFinal} {afterState = oldSuccessor} nameEq keyEq (OInsert following Root component) OInsertTag oldRoot) NoTransitions (DGamma.CP5AvailabilityAwarePlacement.AvailabilityEnd oldSuccessor))) (appendAvailability newTrail (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep newFinal (Fired {before = newFinal} {afterState = newSuccessor} nameEq keyEq (OInsert following Root component) OInsertTag newRoot) NoTransitions (DGamma.CP5AvailabilityAwarePlacement.AvailabilityEnd newSuccessor)))
extendAdmittedMoveByRoot {name} {key} {world} {error} {value} {oldFinal} {newFinal} {oldTrace} {newTrace}
  nameEq keyEq oldTrail newTrail move following component oldSuccessor newSuccessor oldRoot newRoot valid frame
  forced target untouched bounded oldFrame newFrame =
  MkAdmittedDistanceMove (movedRoot move) (movedComponent move) (prefixWord move) (crossedAction move)
    (suffixWord move ++ [(OInsert following Root component)])
    (MkLocatedActionOccurrence (actionBeforeState (crossedOccurrence move)) (actionAfterState (crossedOccurrence move))
      (beforeActionOccurrence (crossedOccurrence move)) (locatedTransition (crossedOccurrence move))
      (appendTransitions (afterActionOccurrence (crossedOccurrence move)) (MoreTransitions (Fired {before = oldFinal} {afterState = oldSuccessor} nameEq keyEq (OInsert following Root component) OInsertTag oldRoot) NoTransitions)) (locatedAction (crossedOccurrence move))
      (trans (sym (appendTransitionsAssociative (beforeActionOccurrence (crossedOccurrence move))
        (MoreTransitions (locatedTransition (crossedOccurrence move)) (afterActionOccurrence (crossedOccurrence move))) (MoreTransitions (Fired {before = oldFinal} {afterState = oldSuccessor} nameEq keyEq (OInsert following Root component) OInsertTag oldRoot) NoTransitions)))
        (cong (\trace => appendTransitions trace (MoreTransitions (Fired {before = oldFinal} {afterState = oldSuccessor} nameEq keyEq (OInsert following Root component) OInsertTag oldRoot) NoTransitions)) (actionOccurrenceDecomposition (crossedOccurrence move)))))
    (MkLocatedActionOccurrence (actionBeforeState (movedBirthOccurrence move)) (actionAfterState (movedBirthOccurrence move))
      (beforeActionOccurrence (movedBirthOccurrence move)) (locatedTransition (movedBirthOccurrence move))
      (appendTransitions (afterActionOccurrence (movedBirthOccurrence move)) (MoreTransitions (Fired {before = newFinal} {afterState = newSuccessor} nameEq keyEq (OInsert following Root component) OInsertTag newRoot) NoTransitions)) (locatedAction (movedBirthOccurrence move))
      (trans (sym (appendTransitionsAssociative (beforeActionOccurrence (movedBirthOccurrence move))
        (MoreTransitions (locatedTransition (movedBirthOccurrence move)) (afterActionOccurrence (movedBirthOccurrence move))) (MoreTransitions (Fired {before = newFinal} {afterState = newSuccessor} nameEq keyEq (OInsert following Root component) OInsertTag newRoot) NoTransitions)))
        (cong (\trace => appendTransitions trace (MoreTransitions (Fired {before = newFinal} {afterState = newSuccessor} nameEq keyEq (OInsert following Root component) OInsertTag newRoot) NoTransitions)) (actionOccurrenceDecomposition (movedBirthOccurrence move)))))
    (crossedOrdinalExact move) (movedBirthOrdinalExact move) (crossingAdmitted move) forced
    (trans (nativeWordAppend oldTrail (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep oldFinal (Fired {before = oldFinal} {afterState = oldSuccessor} nameEq keyEq (OInsert following Root component) OInsertTag oldRoot) NoTransitions (DGamma.CP5AvailabilityAwarePlacement.AvailabilityEnd oldSuccessor)))
      (trans (cong (\word => word ++ [(OInsert following Root component)]) (oldWordExact move))
        (sym (appendAssociative (prefixWord move)
          (crossedAction move :: OInsert (movedRoot move) Root (movedComponent move) :: suffixWord move) [(OInsert following Root component)]))))
    (trans (nativeWordAppend newTrail (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep newFinal (Fired {before = newFinal} {afterState = newSuccessor} nameEq keyEq (OInsert following Root component) OInsertTag newRoot) NoTransitions (DGamma.CP5AvailabilityAwarePlacement.AvailabilityEnd newSuccessor)))
      (trans (cong (\word => word ++ [(OInsert following Root component)]) (newWordExact move))
        (sym (appendAssociative (prefixWord move)
          (OInsert (movedRoot move) Root (movedComponent move) :: crossedAction move :: suffixWord move) [(OInsert following Root component)]))))
    (oldCurrentCut move) (newCurrentCut move)
    (totalDistance nameEq keyEq (appendAvailability oldTrail (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep oldFinal (Fired {before = oldFinal} {afterState = oldSuccessor} nameEq keyEq (OInsert following Root component) OInsertTag oldRoot) NoTransitions (DGamma.CP5AvailabilityAwarePlacement.AvailabilityEnd oldSuccessor)))) (totalDistance nameEq keyEq (appendAvailability newTrail (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep newFinal (Fired {before = newFinal} {afterState = newSuccessor} nameEq keyEq (OInsert following Root component) OInsertTag newRoot) NoTransitions (DGamma.CP5AvailabilityAwarePlacement.AvailabilityEnd newSuccessor)))) Refl Refl
    (totalDistanceOneLeftFromFrame nameEq keyEq (appendAvailability oldTrail (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep oldFinal (Fired {before = oldFinal} {afterState = oldSuccessor} nameEq keyEq (OInsert following Root component) OInsertTag oldRoot) NoTransitions (DGamma.CP5AvailabilityAwarePlacement.AvailabilityEnd oldSuccessor))) (appendAvailability newTrail (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep newFinal (Fired {before = newFinal} {afterState = newSuccessor} nameEq keyEq (OInsert following Root component) OInsertTag newRoot) NoTransitions (DGamma.CP5AvailabilityAwarePlacement.AvailabilityEnd newSuccessor)))
      (length (prefixWord move)) target untouched bounded oldFrame newFrame)
    (replace {p = \next => RegistryExtensional name key world error value nameEq oldSuccessor next}
      (cong snd (justInjective (trans (sym (extensionalChecked (checkedRootAcrossExtensional nameEq keyEq following component oldFinal oldSuccessor newFinal OInsertTag
        oldRoot (moveEndpoints move) valid
        (provisionsDisjointFrom {name} {key} {world} {error} {value} @{keyEq}
          (componentProvisions component) (bindings (registry oldFinal))) Refl frame))) newRoot)))
      (extensionalAfterSame (checkedRootAcrossExtensional nameEq keyEq following component oldFinal oldSuccessor newFinal OInsertTag
        oldRoot (moveEndpoints move) valid
        (provisionsDisjointFrom {name} {key} {world} {error} {value} @{keyEq}
          (componentProvisions component) (bindings (registry oldFinal))) Refl frame)))
