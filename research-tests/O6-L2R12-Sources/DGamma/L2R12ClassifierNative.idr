module DGamma.L2R12ClassifierNative

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.CP5L2R1ChildRelocation
import DGamma.L2R5RootCatalog
import DGamma.L2R10MoveCutObservation
import DGamma.L2R11ClassifierSquare
import DGamma.L2R12AlignedCut
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Normalize an ACTUAL Retire edge's tag from native lookup and source
||| validity, by checked determinism. The target is preserved literally.
export
0 retireTagNormalize : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child : name) ->
  (fiber : Fiber name key value world error) ->
  (before, afterState : SystemState name key value world error) -> (tag : RuleTag) ->
  (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry before) = Just fiber) ->
  (0 valid : registryWellFormed @{nameEq} @{keyEq} before = True) ->
  (0 original : checkedApplyAction @{nameEq} @{keyEq} (ORetire child) before = Just (tag, afterState)) ->
  checkedApplyAction @{nameEq} @{keyEq} (ORetire child) before = Just (ORetireTag, afterState)
retireTagNormalize nameEq keyEq child fiber before afterState tag found valid original =
  trans original (cong (\selectedTag => Just (selectedTag, afterState))
    (cong fst (justInjective (trans (sym original)
      (childRetireAtFound nameEq keyEq child fiber before found valid)))))

||| The selected classifier square now obtains its ORIGINAL Retire edge,
||| tag and target FROM the aligned source-query decoder. Only the following
||| root edge at that target is still explicit; transporting the catalog
||| birth to that successor state remains open despite ordinal adjacency.
export
0 selectedRetireFromAligned : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  {trace : Transitions first finalState} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (trail : AvailabilityTrace name key world error value trace) ->
  (aligned : AlignedTransitions name key world error value nameEq keyEq trace) ->
  (cut : SelectedSquareCut name key world error value nameEq keyEq trail) ->
  (child : name) -> (fiber : Fiber name key value world error) ->
  (0 selectedAction : cutAction cut = ORetire child) ->
  (oldFinal, earlyRoot : SystemState name key value world error) ->
  (0 accepted : earlyRootResult cut = Just (OInsertTag, earlyRoot)) ->
  (0 valid : registryWellFormed @{nameEq} @{keyEq} (cutSource cut) = True) ->
  (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry (cutSource cut)) = Just fiber) ->
  (0 oldRoot : checkedApplyAction @{nameEq} @{keyEq}
    (OInsert (catalogRoot (cutEntry cut)) Root (catalogComponent (cutEntry cut)))
    (edgeTarget (selectedCutAlignedEdge nameEq keyEq trail aligned cut)) = Just (OInsertTag, oldFinal)) ->
  Maybe (ClassifierSquare name key world error value nameEq keyEq
    (catalogRoot (cutEntry cut)) (catalogComponent (cutEntry cut)) (cutSource cut) (cutAction cut) ORetireTag oldFinal)
selectedRetireFromAligned {name} {key} {world} {error} {value}
  nameEq keyEq trail aligned cut child fiber selectedAction oldFinal earlyRoot accepted valid found oldRoot =
  selectedRetireSquare nameEq keyEq trail cut child selectedAction
    (edgeTarget (selectedCutAlignedEdge nameEq keyEq trail aligned cut)) oldFinal earlyRoot accepted valid
    (retireTagNormalize nameEq keyEq child fiber (cutSource cut)
      (edgeTarget (selectedCutAlignedEdge nameEq keyEq trail aligned cut))
      (edgeTag (selectedCutAlignedEdge nameEq keyEq trail aligned cut)) found valid
      (trans (cong (\action => checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} action (cutSource cut))
        (sym selectedAction)) (edgeChecked (selectedCutAlignedEdge nameEq keyEq trail aligned cut)))) oldRoot
