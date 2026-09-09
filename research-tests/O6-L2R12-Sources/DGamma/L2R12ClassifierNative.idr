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
