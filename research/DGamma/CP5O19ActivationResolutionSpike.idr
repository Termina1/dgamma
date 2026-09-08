module DGamma.CP5O19ActivationResolutionSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP4DeletionSelectedForeignLifecycleCore
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorRelianceSelected
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Declared-key exclusion forces the ACTUAL provider candidate to be false,
||| irrespective of the lifecycle or table contents. Observe the Boolean once.
export
0 o19NonProviderObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (keyEq : DecEq key) -> (wanted : key) -> (fiber : Fiber name key value world error) ->
  (observed : Bool) -> (providerCandidate @{keyEq} wanted fiber = observed) ->
  Not (Elem wanted (dependencies (componentProvisions (fiberComponent fiber)))) ->
  observed = False
o19NonProviderObserved keyEq wanted fiber False exact excluded = Refl
o19NonProviderObserved keyEq wanted fiber True exact excluded =
  void (excluded (selectedCandidateDeclaresRelianceAnchor keyEq wanted fiber exact))
