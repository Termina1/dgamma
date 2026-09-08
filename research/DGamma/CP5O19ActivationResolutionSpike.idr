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

||| Separate observed-Boolean boundary approved after E2. The unchanged head
||| is decided from its actual candidate/equation, never by lazy-if congruence.
export
0 o19ProviderHeadObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (wanted : key) -> (current : name) ->
  (fiber : Fiber name key value world error) ->
  (left, right : List (Binding name (FiberAt name key value world error))) ->
  (observed : Bool) ->
  (isActive (fiberLifecycle fiber) && memberKey @{keyEq} wanted (ownedValues (fiberTable fiber)) = observed) ->
  (providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted left =
   providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted right) ->
  (providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted (Bind current fiber :: left) =
   providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted (Bind current fiber :: right))
o19ProviderHeadObserved nameEq keyEq wanted current fiber left right False exact tailSame = rewrite exact in tailSame
o19ProviderHeadObserved nameEq keyEq wanted current fiber left right True exact tailSame = rewrite exact in Refl
