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


||| E4 consumes the independently checked observed-Boolean head boundary.
export
0 o19ProviderReplaceHeadObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (wanted : key) ->
  (actor, current : name) -> (old, next : Fiber name key value world error) ->
  (rest : List (Binding name (FiberAt name key value world error))) ->
  (decision : Dec (actor = current)) -> (decEq @{nameEq} actor current = decision) ->
  (providerCandidate @{keyEq} wanted next = False) ->
  ((actor = current) -> providerCandidate @{keyEq} wanted old = False) ->
  (providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted (replaceEntries @{nameEq} actor next rest) = providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted rest) ->
  (providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted (replaceEntries @{nameEq} actor next (Bind current old :: rest)) =
   providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted (Bind current old :: rest))
o19ProviderReplaceHeadObserved nameEq keyEq wanted actor _ old next rest (Yes Refl) exact nextFalse oldFalse tailSame =
  rewrite exact in rewrite nextFalse in rewrite oldFalse Refl in Refl
o19ProviderReplaceHeadObserved nameEq keyEq wanted actor current old next rest (No distinct) exact nextFalse oldFalse tailSame =
  rewrite exact in o19ProviderHeadObserved nameEq keyEq wanted current old
    (replaceEntries @{nameEq} actor next rest) rest
    (isActive (fiberLifecycle old) && memberKey @{keyEq} wanted (ownedValues (fiberTable old))) Refl tailSame

||| Induction on the ACTUAL ordered registry entries. Every unchanged head
||| passes through E3; the selected head is absent as a provider on both sides.
export
0 o19ProviderReplaceEntries :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (wanted : key) ->
  (actor : name) -> (next : Fiber name key value world error) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (providerCandidate @{keyEq} wanted next = False) ->
  ((old : Fiber name key value world error) -> Elem (Bind actor old) entries -> providerCandidate @{keyEq} wanted old = False) ->
  (providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted (replaceEntries @{nameEq} actor next entries) =
   providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted entries)
o19ProviderReplaceEntries nameEq keyEq wanted actor next [] nextFalse excluded = Refl
o19ProviderReplaceEntries nameEq keyEq wanted actor next (Bind current old :: rest) nextFalse excluded =
  o19ProviderReplaceHeadObserved nameEq keyEq wanted actor current old next rest
    (decEq @{nameEq} actor current) Refl nextFalse
    (\same => excluded old (rewrite same in Here))
    (o19ProviderReplaceEntries nameEq keyEq wanted actor next rest nextFalse (\fiber, occurs => excluded fiber (There occurs)))
