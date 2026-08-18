module DGamma.CP4DeletionSelectedForeignLifecycleGuards

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP4DeletionSelectedForeignLifecycleCore
import DGamma.CP4DeletionSelectedForeignLifecycleFrame
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total

0 justInjectiveLifecycleGuards : Just left = Just right -> left = right
justInjectiveLifecycleGuards Refl = Refl

0 selectedSourceRightCandidateFalse :
  (keyEq : DecEq key) -> (wanted : key) ->
  {current : name} ->
  {left, right : Fiber name key value world error} ->
  ForeignLifecycleSourceCellRelated name key world error value nameEq keyEq
    selected current deps left right ->
  current = selected ->
  providerCandidate @{keyEq} wanted right = False
selectedSourceRightCandidateFalse keyEq wanted
  (SelectedLifecycleSourceCell currentIsSelected static rightUninstalled
    rightInactive rightReliedFalse leftProviderFalse) same =
      rewrite rightInactive in Refl
selectedSourceRightCandidateFalse keyEq wanted
  (ForeignLifecycleSourceCell currentDistinct controls tablesSame reliedSame)
  same = void (currentDistinct same)

0 foreignLifecycleSourceCandidateSame :
  (keyEq : DecEq key) -> (wanted : key) -> Elem wanted deps ->
  {current : name} ->
  {left, right : Fiber name key value world error} ->
  ForeignLifecycleSourceCellRelated name key world error value nameEq keyEq
    selected current deps left right ->
  providerCandidate @{keyEq} wanted left =
    providerCandidate @{keyEq} wanted right
foreignLifecycleSourceCandidateSame keyEq wanted present
  (SelectedLifecycleSourceCell currentIsSelected static rightUninstalled
    rightInactive rightReliedFalse leftProviderFalse) =
      trans (leftProviderFalse wanted present)
        (sym (selectedSourceRightCandidateFalse keyEq wanted
          (SelectedLifecycleSourceCell currentIsSelected static rightUninstalled
            rightInactive rightReliedFalse leftProviderFalse)
          currentIsSelected))
foreignLifecycleSourceCandidateSame keyEq wanted present
  (ForeignLifecycleSourceCell currentDistinct controls tablesSame reliedSame) =
    foreignProviderCandidateSame keyEq wanted controls tablesSame

||| Every declared dependency sees the same first active provider in the exact
||| ordered registry.  The selected cell is false on both sides; every foreign
||| cell compares its complete ordered owned-table bindings.
public export
0 foreignLifecycleProviderInSame :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {selected : name} -> {deps : List key} ->
  (keyEq : DecEq key) -> (wanted : key) -> Elem wanted deps ->
  (left, right : List (Binding name (FiberAt name key value world error))) ->
  ForeignLifecycleOrderedSourcesRelated name key world error value nameEq keyEq
    selected deps left right ->
  providerIn @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} wanted left =
  providerIn @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} wanted right
foreignLifecycleProviderInSame keyEq wanted present [] []
  ForeignLifecycleSourcesNil = Refl
foreignLifecycleProviderInSame keyEq wanted present
  (Bind current leftFiber :: leftRest)
  (Bind current rightFiber :: rightRest)
  (ForeignLifecycleSourcesCons current relation tail)
  with (isActive (fiberLifecycle rightFiber) &&
    memberKey @{keyEq} wanted (ownedValues (fiberTable rightFiber)))
    proof rightCandidate
  foreignLifecycleProviderInSame keyEq wanted present
    (Bind current leftFiber :: leftRest)
    (Bind current rightFiber :: rightRest)
    (ForeignLifecycleSourcesCons current relation tail) | False =
      let 0 candidatesSame = foreignLifecycleSourceCandidateSame keyEq wanted
            present relation
          0 runtimeCandidatesSame :
            (isActive (fiberLifecycle leftFiber) &&
              memberKey @{keyEq} wanted (ownedValues (fiberTable leftFiber)) =
             isActive (fiberLifecycle rightFiber) &&
              memberKey @{keyEq} wanted (ownedValues (fiberTable rightFiber)))
          runtimeCandidatesSame = trans
            (sym (providerCandidateExplicit keyEq wanted leftFiber))
            (trans candidatesSame
              (providerCandidateExplicit keyEq wanted rightFiber))
          0 leftFalse :
            (isActive (fiberLifecycle leftFiber) &&
              memberKey @{keyEq} wanted
                (ownedValues (fiberTable leftFiber)) = False)
          leftFalse = trans runtimeCandidatesSame rightCandidate
      in rewrite leftFalse in
        foreignLifecycleProviderInSame keyEq wanted present leftRest rightRest
          tail
  foreignLifecycleProviderInSame keyEq wanted present
    (Bind current leftFiber :: leftRest)
    (Bind current rightFiber :: rightRest)
    (ForeignLifecycleSourcesCons current relation tail) | True =
      let 0 candidatesSame = foreignLifecycleSourceCandidateSame keyEq wanted
            present relation
          0 runtimeCandidatesSame :
            (isActive (fiberLifecycle leftFiber) &&
              memberKey @{keyEq} wanted (ownedValues (fiberTable leftFiber)) =
             isActive (fiberLifecycle rightFiber) &&
              memberKey @{keyEq} wanted (ownedValues (fiberTable rightFiber)))
          runtimeCandidatesSame = trans
            (sym (providerCandidateExplicit keyEq wanted leftFiber))
            (trans candidatesSame
              (providerCandidateExplicit keyEq wanted rightFiber))
          0 leftTrue :
            (isActive (fiberLifecycle leftFiber) &&
              memberKey @{keyEq} wanted
                (ownedValues (fiberTable leftFiber)) = True)
          leftTrue = trans runtimeCandidatesSame rightCandidate
      in rewrite leftTrue in Refl

0 foreignLifecycleResolveViewSubsetSame :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {selected : name} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (requested, declared : List key) ->
  ((wanted : key) -> Elem wanted requested -> Elem wanted declared) ->
  (left, right : Registry name key value world error) ->
  ForeignLifecycleOrderedSourcesRelated name key world error value nameEq keyEq
    selected declared (bindings left) (bindings right) ->
  resolveView @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} requested left =
  resolveView @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} requested right
foreignLifecycleResolveViewSubsetSame nameEq keyEq [] declared subset left right
  related = Refl
foreignLifecycleResolveViewSubsetSame nameEq keyEq (wanted :: rest) declared
  subset left right related
  with (providerOf @{nameEq} @{keyEq} wanted left) proof leftProvider
  foreignLifecycleResolveViewSubsetSame nameEq keyEq (wanted :: rest) declared
    subset left right related | Nothing
    with (providerOf @{nameEq} @{keyEq} wanted right) proof rightProvider
    foreignLifecycleResolveViewSubsetSame nameEq keyEq (wanted :: rest)
      declared subset left right related | Nothing | Nothing = Refl
    foreignLifecycleResolveViewSubsetSame nameEq keyEq (wanted :: rest)
      declared subset left right related | Nothing | Just rightName =
        let contradiction : (Nothing = Just rightName)
            contradiction = trans (sym leftProvider)
              (trans (foreignLifecycleProviderInSame keyEq wanted
                (subset wanted Here) (bindings left) (bindings right) related)
                rightProvider)
        in case contradiction of Refl impossible
  foreignLifecycleResolveViewSubsetSame nameEq keyEq (wanted :: rest) declared
    subset left right related | Just leftName
    with (providerOf @{nameEq} @{keyEq} wanted right) proof rightProvider
    foreignLifecycleResolveViewSubsetSame nameEq keyEq (wanted :: rest)
      declared subset left right related | Just leftName | Nothing =
        let contradiction : (Just leftName = Nothing)
            contradiction = trans (sym leftProvider)
              (trans (foreignLifecycleProviderInSame keyEq wanted
                (subset wanted Here) (bindings left) (bindings right) related)
                rightProvider)
        in case contradiction of Refl impossible
    foreignLifecycleResolveViewSubsetSame nameEq keyEq (wanted :: rest)
      declared subset left right related | Just leftName | Just rightName =
        let sameName : (leftName = rightName)
            sameName = justInjectiveLifecycleGuards
              (trans (sym leftProvider)
                (trans (foreignLifecycleProviderInSame keyEq wanted
                  (subset wanted Here) (bindings left) (bindings right) related)
                  rightProvider))
        in case sameName of
          Refl => cong (map (ProviderView leftName))
            (foreignLifecycleResolveViewSubsetSame nameEq keyEq rest declared
              (\later, occurrence => subset later (There occurrence)) left right
              related)

||| Full target resolution is invariant under the saturated source relation.
public export
0 foreignLifecycleResolveViewSame :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {selected : name} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (deps : List key) ->
  (left, right : Registry name key value world error) ->
  ForeignLifecycleOrderedSourcesRelated name key world error value nameEq keyEq
    selected deps (bindings left) (bindings right) ->
  resolveView @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} deps left =
  resolveView @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} deps right
foreignLifecycleResolveViewSame nameEq keyEq deps left right related =
  foreignLifecycleResolveViewSubsetSame nameEq keyEq deps deps
    (\wanted, present => present) left right related
