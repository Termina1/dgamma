module DGamma.CP4DeletionSelectedForeignLifecycleAnchorCore

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import Decidable.Equality

%default total

||| Trace-derived alternatives for excluding the selected closing activation
||| from a retained foreign lifecycle target.  A closing foreign consumer is
||| rejected directly by `NoDependentClosingEpisode`.  A consumer whose last
||| activation remains open at the quiet endpoint is handled by Lemma 70: its
||| endpoint Active/support witness and the registry's single-provider
||| invariant force every declared provider to be Active, while the selected
||| closing activation is Inactive.
|||
||| This is an internal Lemma-72 intermediate.  Its constructors are populated
||| from the public trace premises; it is not an additional public premise of
||| `deletionTheorem`.
public export
data ForeignLifecyclePrecedenceAnchor :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (global : Transitions initial finalState) ->
  (selected, actor : name) ->
  (currentSelected, currentOwner : Fiber name key value world error) -> Type where
  ClosedForeignLifecyclePrecedenceAnchor :
    (consumerEpisode : LocatedClosedEpisode name key world error value
      nameEq keyEq actor global) ->
    (openingSelected : Fiber name key value world error) ->
    (openingOwner : Fiber name key value world error) ->
    lookupFiber @{nameEq} selected
      (registry (closedStartState (locatedEpisode consumerEpisode))) =
        Just openingSelected ->
    lookupFiber @{nameEq} actor
      (registry (closedStartState (locatedEpisode consumerEpisode))) =
        Just openingOwner ->
    fiberComponent openingSelected = fiberComponent currentSelected ->
    fiberComponent openingOwner = fiberComponent currentOwner ->
    ForeignLifecyclePrecedenceAnchor name key world error value nameEq keyEq
      global selected actor currentSelected currentOwner
  OpenForeignLifecyclePrecedenceAnchor :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {keyEq : DecEq key} ->
    {initial, finalState : SystemState name key value world error} ->
    {global : Transitions initial finalState} ->
    {selected, actor : name} ->
    {currentSelected, currentOwner : Fiber name key value world error} ->
    (finalSelected : Fiber name key value world error) ->
    (finalOwner : Fiber name key value world error) ->
    lookupFiber @{nameEq} selected (registry finalState) = Just finalSelected ->
    lookupFiber @{nameEq} actor (registry finalState) = Just finalOwner ->
    fiberComponent finalSelected = fiberComponent currentSelected ->
    fiberComponent finalOwner = fiberComponent currentOwner ->
    isActive (fiberLifecycle finalSelected) = False ->
    isActive (fiberLifecycle finalOwner) = True ->
    registryWellFormed @{nameEq} @{keyEq} finalState = True ->
    SupportMatchesActive nameEq keyEq finalState ->
    ForeignLifecyclePrecedenceAnchor name key world error value nameEq keyEq
      global selected actor currentSelected currentOwner
