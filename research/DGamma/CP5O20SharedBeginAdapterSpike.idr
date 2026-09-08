module DGamma.CP5O20SharedBeginAdapterSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5O20BeginObservationSpike
import DGamma.CP5O20AllNameSynchronizationSpike
import Decidable.Equality

%default total
%unbound_implicits off

||| B8-style paired observed values: one runtime component, but the two ACTUAL
||| tables, parents, resolver views and output equations. This is the shared
||| adapter boundary, not a projected-record equality or endpoint oracle.
public export
record O20SharedBeginObservations
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (renaming : NameBijection name) (actor : name)
  (leftBefore, leftAfter, rightBefore, rightAfter : SystemState name key value world error) where
  constructor MkO20SharedBeginObservations
  sharedBeginComponent : Component key value world error
  sharedLeftParent : Parent name
  sharedRightParent : Parent name
  sharedLeftTable : OwnedTable key value (componentProvisions sharedBeginComponent)
  sharedRightTable : OwnedTable key value (componentProvisions sharedBeginComponent)
  sharedLeftView : View name (dependencies (componentDependencies sharedBeginComponent))
  sharedRightView : View name (dependencies (componentDependencies sharedBeginComponent))
  0 sharedLeftFound : lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry leftBefore) =
    Just (MkFiber sharedBeginComponent sharedLeftParent False sharedLeftTable (Inactive Nothing))
  0 sharedRightFound : lookupFiber {name} {key} {value} {world} {error} @{nameEq} (renameForward renaming actor) (registry rightBefore) =
    Just (MkFiber sharedBeginComponent sharedRightParent False sharedRightTable (Inactive Nothing))
  0 sharedLeftResolved : resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (dependencies (componentDependencies sharedBeginComponent)) (registry leftBefore) = Just sharedLeftView
  0 sharedRightResolved : resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (dependencies (componentDependencies sharedBeginComponent)) (registry rightBefore) = Just sharedRightView
  0 sharedLeftAfter : MkSystemState (worldState leftBefore) (replaceBinding @{nameEq} actor
    (MkFiber sharedBeginComponent sharedLeftParent False sharedLeftTable
      (Reloading (componentProgram sharedBeginComponent) id sharedLeftView)) (registry leftBefore)) = leftAfter
  0 sharedRightAfter : MkSystemState (worldState rightBefore) (replaceBinding @{nameEq} (renameForward renaming actor)
    (MkFiber sharedBeginComponent sharedRightParent False sharedRightTable
      (Reloading (componentProgram sharedBeginComponent) id sharedRightView)) (registry rightBefore)) = rightAfter

||| Eliminate equality of TWO EXPLICIT component VALUES before their dependent
||| payloads. No equality between projections of suspended observation records
||| is eliminated. The next producer derives this scalar equality itself.
export
0 o20ShareBeginValues :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {renaming : NameBijection name} -> {actor : name} ->
  {leftBefore, leftAfter, rightBefore, rightAfter : SystemState name key value world error} ->
  (leftComponent, rightComponent : Component key value world error) -> leftComponent = rightComponent ->
  (leftParent, rightParent : Parent name) ->
  (leftTable : OwnedTable key value (componentProvisions leftComponent)) ->
  (rightTable : OwnedTable key value (componentProvisions rightComponent)) ->
  (leftView : View name (dependencies (componentDependencies leftComponent))) ->
  (rightView : View name (dependencies (componentDependencies rightComponent))) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry leftBefore) =
    Just (MkFiber leftComponent leftParent False leftTable (Inactive Nothing))) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (renameForward renaming actor) (registry rightBefore) =
    Just (MkFiber rightComponent rightParent False rightTable (Inactive Nothing))) ->
  (resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (dependencies (componentDependencies leftComponent)) (registry leftBefore) = Just leftView) ->
  (resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (dependencies (componentDependencies rightComponent)) (registry rightBefore) = Just rightView) ->
  (MkSystemState (worldState leftBefore) (replaceBinding @{nameEq} actor
    (MkFiber leftComponent leftParent False leftTable (Reloading (componentProgram leftComponent) id leftView)) (registry leftBefore)) = leftAfter) ->
  (MkSystemState (worldState rightBefore) (replaceBinding @{nameEq} (renameForward renaming actor)
    (MkFiber rightComponent rightParent False rightTable (Reloading (componentProgram rightComponent) id rightView)) (registry rightBefore)) = rightAfter) ->
  O20SharedBeginObservations name key world error value nameEq keyEq renaming actor leftBefore leftAfter rightBefore rightAfter
o20ShareBeginValues component component Refl leftParent rightParent leftTable rightTable leftView rightView
  leftFound rightFound leftResolved rightResolved leftAfter rightAfter =
    MkO20SharedBeginObservations component leftParent rightParent leftTable rightTable leftView rightView
      leftFound rightFound leftResolved rightResolved leftAfter rightAfter

||| Both actual observation records are opened FIRST. Their component equality
||| is derived from the all-name cut and consumed only at B2's explicit-value
||| boundary. No shared-component or dependent cast oracle is a premise.
export
0 o20ShareObservedBegins :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (renaming : NameBijection name) -> (actor : name) ->
  (leftBefore, leftAfter, rightBefore, rightAfter : SystemState name key value world error) ->
  O20BeginObservation name key world error value nameEq keyEq actor leftBefore leftAfter ->
  O20BeginObservation name key world error value nameEq keyEq (renameForward renaming actor) rightBefore rightAfter ->
  O20AllNameCut name key world error value nameEq renaming leftBefore rightBefore ->
  O20SharedBeginObservations name key world error value nameEq keyEq renaming actor leftBefore leftAfter rightBefore rightAfter
o20ShareObservedBegins nameEq keyEq renaming actor leftBefore leftAfter rightBefore rightAfter
  (MkO20BeginObservation leftComponent leftParent leftTable leftView leftFound leftResolved leftExact)
  (MkO20BeginObservation rightComponent rightParent rightTable rightView rightFound rightResolved rightExact) paired =
    o20ShareBeginValues leftComponent rightComponent
      (fst (o20ObservedBeginsMetadata nameEq keyEq renaming actor leftBefore leftAfter rightBefore rightAfter
        (MkO20BeginObservation leftComponent leftParent leftTable leftView leftFound leftResolved leftExact)
        (MkO20BeginObservation rightComponent rightParent rightTable rightView rightFound rightResolved rightExact) paired))
      leftParent rightParent leftTable rightTable leftView rightView leftFound rightFound leftResolved rightResolved leftExact rightExact

||| General ACTUAL BeginStep producer: neither observations, shared component,
||| resolution witnesses nor output equations are supplied by the caller.
export
0 o20ObserveSharedActualBegins :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (renaming : NameBijection name) -> (actor : name) ->
  (leftBefore, leftAfter, rightBefore, rightAfter : SystemState name key value world error) ->
  BeginStep nameEq keyEq actor leftBefore leftAfter ->
  BeginStep nameEq keyEq (renameForward renaming actor) rightBefore rightAfter ->
  O20AllNameCut name key world error value nameEq renaming leftBefore rightBefore ->
  O20SharedBeginObservations name key world error value nameEq keyEq renaming actor leftBefore leftAfter rightBefore rightAfter
o20ObserveSharedActualBegins nameEq keyEq renaming actor leftBefore leftAfter rightBefore rightAfter leftOpening rightOpening paired =
  o20ShareObservedBegins nameEq keyEq renaming actor leftBefore leftAfter rightBefore rightAfter
    (o20ObserveActualBegin nameEq keyEq actor leftBefore leftAfter leftOpening)
    (o20ObserveActualBegin nameEq keyEq (renameForward renaming actor) rightBefore rightAfter rightOpening) paired

||| Consume the producer-owned shared observation at the existing B8 successor.
||| Its exact component-indexed payloads need no projected-record coercions.
export
0 o20BeginCutFromSharedObservations :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (renaming : NameBijection name) -> (actor : name) ->
  (leftBefore, leftAfter, rightBefore, rightAfter : SystemState name key value world error) ->
  BeginStep nameEq keyEq actor leftBefore leftAfter ->
  BeginStep nameEq keyEq (renameForward renaming actor) rightBefore rightAfter ->
  O20SharedBeginObservations name key world error value nameEq keyEq renaming actor leftBefore leftAfter rightBefore rightAfter ->
  O20AllNameCut name key world error value nameEq renaming leftBefore rightBefore ->
  (pairwiseProvisionInvariant {name} {key} {value} {world} {error} @{keyEq} (bindings (registry rightBefore)) = True) ->
  O20AllNameCut name key world error value nameEq renaming leftAfter rightAfter
o20BeginCutFromSharedObservations nameEq keyEq renaming actor leftBefore leftAfter rightBefore rightAfter leftOpening rightOpening
  (MkO20SharedBeginObservations component leftParent rightParent leftTable rightTable leftView rightView
    leftFound rightFound leftResolved rightResolved leftExact rightExact) paired pairwise =
      o20SharedObservedBeginCut nameEq keyEq renaming actor leftBefore leftAfter rightBefore rightAfter
        leftOpening rightOpening component leftParent rightParent leftTable rightTable leftView rightView
        leftFound rightFound leftResolved rightResolved leftExact rightExact paired pairwise

||| GENERAL paired actual Begin successor, including ALL names. Shared
||| component, both actual views, both exact updates and control correspondence
||| are now produced internally from the real steps and the pre-cut invariant.
export
0 o20PairedActualBeginCut :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (renaming : NameBijection name) -> (actor : name) ->
  (leftBefore, leftAfter, rightBefore, rightAfter : SystemState name key value world error) ->
  BeginStep nameEq keyEq actor leftBefore leftAfter ->
  BeginStep nameEq keyEq (renameForward renaming actor) rightBefore rightAfter ->
  O20AllNameCut name key world error value nameEq renaming leftBefore rightBefore ->
  (pairwiseProvisionInvariant {name} {key} {value} {world} {error} @{keyEq} (bindings (registry rightBefore)) = True) ->
  O20AllNameCut name key world error value nameEq renaming leftAfter rightAfter
o20PairedActualBeginCut nameEq keyEq renaming actor leftBefore leftAfter rightBefore rightAfter leftOpening rightOpening paired pairwise =
  o20BeginCutFromSharedObservations nameEq keyEq renaming actor leftBefore leftAfter rightBefore rightAfter leftOpening rightOpening
    (o20ObserveSharedActualBegins nameEq keyEq renaming actor leftBefore leftAfter rightBefore rightAfter leftOpening rightOpening paired)
    paired pairwise
