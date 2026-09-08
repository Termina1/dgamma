module DGamma.CP5O20AllNameSynchronizationSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5O19SurfaceSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5O20EpisodeSynchronizationSpike
import DGamma.CP5O20PairedPrefixProducerSpike
import DGamma.CP5O20BeginObservationSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| The genuine paired-cut invariant for the first THREE bridge clauses.
||| ALL raw names, including unsupported/absent/retired names, are quantified.
||| Its type does not assert that accepted canonical endpoints satisfy it.
||| Production at actual intermediate cuts starts from the empty origin and
||| derives successor fields; callers do not supply endpoint conclusions.
public export
record O20AllNameCut
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (renaming : NameBijection name)
  (left, right : SystemState name key value world error) where
  constructor MkO20AllNameCut
  0 allNameEffects : RenamedRuntimeEffects name key world value renaming
    (projectEffectState {name} {key} {value} {world} {error} @{nameEq} left)
    (projectEffectState {name} {key} {value} {world} {error} @{nameEq} right)
  0 allNameControls : (selected : name) ->
    MaybeFiberRelatedBy {name} {key} {value} {world} {error} renaming
      (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry left))
      (lookupFiber {name} {key} {value} {world} {error} @{nameEq}
        (renameForward renaming selected) (registry right))

||| Full empty-origin PRODUCER. The only input property is the actual empty
||| runtime registry; effects and controls for EVERY queried name are derived.
export
0 o20AllNameEmptyOrigin :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (renaming : NameBijection name) ->
  (initial : SystemState name key value world error) -> (bindings (registry initial) = []) ->
  O20AllNameCut name key world error value nameEq renaming initial initial
o20AllNameEmptyOrigin {name} {key} {world} {error} {value} nameEq renaming
  (MkSystemState ambient fibers) empty =
    MkO20AllNameCut
      (MkRenamedRuntimeEffects Refl (synchronizationEmptyTables name key world error value nameEq renaming ambient fibers empty))
      (\selected => snd (synchronizationEmptyObservations name key world error value nameEq renaming ambient fibers empty selected))

||| General ALL-NAME successor for two actual replacements. The owner case
||| uses the produced new local control relation; every foreign name uses the
||| old all-name invariant, regardless of support/absence/retirement status.
export
0 o20PairedReplaceControls :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (renaming : NameBijection name) -> (actor : name) ->
  (leftOld, rightOld, leftNext, rightNext : Fiber name key value world error) ->
  (leftRegistry, rightRegistry : Registry name key value world error) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor leftRegistry = Just leftOld) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (renameForward renaming actor) rightRegistry = Just rightOld) ->
  FiberRelatedBy renaming leftNext rightNext ->
  ((selected : name) -> MaybeFiberRelatedBy renaming
    (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected leftRegistry)
    (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (renameForward renaming selected) rightRegistry)) ->
  (selected : name) -> MaybeFiberRelatedBy renaming
    (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (replaceBinding @{nameEq} actor leftNext leftRegistry))
    (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (renameForward renaming selected)
      (replaceBinding @{nameEq} (renameForward renaming actor) rightNext rightRegistry))
o20PairedReplaceControls nameEq renaming actor leftOld rightOld leftNext rightNext
  leftRegistry rightRegistry leftFound rightFound nextRelated previous selected =
    case decEq @{nameEq} selected actor of
      Yes same => rewrite same in
        rewrite lookupReplacedFiber @{nameEq} actor leftOld leftNext leftRegistry leftFound in
        rewrite lookupReplacedFiber @{nameEq} (renameForward renaming actor) rightOld rightNext rightRegistry rightFound in
          RenamedPresent nextRelated
      No different =>
        rewrite lookupReplaceOther @{nameEq} selected actor different leftNext leftRegistry in
        rewrite lookupReplaceOther @{nameEq} (renameForward renaming selected) (renameForward renaming actor)
          (\same => different (trans (sym (renameLeftInverse renaming selected))
            (trans (cong (renameBackward renaming) same) (renameLeftInverse renaming actor)))) rightNext rightRegistry in
          previous selected

||| One constructor elimination at two explicitly observed present fibers.
export
0 o20PresentControl :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {renaming : NameBijection name} -> {left, right : Fiber name key value world error} ->
  MaybeFiberRelatedBy renaming (Just left) (Just right) -> FiberRelatedBy renaming left right
o20PresentControl (RenamedPresent related) = related

||| Component equality and parent renaming are DERIVED from full fiber
||| control relation, not supplied as new assumptions for actual Begin plans.
export
0 o20RelatedFiberMetadata :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {renaming : NameBijection name} -> {left, right : Fiber name key value world error} ->
  FiberRelatedBy renaming left right ->
  ((fiberComponent left = fiberComponent right), ParentRelatedBy renaming (fiberParent left) (fiberParent right))
o20RelatedFiberMetadata (RenamedFibers leftParent rightParent leftRetired rightRetired
  leftTable rightTable leftLifecycle rightLifecycle parents retired lifecycle) = (Refl, parents)

||| Actual Begin observations plus the INTERNAL pre-cut relation derive the
||| component equality and renamed parents required to pair their interpreters.
export
0 o20ObservedBeginsMetadata :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (renaming : NameBijection name) -> (actor : name) ->
  (leftBefore, leftAfter, rightBefore, rightAfter : SystemState name key value world error) ->
  (left : O20BeginObservation name key world error value nameEq keyEq actor leftBefore leftAfter) ->
  (right : O20BeginObservation name key world error value nameEq keyEq (renameForward renaming actor) rightBefore rightAfter) ->
  O20AllNameCut name key world error value nameEq renaming leftBefore rightBefore ->
  ((beginObservedComponent left = beginObservedComponent right),
    ParentRelatedBy renaming (beginObservedParent left) (beginObservedParent right))
o20ObservedBeginsMetadata nameEq keyEq renaming actor leftBefore leftAfter rightBefore rightAfter left right paired =
  o20RelatedFiberMetadata
    {left = MkFiber (beginObservedComponent left) (beginObservedParent left) False (beginObservedTable left) (Inactive Nothing)}
    {right = MkFiber (beginObservedComponent right) (beginObservedParent right) False (beginObservedTable right) (Inactive Nothing)}
    (o20PresentControl (rewrite sym (beginObservedFound left) in
      rewrite sym (beginObservedFound right) in allNameControls paired actor))

||| B7 stop gate authorized DISTINCT shared-COMPONENT boundary. The common
||| runtime component is explicit and authenticated at BOTH actual source
||| lookups, with both actual resolver equations. No projected-record equality
||| is eliminated, and this is NOT a reattempt/claim of the general B7 theorem.
export
0 o20SharedComponentBeginControl :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (renaming : NameBijection name) -> (actor : name) ->
  (component : Component key value world error) -> (leftParent, rightParent : Parent name) ->
  (leftTable, rightTable : OwnedTable key value (componentProvisions component)) ->
  (leftView, rightView : View name (dependencies (componentDependencies component))) ->
  (left, right : SystemState name key value world error) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry left) =
    Just (MkFiber component leftParent False leftTable (Inactive Nothing))) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (renameForward renaming actor) (registry right) =
    Just (MkFiber component rightParent False rightTable (Inactive Nothing))) ->
  (resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (dependencies (componentDependencies component)) (registry left) = Just leftView) ->
  (resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (dependencies (componentDependencies component)) (registry right) = Just rightView) ->
  O20AllNameCut name key world error value nameEq renaming left right ->
  (pairwiseProvisionInvariant {name} {key} {value} {world} {error} @{keyEq} (bindings (registry right)) = True) ->
  FiberRelatedBy renaming
    (MkFiber component leftParent False leftTable (Reloading (componentProgram component) id leftView))
    (MkFiber component rightParent False rightTable (Reloading (componentProgram component) id rightView))
o20SharedComponentBeginControl {name} {key} {world} {error} {value} nameEq keyEq renaming actor
  component leftParent rightParent leftTable rightTable leftView rightView
  (MkSystemState leftWorld leftRegistry) (MkSystemState rightWorld rightRegistry)
  leftFound rightFound leftResolved rightResolved paired pairwise =
    RenamedFibers leftParent rightParent False False leftTable rightTable
      (Reloading (componentProgram component) id leftView) (Reloading (componentProgram component) id rightView)
      (snd (o20RelatedFiberMetadata
        {left = MkFiber component leftParent False leftTable (Inactive Nothing)}
        {right = MkFiber component rightParent False rightTable (Inactive Nothing)}
        (o20PresentControl (rewrite sym leftFound in rewrite sym rightFound in allNameControls paired actor))))
      Refl (RenamedReloading Refl localStateRuntimeReflexive
        (pairedActualResolvedViews name key world error value nameEq keyEq renaming
          (dependencies (componentDependencies component)) leftWorld rightWorld leftRegistry rightRegistry
          (allNameEffects paired) pairwise leftView rightView leftResolved rightResolved))

||| Derive effects AND EVERY control at the actual two fresh insert outputs.
||| Freshness is observed on both runtime registries. A whole paired schedule
||| must still authenticate protocol/orchestration guards and select these cuts.
export
0 o20AllNameInsert :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (renaming : NameBijection name) -> (actor : name) ->
  (component : Component key value world error) -> (leftParent, rightParent : Parent name) ->
  ParentRelatedBy renaming leftParent rightParent ->
  (leftWorld, rightWorld : world) -> (leftRegistry, rightRegistry : Registry name key value world error) ->
  (leftAbsent : (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor leftRegistry = Nothing)) ->
  (rightAbsent : (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (renameForward renaming actor) rightRegistry = Nothing)) ->
  O20AllNameCut name key world error value nameEq renaming
    (MkSystemState leftWorld leftRegistry) (MkSystemState rightWorld rightRegistry) ->
  O20AllNameCut name key world error value nameEq renaming
    (MkSystemState leftWorld (insertBinding @{nameEq} actor (freshFiber component leftParent) leftRegistry leftAbsent))
    (MkSystemState rightWorld (insertBinding @{nameEq} (renameForward renaming actor) (freshFiber component rightParent) rightRegistry rightAbsent))
o20AllNameInsert {name} {key} {world} {error} {value} nameEq keyEq renaming actor component
  leftParent rightParent parents leftWorld rightWorld leftRegistry rightRegistry leftAbsent rightAbsent paired =
    MkO20AllNameCut
      (pairedInsertEffects name key world error value nameEq keyEq renaming actor component
        leftParent rightParent leftWorld rightWorld leftRegistry rightRegistry leftAbsent rightAbsent (allNameEffects paired))
      (\selected => pairedInsertControls name key world error value nameEq renaming actor component
        leftParent rightParent parents leftRegistry rightRegistry leftAbsent rightAbsent selected (allNameControls paired selected))
