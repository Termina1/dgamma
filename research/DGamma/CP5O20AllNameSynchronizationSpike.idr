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
