module DGamma.CP5O20DiscardedSelectionCoverageSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5O20DeletionDisappearanceSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| The native Begin index update retains its discarded list at the observed
||| current-generation lookup. This is a scanner equation, not coverage.
export
0 o20BeginDiscardedObserved :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) ->
  (ordinal : Nat) -> (actor : name) -> (live : GenerationEnvironment name) ->
  (activations : List (name, RegistrationActivation name)) ->
  (counts : List (RegistrationActivation name, Nat)) -> (discarded : List (RegistrationGeneration name)) ->
  (observed : Maybe (RegistrationGeneration name)) ->
  (lookupCurrentGeneration @{nameEq} actor live = observed) ->
  (indexedDeletedGenerations (advanceRegistrationIndex @{nameEq} ordinal
    (the (Action name key value world error) (LBegin actor))
    (MkRegistrationIndexState live activations counts discarded)) = discarded)
o20BeginDiscardedObserved name key world error value nameEq ordinal actor live activations counts discarded Nothing exact =
  rewrite exact in Refl
o20BeginDiscardedObserved name key world error value nameEq ordinal actor live activations counts discarded (Just generation) exact =
  rewrite exact in Refl

||| Every ordinary native index update retains its discarded history.
export
0 o20IndexDiscardedAdvance :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) ->
  (ordinal : Nat) -> (action : Action name key value world error) -> (index : RegistrationIndexState name) ->
  (indexedDeletedGenerations (advanceRegistrationIndex @{nameEq} ordinal action index) =
    indexedDeletedGenerations index)
o20IndexDiscardedAdvance name key world error value nameEq ordinal (OInsert child Root component)
  (MkRegistrationIndexState live activations counts deleted) = Refl
o20IndexDiscardedAdvance name key world error value nameEq ordinal (OInsert child (ChildOf parent) component)
  (MkRegistrationIndexState live activations counts deleted) = Refl
o20IndexDiscardedAdvance name key world error value nameEq ordinal (ORetire actor)
  (MkRegistrationIndexState live activations counts deleted) = Refl
o20IndexDiscardedAdvance name key world error value nameEq ordinal (ORemove actor)
  (MkRegistrationIndexState live activations counts deleted) = Refl
o20IndexDiscardedAdvance name key world error value nameEq ordinal (LBegin actor)
  (MkRegistrationIndexState live activations counts deleted) =
    o20BeginDiscardedObserved name key world error value nameEq ordinal actor live activations counts deleted
      (lookupCurrentGeneration @{nameEq} actor live) Refl
o20IndexDiscardedAdvance name key world error value nameEq ordinal (LAdvance actor)
  (MkRegistrationIndexState live activations counts deleted) = Refl
o20IndexDiscardedAdvance name key world error value nameEq ordinal (LDivert actor)
  (MkRegistrationIndexState live activations counts deleted) = Refl
o20IndexDiscardedAdvance name key world error value nameEq ordinal (LLeave actor)
  (MkRegistrationIndexState live activations counts deleted) = Refl
o20IndexDiscardedAdvance name key world error value nameEq ordinal (LUnload actor)
  (MkRegistrationIndexState live activations counts deleted) = Refl

||| Observed surviving-Insert activation leaves discarded history unchanged.
export
0 o20SurvivingDiscardedObserved :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) ->
  (ordinal : Nat) -> (child, parent : name) -> (component : Component key value world error) ->
  (live : GenerationEnvironment name) ->
  (activations : List (name, RegistrationActivation name)) ->
  (counts : List (RegistrationActivation name, Nat)) -> (deleted : List (RegistrationGeneration name)) ->
  (observed : Maybe (RegistrationActivation name)) ->
  (lookupParentActivation @{nameEq} parent activations = observed) ->
  (indexedDeletedGenerations (advanceSurvivingRegistrationIndex @{nameEq} ordinal child parent component
    (MkRegistrationIndexState live activations counts deleted)) =
    deleted)
o20SurvivingDiscardedObserved name key world error value nameEq ordinal child parent component live activations counts deleted Nothing exact =
  rewrite exact in Refl
o20SurvivingDiscardedObserved name key world error value nameEq ordinal child parent component live activations counts deleted (Just activation) exact =
  rewrite exact in Refl

||| The public bilateral scanner cannot add a left discarded generation when
||| the actual left word contains no Unload. Right-only advances are retained;
||| the actual discard constructor contradicts its own closing occurrence.
export
0 o20NoUnloadDiscardedScan :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) ->
  (mapping : RegistrationGenerationBijection name) ->
  (leftOrdinal : Nat) -> (leftIndex : RegistrationIndexState name) ->
  (rightOrdinal : Nat) -> (rightIndex : RegistrationIndexState name) ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  (left : Transitions leftFirst leftFinal) -> (right : Transitions rightFirst rightFinal) ->
  (leftFinalIndex, rightFinalIndex : RegistrationIndexState name) ->
  {pendingLeft, pendingRight : List (RegistrationEvent name key world error value)} ->
  RegistrationTraceCorrespondence nameEq mapping leftOrdinal leftIndex left leftFinalIndex
    rightOrdinal rightIndex right rightFinalIndex pendingLeft pendingRight ->
  ((actor : name) -> (ActionOccurs (LUnload actor) left -> Void)) ->
  (indexedDeletedGenerations leftFinalIndex = indexedDeletedGenerations leftIndex)
o20NoUnloadDiscardedScan name key world error value nameEq mapping leftOrdinal
  (MkRegistrationIndexState live activations counts discarded) rightOrdinal rightIndex
  left right leftFinalIndex rightFinalIndex correspondence noUnload = case correspondence of
    RegistrationCorrespondenceEnd => Refl
    SkipLeftNonRegistration action step rest actionExact nonRegistration tail =>
      trans (o20NoUnloadDiscardedScan name key world error value nameEq mapping (S leftOrdinal)
        (advanceRegistrationIndex @{nameEq} leftOrdinal action (MkRegistrationIndexState live activations counts discarded))
        rightOrdinal rightIndex rest right leftFinalIndex rightFinalIndex tail
        (\actor, occurs => noUnload actor (ActionOccursLater step rest occurs)))
        (o20IndexDiscardedAdvance name key world error value nameEq leftOrdinal action
          (MkRegistrationIndexState live activations counts discarded))
    DiscardLeftDeletedRegistration {child} {parent} {component} step rest actionExact closing tail =>
      void (noUnload parent (ActionOccursLater step rest (deletedParentEpisodeCloses closing)))
    QueueLeftGeneratedRegistration {child} {parent} {component} step rest actionExact retained tail =>
      trans (o20NoUnloadDiscardedScan name key world error value nameEq mapping (S leftOrdinal)
        (advanceSurvivingRegistrationIndex @{nameEq} leftOrdinal child parent component (MkRegistrationIndexState live activations counts discarded))
        rightOrdinal rightIndex rest right leftFinalIndex rightFinalIndex tail
        (\actor, occurs => noUnload actor (ActionOccursLater step rest occurs)))
        (o20SurvivingDiscardedObserved name key world error value nameEq leftOrdinal child parent component
          live activations counts discarded (lookupParentActivation @{nameEq} parent activations) Refl)
    MatchLeftWithPendingRight {child} {parent} {component} step rest actionExact retained priorWords event laterWords matched tail =>
      trans (o20NoUnloadDiscardedScan name key world error value nameEq mapping (S leftOrdinal)
        (advanceSurvivingRegistrationIndex @{nameEq} leftOrdinal child parent component (MkRegistrationIndexState live activations counts discarded))
        rightOrdinal rightIndex rest right leftFinalIndex rightFinalIndex tail
        (\actor, occurs => noUnload actor (ActionOccursLater step rest occurs)))
        (o20SurvivingDiscardedObserved name key world error value nameEq leftOrdinal child parent component
          live activations counts discarded (lookupParentActivation @{nameEq} parent activations) Refl)
    SkipRightNonRegistration action step rest actionExact nonRegistration tail =>
      o20NoUnloadDiscardedScan name key world error value nameEq mapping leftOrdinal
        (MkRegistrationIndexState live activations counts discarded) (S rightOrdinal)
        (advanceRegistrationIndex @{nameEq} rightOrdinal action rightIndex)
        left rest leftFinalIndex rightFinalIndex tail noUnload
    DiscardRightDeletedRegistration {child} {parent} {component} step rest actionExact closing tail =>
      o20NoUnloadDiscardedScan name key world error value nameEq mapping leftOrdinal
        (MkRegistrationIndexState live activations counts discarded) (S rightOrdinal)
        (advanceDeletedRegistrationIndex @{nameEq} rightOrdinal child parent component rightIndex)
        left rest leftFinalIndex rightFinalIndex tail noUnload
    QueueRightGeneratedRegistration {child} {parent} {component} step rest actionExact retained tail =>
      o20NoUnloadDiscardedScan name key world error value nameEq mapping leftOrdinal
        (MkRegistrationIndexState live activations counts discarded) (S rightOrdinal)
        (advanceSurvivingRegistrationIndex @{nameEq} rightOrdinal child parent component rightIndex)
        left rest leftFinalIndex rightFinalIndex tail noUnload
    MatchRightWithPendingLeft {child} {parent} {component} step rest actionExact retained priorWords event laterWords matched tail =>
      o20NoUnloadDiscardedScan name key world error value nameEq mapping leftOrdinal
        (MkRegistrationIndexState live activations counts discarded) (S rightOrdinal)
        (advanceSurvivingRegistrationIndex @{nameEq} rightOrdinal child parent component rightIndex)
        left rest leftFinalIndex rightFinalIndex tail noUnload

||| An accepted complete left scan beginning at the empty index has no
||| discarded births if its actual word has no Unload. This is the native
||| discarded-list invariant specialized to the accepted scan, not a fixture.
export
0 o20AcceptedNoUnloadDiscardedEmpty :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  (left : Transitions leftFirst leftFinal) -> (right : Transitions rightFirst rightFinal) ->
  (mapping : RegistrationGenerationBijection name) ->
  (registrations : RegistrationCorrespondenceByGeneration nameEq mapping left right) ->
  ((actor : name) -> (ActionOccurs (LUnload actor) left -> Void)) ->
  (leftDeletedGenerations registrations = [])
o20AcceptedNoUnloadDiscardedEmpty name key world error value nameEq left right mapping registrations noUnload =
  o20NoUnloadDiscardedScan name key world error value nameEq mapping Z emptyRegistrationIndex Z emptyRegistrationIndex
    left right (leftFinalIndex registrations) (rightFinalIndex registrations)
    (generationTraceCorrespondence registrations) noUnload
