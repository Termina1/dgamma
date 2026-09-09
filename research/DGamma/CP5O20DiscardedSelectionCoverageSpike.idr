module DGamma.CP5O20DiscardedSelectionCoverageSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorClassify
import DGamma.CP5RetirementHistorySpike
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

||| A checked Unload at an authentic split supplies a located closed episode.
||| Eliminate only its observed native tag equation; the installed anchor and
||| first-close result are built at this very edge, not independently replayed.
export
0 o20ClosingFreeRejectsUnloadSplit :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {initial, before, afterState, finalState : SystemState name key value world error} ->
  (global : Transitions initial finalState) -> (earlier : Transitions initial before) ->
  (tag : RuleTag) ->
  (checked : (checkedApplyAction @{nameEq} @{keyEq} (LUnload selected) before = Just (tag, afterState))) ->
  (later : Transitions afterState finalState) ->
  (appendTransitions earlier (MoreTransitions (Fired {before} {afterState} nameEq keyEq (LUnload selected) tag checked) later) = global) ->
  AlignedTransitions name key world error value nameEq keyEq global ->
  (bindings (registry initial) = []) ->
  NoClosingEpisodes name key world error value nameEq keyEq global ->
  (tag = LUnloadTag) -> Void
o20ClosingFreeRejectsUnloadSplit name key world error value nameEq keyEq selected
  {before} {afterState} global earlier _ checked later decomposition aligned empty noClosing Refl =
    noClosing selected
      (closingOccurrenceGivesLocatedEpisode nameEq keyEq selected
        (Fired {before} {afterState} nameEq keyEq (LUnload selected) LUnloadTag checked)
        global aligned empty
        (MkForeignLifecycleInstalledAnchor before earlier
          (MoreTransitions (Fired {before} {afterState} nameEq keyEq (LUnload selected) LUnloadTag checked) later)
          (fst (snd (lUnloadBoundary nameEq keyEq selected before afterState LUnloadTag
            (checkedActionProjects nameEq keyEq (LUnload selected) before afterState LUnloadTag checked))))
          Refl decomposition)
        (MkFirstClosingResult before afterState NoTransitions
          (InstalledEnd (fst (snd (lUnloadBoundary nameEq keyEq selected before afterState LUnloadTag
            (checkedActionProjects nameEq keyEq (LUnload selected) before afterState LUnloadTag checked)))))
          (MkUnloadStep checked) later Refl))

||| The actual native action equation selects Unload. Its checked evaluator
||| supplies the tag equation used by the preceding closed-episode producer.
export
0 o20ClosingFreeRejectsCheckedAction :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {initial, before, afterState, finalState : SystemState name key value world error} ->
  (global : Transitions initial finalState) -> (earlier : Transitions initial before) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (checked : (checkedApplyAction @{nameEq} @{keyEq} action before = Just (tag, afterState))) ->
  (later : Transitions afterState finalState) ->
  (appendTransitions earlier (MoreTransitions (Fired {before} {afterState} nameEq keyEq action tag checked) later) = global) ->
  AlignedTransitions name key world error value nameEq keyEq global ->
  (bindings (registry initial) = []) ->
  NoClosingEpisodes name key world error value nameEq keyEq global ->
  (action = LUnload selected) -> Void
o20ClosingFreeRejectsCheckedAction name key world error value nameEq keyEq selected
  {before} {afterState} global earlier _ tag checked later decomposition aligned empty noClosing Refl =
    o20ClosingFreeRejectsUnloadSplit name key world error value nameEq keyEq selected
      global earlier tag checked later decomposition aligned empty noClosing
      (fst (lUnloadBoundary nameEq keyEq selected before afterState tag
        (checkedActionProjects nameEq keyEq (LUnload selected) before afterState tag checked)))

||| Alignment at the actual split exposes its native checked dictionary and
||| action. Only this aligned head is eliminated; the source trace is fixed.
export
0 o20ClosingFreeRejectsAlignedUnload :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {initial, before, afterState, finalState : SystemState name key value world error} ->
  (global : Transitions initial finalState) -> (earlier : Transitions initial before) ->
  (step : Transition before afterState) -> (later : Transitions afterState finalState) ->
  (appendTransitions earlier (MoreTransitions step later) = global) ->
  AlignedTransitions name key world error value nameEq keyEq global ->
  (bindings (registry initial) = []) ->
  NoClosingEpisodes name key world error value nameEq keyEq global ->
  (transitionAction step = LUnload selected) ->
  AlignedTransitions name key world error value nameEq keyEq (MoreTransitions step later) -> Void
o20ClosingFreeRejectsAlignedUnload name key world error value nameEq keyEq selected
  global earlier _ _ decomposition aligned empty noClosing actionExact
  (AlignedStep action tag checked rest alignedRest) =
    o20ClosingFreeRejectsCheckedAction name key world error value nameEq keyEq selected
      global earlier action tag checked rest decomposition aligned empty noClosing actionExact

||| Every actual located Unload contradicts closing-freeness of an aligned
||| empty-origin trace. The occurrence owns the split used to obtain alignment.
export
0 o20ClosingFreeRejectsLocatedUnload :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (global : Transitions initial finalState) ->
  AlignedTransitions name key world error value nameEq keyEq global ->
  (bindings (registry initial) = []) ->
  NoClosingEpisodes name key world error value nameEq keyEq global ->
  (selected : name) -> LocatedActionOccurrence (LUnload selected) global -> Void
o20ClosingFreeRejectsLocatedUnload name key world error value nameEq keyEq global aligned empty noClosing selected occurrence =
  o20ClosingFreeRejectsAlignedUnload name key world error value nameEq keyEq selected
    global (beforeActionOccurrence occurrence) (locatedTransition occurrence) (afterActionOccurrence occurrence)
    (actionOccurrenceDecomposition occurrence) aligned empty noClosing (locatedAction occurrence)
    (snd (alignedAppendSplit (beforeActionOccurrence occurrence)
      (MoreTransitions (locatedTransition occurrence) (afterActionOccurrence occurrence))
      (replace {p = AlignedTransitions name key world error value nameEq keyEq}
        (sym (actionOccurrenceDecomposition occurrence)) aligned)))
