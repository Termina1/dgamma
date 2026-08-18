module DGamma.CP4DeletionFilterSuccess

import DGamma.Calculus
import DGamma.CP3
import DGamma.CP4DeletionGenerationFilter
import Decidable.Equality

%default total

||| Exact replay-readiness evidence consumed by the executable dependent
||| generation filter. Deleted actions need no smaller-state transition; every
||| retained action supplies the actual `fireNamed` success at the current
||| survivor and readiness for the resulting tail.
public export
data GenerationReplayReady :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (deletable : Nat -> GenerationEnvironment name ->
    Action name key value world error -> Type) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  {originalFirst, originalFinal : SystemState name key value world error} ->
  Transitions originalFirst originalFinal ->
  (survivingFirst : SystemState name key value world error) -> Type where
  ReplayReadyEnd :
    GenerationReplayReady nameEq keyEq deletable ordinal live NoTransitions
      survivingFirst
  ReplayReadyDelete :
    {originalTransition : Transition originalFirst originalMiddle} ->
    {originalRest : Transitions originalMiddle originalFinal} ->
    deletable ordinal live (transitionAction originalTransition) ->
    GenerationReplayReady nameEq keyEq deletable (S ordinal)
      (advanceGenerationEnvironment @{nameEq} ordinal
        (transitionAction originalTransition) live)
      originalRest survivingFirst ->
    GenerationReplayReady nameEq keyEq deletable ordinal live
      (MoreTransitions originalTransition originalRest) survivingFirst
  ReplayReadyKeep :
    {originalTransition : Transition originalFirst originalMiddle} ->
    {originalRest : Transitions originalMiddle originalFinal} ->
    Not (deletable ordinal live (transitionAction originalTransition)) ->
    (survivingAfter : SystemState name key value world error) ->
    (survivingTag : RuleTag) ->
    (survivingTransition : Transition survivingFirst survivingAfter) ->
    (0 sameAction : transitionAction survivingTransition =
      transitionAction originalTransition) ->
    fireNamed nameEq keyEq (transitionAction originalTransition) survivingFirst =
      Just (MkNamedTransition survivingAfter survivingTag survivingTransition
        sameAction) ->
    GenerationReplayReady nameEq keyEq deletable (S ordinal)
      (advanceGenerationEnvironment @{nameEq} ordinal
        (transitionAction originalTransition) live)
      originalRest survivingAfter ->
    GenerationReplayReady nameEq keyEq deletable ordinal live
      (MoreTransitions originalTransition originalRest) survivingFirst

||| Existential success equation for the concrete filter, not merely a parallel
||| hand-built subsequence.
public export
record GenerationFilterSucceeded
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (deletable : Nat -> GenerationEnvironment name ->
    Action name key value world error -> Type)
  (decDeletable : (ordinal : Nat) -> (live : GenerationEnvironment name) ->
    (action : Action name key value world error) ->
    Dec (deletable ordinal live action))
  (ordinal : Nat) (live : GenerationEnvironment name)
  {originalFirst, originalFinal : SystemState name key value world error}
  (original : Transitions originalFirst originalFinal)
  (survivingFirst : SystemState name key value world error) where
  constructor MkGenerationFilterSucceeded
  succeededResult : GenerationFilterResult name key world error value nameEq
    deletable ordinal live original survivingFirst
  0 filterReturnedJust :
    filterGenerationActions nameEq keyEq deletable decDeletable ordinal live
      original survivingFirst = Just succeededResult

||| Replay readiness is exactly sufficient to turn the filter's `Maybe` into a
||| constructive `Just` result carrying its generated subsequence witness.
public export
0 generationReplayReadyGivesFilterSuccess :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {originalFirst, originalFinal : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (deletable : Nat -> GenerationEnvironment name ->
    Action name key value world error -> Type) ->
  (decDeletable : (ordinal : Nat) -> (live : GenerationEnvironment name) ->
    (action : Action name key value world error) ->
    Dec (deletable ordinal live action)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (original : Transitions originalFirst originalFinal) ->
  (survivingFirst : SystemState name key value world error) ->
  GenerationReplayReady nameEq keyEq deletable ordinal live original
    survivingFirst ->
  GenerationFilterSucceeded name key world error value nameEq keyEq deletable
    decDeletable ordinal live original survivingFirst
generationReplayReadyGivesFilterSuccess nameEq keyEq deletable decDeletable
  ordinal live NoTransitions survivingFirst ReplayReadyEnd =
    MkGenerationFilterSucceeded
      (MkGenerationFilterResult survivingFirst NoTransitions
        GenerationActionSubsequenceEnd) Refl
generationReplayReadyGivesFilterSuccess nameEq keyEq deletable decDeletable
  ordinal live
  (MoreTransitions (Fired stepNameEq stepKeyEq action tag checked) originalRest)
  survivingFirst (ReplayReadyDelete deleted readyTail)
  with (decDeletable ordinal live action) proof decision
  generationReplayReadyGivesFilterSuccess nameEq keyEq deletable decDeletable
    ordinal live
    (MoreTransitions (Fired stepNameEq stepKeyEq action tag checked) originalRest)
    survivingFirst (ReplayReadyDelete deleted readyTail) | Yes actual =
      case generationReplayReadyGivesFilterSuccess nameEq keyEq deletable
        decDeletable (S ordinal)
        (advanceGenerationEnvironment @{nameEq} ordinal action live)
        originalRest survivingFirst readyTail of
        MkGenerationFilterSucceeded
          (MkGenerationFilterResult finalState survivor tailWitness)
          tailEquation =>
          MkGenerationFilterSucceeded
            (MkGenerationFilterResult finalState survivor
              (DeleteGenerationAction
                (Fired stepNameEq stepKeyEq action tag checked) originalRest
                actual tailWitness))
            (rewrite decision in rewrite tailEquation in Refl)
  generationReplayReadyGivesFilterSuccess nameEq keyEq deletable decDeletable
    ordinal live
    (MoreTransitions (Fired stepNameEq stepKeyEq action tag checked) originalRest)
    survivingFirst (ReplayReadyDelete deleted readyTail) | No notDeleted =
      void (notDeleted deleted)
generationReplayReadyGivesFilterSuccess nameEq keyEq deletable decDeletable
  ordinal live
  (MoreTransitions (Fired stepNameEq stepKeyEq action tag checked) originalRest)
  survivingFirst (ReplayReadyKeep kept survivingAfter survivingTag
    survivingTransition sameAction fired readyTail)
  with (decDeletable ordinal live action) proof decision
  generationReplayReadyGivesFilterSuccess nameEq keyEq deletable decDeletable
    ordinal live
    (MoreTransitions (Fired stepNameEq stepKeyEq action tag checked) originalRest)
    survivingFirst (ReplayReadyKeep kept survivingAfter survivingTag
      survivingTransition sameAction fired readyTail) | Yes deleted =
      void (kept deleted)
  generationReplayReadyGivesFilterSuccess nameEq keyEq deletable decDeletable
    ordinal live
    (MoreTransitions (Fired stepNameEq stepKeyEq action tag checked) originalRest)
    survivingFirst (ReplayReadyKeep kept survivingAfter survivingTag
      survivingTransition sameAction fired readyTail) | No notDeleted =
      case generationReplayReadyGivesFilterSuccess nameEq keyEq deletable
        decDeletable (S ordinal)
        (advanceGenerationEnvironment @{nameEq} ordinal action live)
        originalRest survivingAfter readyTail of
        MkGenerationFilterSucceeded
          (MkGenerationFilterResult finalState survivor tailWitness)
          tailEquation =>
          MkGenerationFilterSucceeded
            (MkGenerationFilterResult finalState
              (MoreTransitions survivingTransition survivor)
              (KeepGenerationAction
                (Fired stepNameEq stepKeyEq action tag checked) originalRest
                survivingTransition survivor notDeleted (sym sameAction)
                tailWitness))
            (rewrite decision in rewrite fired in
              rewrite tailEquation in Refl)

||| Exact selected-episode specialization: readiness rules out both `Nothing`
||| branches of `filterSelectedEpisode` and returns its concrete result.
public export
0 selectedEpisodeReplayReadyGivesFilterSuccess :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {originalFirst, originalFinal : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (original : Transitions originalFirst originalFinal) ->
  (survivingFirst : SystemState name key value world error) ->
  GenerationReplayReady nameEq keyEq
    (EpisodeGenerationDeletedActor nameEq selected registered)
    ordinal live original survivingFirst ->
  GenerationFilterSucceeded name key world error value nameEq keyEq
    (EpisodeGenerationDeletedActor nameEq selected registered)
    (decEpisodeGenerationDeletedActor nameEq selected registered)
    ordinal live original survivingFirst
selectedEpisodeReplayReadyGivesFilterSuccess nameEq keyEq selected registered
  ordinal live original survivingFirst ready =
    generationReplayReadyGivesFilterSuccess nameEq keyEq
      (EpisodeGenerationDeletedActor nameEq selected registered)
      (decEpisodeGenerationDeletedActor nameEq selected registered)
      ordinal live original survivingFirst ready

||| Exact suffix specialization for deletion of current/historical R action
||| occurrences.
public export
0 registeredGenerationReplayReadyGivesFilterSuccess :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {originalFirst, originalFinal : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (original : Transitions originalFirst originalFinal) ->
  (survivingFirst : SystemState name key value world error) ->
  GenerationReplayReady nameEq keyEq
    (GenerationOwnedActor nameEq registered)
    ordinal live original survivingFirst ->
  GenerationFilterSucceeded name key world error value nameEq keyEq
    (GenerationOwnedActor nameEq registered)
    (decGenerationOwnedActor nameEq registered)
    ordinal live original survivingFirst
registeredGenerationReplayReadyGivesFilterSuccess nameEq keyEq registered
  ordinal live original survivingFirst ready =
    generationReplayReadyGivesFilterSuccess nameEq keyEq
      (GenerationOwnedActor nameEq registered)
      (decGenerationOwnedActor nameEq registered)
      ordinal live original survivingFirst ready
