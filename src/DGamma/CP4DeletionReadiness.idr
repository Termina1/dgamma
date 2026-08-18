module DGamma.CP4DeletionReadiness

import DGamma.Calculus
import DGamma.CP3
import DGamma.CP4DeletionFilterSuccess
import DGamma.CP4DeletionGenerationFilter
import Decidable.Equality

%default total

||| One retained original head replayed at the survivor boundary.  The future
||| cross-boundary invariant has only to construct this local package; ordinal,
||| generation-environment, and survivor threading are handled by the generic
||| readiness induction below.
public export
record RetainedGenerationReplayStep
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {originalFirst, originalMiddle, originalFinal, survivingFirst :
    SystemState name key value world error}
  (originalTransition : Transition originalFirst originalMiddle)
  (originalRest : Transitions originalMiddle originalFinal) where
  constructor MkRetainedGenerationReplayStep
  replayedHead : NamedTransition name key world error value
    (transitionAction originalTransition) survivingFirst
  0 replayedHeadFires : fireNamed nameEq keyEq
    (transitionAction originalTransition) survivingFirst = Just replayedHead

||| Record-saturated interface expected from a replay-boundary invariant.
||| It is deliberately independent of the deletion predicate: the readiness
||| induction calls it only after obtaining `Not (deletable ...)`.
public export
GenerationRetainedReplay :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> Type
GenerationRetainedReplay name key world error value nameEq keyEq =
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  {originalFirst, originalMiddle, originalFinal, survivingFirst :
    SystemState name key value world error} ->
  (originalTransition : Transition originalFirst originalMiddle) ->
  (originalRest : Transitions originalMiddle originalFinal) ->
  RetainedGenerationReplayStep name key world error value nameEq keyEq
    originalTransition originalRest

||| Generic structural readiness induction.  Deletable heads leave the
||| survivor untouched; retained heads are supplied by the local replay
||| interface and determine the exact source of the recursive call.
public export
0 retainedReplayGivesGenerationReadiness :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {originalFirst, originalFinal : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (deletable : Nat -> GenerationEnvironment name ->
    Action name key value world error -> Type) ->
  (decDeletable : (ordinal : Nat) -> (live : GenerationEnvironment name) ->
    (action : Action name key value world error) ->
    Dec (deletable ordinal live action)) ->
  (replayRetained : GenerationRetainedReplay name key world error value
    nameEq keyEq) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (original : Transitions originalFirst originalFinal) ->
  (currentSurvivor : SystemState name key value world error) ->
  GenerationReplayReady nameEq keyEq deletable ordinal live original
    currentSurvivor
retainedReplayGivesGenerationReadiness nameEq keyEq deletable decDeletable
  replayRetained ordinal live NoTransitions currentSurvivor = ReplayReadyEnd
retainedReplayGivesGenerationReadiness nameEq keyEq deletable decDeletable
  replayRetained ordinal live
  (MoreTransitions originalTransition originalRest) currentSurvivor
  with (decDeletable ordinal live (transitionAction originalTransition))
  retainedReplayGivesGenerationReadiness nameEq keyEq deletable decDeletable
    replayRetained ordinal live
    (MoreTransitions originalTransition originalRest) currentSurvivor |
      Yes deleted =
        ReplayReadyDelete deleted
          (retainedReplayGivesGenerationReadiness nameEq keyEq deletable
            decDeletable replayRetained (S ordinal)
            (advanceGenerationEnvironment @{nameEq} ordinal
              (transitionAction originalTransition) live)
            originalRest currentSurvivor)
  retainedReplayGivesGenerationReadiness nameEq keyEq deletable decDeletable
    replayRetained ordinal live
    (MoreTransitions originalTransition originalRest) currentSurvivor |
      No retained =
        case replayRetained {survivingFirst = currentSurvivor} ordinal live
          originalTransition originalRest of
          MkRetainedGenerationReplayStep
            (MkNamedTransition survivingAfter survivingTag survivingTransition
              sameAction) fired =>
                ReplayReadyKeep retained survivingAfter survivingTag
                  survivingTransition sameAction fired
                  (retainedReplayGivesGenerationReadiness nameEq keyEq deletable
                    decDeletable replayRetained (S ordinal)
                    (advanceGenerationEnvironment @{nameEq} ordinal
                      (transitionAction originalTransition) live)
                    originalRest survivingAfter)

||| First of the two Lemma-72 specializations: selected lifecycle and exact R
||| generation actions are deleted from the located closed-episode segment.
public export
0 selectedEpisodeRetainedReplayGivesReadiness :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {originalFirst, originalFinal : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (replayRetained : GenerationRetainedReplay name key world error value
    nameEq keyEq) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (original : Transitions originalFirst originalFinal) ->
  (currentSurvivor : SystemState name key value world error) ->
  GenerationReplayReady nameEq keyEq
    (EpisodeGenerationDeletedActor nameEq selected registered)
    ordinal live original currentSurvivor
selectedEpisodeRetainedReplayGivesReadiness nameEq keyEq selected registered
  replayRetained ordinal live original currentSurvivor =
    retainedReplayGivesGenerationReadiness nameEq keyEq
      (EpisodeGenerationDeletedActor nameEq selected registered)
      (decEpisodeGenerationDeletedActor nameEq selected registered)
      replayRetained ordinal live original currentSurvivor

||| Second Lemma-72 specialization: exact R generation actions are deleted from
||| the suffix, while every later raw-name reissue is offered to the retained
||| replay interface.
public export
0 registeredGenerationRetainedReplayGivesReadiness :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {originalFirst, originalFinal : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (registered : List (RegistrationGeneration name)) ->
  (replayRetained : GenerationRetainedReplay name key world error value
    nameEq keyEq) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (original : Transitions originalFirst originalFinal) ->
  (currentSurvivor : SystemState name key value world error) ->
  GenerationReplayReady nameEq keyEq
    (GenerationOwnedActor nameEq registered)
    ordinal live original currentSurvivor
registeredGenerationRetainedReplayGivesReadiness nameEq keyEq registered
  replayRetained ordinal live original currentSurvivor =
    retainedReplayGivesGenerationReadiness nameEq keyEq
      (GenerationOwnedActor nameEq registered)
      (decGenerationOwnedActor nameEq registered)
      replayRetained ordinal live original currentSurvivor
