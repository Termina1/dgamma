module DGamma.CP4DeletionSuffixFold

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionBoundaryDeleted
import DGamma.CP4DeletionBoundaryPlan
import DGamma.CP4DeletionBoundaryRetained
import DGamma.CP4DeletionFilterSuccess
import DGamma.CP4DeletionGenerationFilter
import DGamma.CP4DeletionNoEpisodeReplay
import Data.Nat
import Decidable.Equality

%default total

||| Simultaneous whole-suffix result: generation scanning, executable-filter
||| readiness, and the final complete replay boundary are constructed by one
||| induction, so the endpoint boundary cannot drift from the replayed trace.
public export
record NoEpisodeSuffixReplayFold
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (registered : List (RegistrationGeneration name))
  (ordinal : Nat) (live : GenerationEnvironment name)
  {originalFirst, originalFinal : SystemState name key value world error}
  (original : Transitions originalFirst originalFinal)
  (survivingFirst : SystemState name key value world error) where
  constructor MkNoEpisodeSuffixReplayFold
  suffixFinalOrdinal : Nat
  suffixFinalLive : GenerationEnvironment name
  suffixFinalSurvivor : SystemState name key value world error
  0 suffixGenerationScan : GenerationTraceScan nameEq ordinal live original
    suffixFinalOrdinal suffixFinalLive
  0 suffixReplayReady : GenerationReplayReady nameEq keyEq
    (GenerationOwnedActor nameEq registered) ordinal live original survivingFirst
  0 suffixFinalBoundary : NoEpisodeReplayBoundary name key world error value
    nameEq keyEq registered suffixFinalLive originalFinal suffixFinalSurvivor

||| Structural whole-suffix fold for the no-selected-episode segment. Deleted
||| heads update only the original boundary; retained heads replay exactly on the
||| survivor and thread the resulting boundary.  All eight retained action forms
||| and the exhaustive deleted-head theorem are consumed here.
public export
0 noEpisodeSuffixReplayFold :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  RegisteredGenerationsBornBefore registered ordinal ->
  (original : Transitions originalFirst originalFinal) ->
  (survivingFirst : SystemState name key value world error) ->
  NoEpisodeReplayBoundary name key world error value nameEq keyEq registered live
    originalFirst survivingFirst ->
  RegistrationDiscipline protocol nameEq original ->
  AlignedTransitions name key world error value nameEq keyEq original ->
  NoRegisteredEpisode nameEq registered ordinal live original ->
  NoEpisodeSuffixReplayFold name key world error value nameEq keyEq registered
    ordinal live original survivingFirst
noEpisodeSuffixReplayFold protocol nameEq keyEq registered ordinal live
  bornBefore NoTransitions survivingFirst boundary RegistrationDisciplineEnd
  AlignedEnd NoRegisteredEpisodeEnd =
    MkNoEpisodeSuffixReplayFold ordinal live survivingFirst
      GenerationTraceScanEnd ReplayReadyEnd boundary
noEpisodeSuffixReplayFold protocol nameEq keyEq registered ordinal live
  bornBefore
  (MoreTransitions (Fired nameEq keyEq action tag checked) rest)
  survivingFirst boundary
  (RegistrationDisciplineStep
    (Fired nameEq keyEq action tag checked) rest stepDiscipline restDiscipline)
  (AlignedStep action tag checked rest alignedRest)
  (NoRegisteredEpisodeStep
    (Fired nameEq keyEq action tag checked) rest noBegin noRegisteredRest)
  with (decGenerationOwnedActor nameEq registered ordinal live action)
  noEpisodeSuffixReplayFold protocol nameEq keyEq registered ordinal live
    bornBefore
    (MoreTransitions (Fired nameEq keyEq action tag checked) rest)
    survivingFirst boundary
    (RegistrationDisciplineStep
      (Fired nameEq keyEq action tag checked) rest stepDiscipline restDiscipline)
    (AlignedStep action tag checked rest alignedRest)
    (NoRegisteredEpisodeStep
      (Fired nameEq keyEq action tag checked) rest noBegin noRegisteredRest) |
    Yes deleted =
      let 0 nextBoundary = deletedSuffixHeadPreservesNoEpisodeBoundary nameEq
            keyEq registered ordinal live bornBefore action _ survivingFirst
            boundary tag checked deleted noBegin
          0 folded = noEpisodeSuffixReplayFold protocol nameEq keyEq registered
            (S ordinal)
            (advanceGenerationEnvironment @{nameEq} ordinal action live)
            (registeredGenerationsBornBeforeNext bornBefore) rest survivingFirst
            nextBoundary restDiscipline alignedRest noRegisteredRest
      in MkNoEpisodeSuffixReplayFold (suffixFinalOrdinal folded)
        (suffixFinalLive folded) (suffixFinalSurvivor folded)
        (GenerationTraceScanStep
          (Fired nameEq keyEq action tag checked) rest
          (suffixGenerationScan folded))
        (ReplayReadyDelete deleted (suffixReplayReady folded))
        (suffixFinalBoundary folded)
  noEpisodeSuffixReplayFold protocol nameEq keyEq registered ordinal live
    bornBefore
    (MoreTransitions (Fired nameEq keyEq action tag checked) rest)
    survivingFirst boundary
    (RegistrationDisciplineStep
      (Fired nameEq keyEq action tag checked) rest stepDiscipline restDiscipline)
    (AlignedStep action tag checked rest alignedRest)
    (NoRegisteredEpisodeStep
      (Fired nameEq keyEq action tag checked) rest noBegin noRegisteredRest) |
    No retained =
      case retainedSuffixHeadPreservesNoEpisodeBoundary protocol nameEq keyEq
        registered ordinal live action _ survivingFirst boundary tag checked rest
        stepDiscipline retained of
        MkRetainedNoEpisodeBoundaryStep
          named@(MkNamedTransition survivingAfter survivingTag
            survivingTransition sameAction) fired tagSame nextBoundary =>
              let 0 folded = noEpisodeSuffixReplayFold protocol nameEq keyEq
                    registered (S ordinal)
                    (advanceGenerationEnvironment @{nameEq} ordinal action live)
                    (registeredGenerationsBornBeforeNext bornBefore) rest
                    survivingAfter nextBoundary restDiscipline alignedRest
                    noRegisteredRest
              in MkNoEpisodeSuffixReplayFold (suffixFinalOrdinal folded)
                (suffixFinalLive folded) (suffixFinalSurvivor folded)
                (GenerationTraceScanStep
                  (Fired nameEq keyEq action tag checked) rest
                  (suffixGenerationScan folded))
                (ReplayReadyKeep retained survivingAfter survivingTag
                  survivingTransition sameAction fired
                  (suffixReplayReady folded))
                (suffixFinalBoundary folded)
