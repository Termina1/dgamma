module DGamma.CP4DeletionSelectedEpisodeFoldCore

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionEmptyTableInvariant
import DGamma.CP4DeletionFilterSuccess
import DGamma.CP4DeletionGenerationFilter
import DGamma.CP4DeletionGenerationStamped
import DGamma.CP4DeletionGenerationUnique
import DGamma.CP4DeletionInactiveInvariant
import DGamma.CP4DeletionIndependenceRestriction
import DGamma.CP4DeletionPlanBuilder
import DGamma.CP4DeletionPlanComplete
import DGamma.CP4DeletionPlanEffects
import DGamma.CP4DeletionPlanEmpty
import DGamma.CP4DeletionSelectedBoundary
import DGamma.CP4RecoveryModelTrace
import Data.List.Elem
import Decidable.Equality

%default total

||| One retained head in the selected-episode quotient.  The named transition
||| is the concrete executable replay consumed by `GenerationReplayReady`; the
||| boundary is already advanced across the original head and the replayed
||| survivor head.
public export
record SelectedEpisodeRetainedHead
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (selected : name)
  (registered : List (RegistrationGeneration name))
  (ordinal : Nat) (live : GenerationEnvironment name)
  {wholeFirst, wholeLast : SystemState name key value world error}
  (whole : Transitions wholeFirst wholeLast)
  (action : Action name key value world error)
  (originalAfter, survivorBefore : SystemState name key value world error) where
  constructor MkSelectedEpisodeRetainedHead
  selectedHeadNamed : NamedTransition name key world error value action
    survivorBefore
  0 selectedHeadFires : fireNamed nameEq keyEq action survivorBefore =
    Just selectedHeadNamed
  0 selectedHeadBoundary : SelectedEpisodeReplayBoundary name key world error
    value nameEq keyEq selected registered (S ordinal)
    (advanceGenerationEnvironment @{nameEq} ordinal action live) whole
    originalAfter (namedAfter selectedHeadNamed)

||| Saturated per-head interface for the structural selected-episode fold.
||| The concrete implementation dispatches to the already checked selected
||| lifecycle, selected O-Retire, deleted-R orchestration, and retained foreign
||| orchestration/lifecycle modules.  Occurrence identity is retained so the
||| foreign lifecycle implementation can reconstruct its provider anchor.
public export
record SelectedEpisodeLocalReplayer
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (selected : name)
  (registered : List (RegistrationGeneration name))
  (protocol : RegistrationProtocol key value world error)
  {wholeFirst, wholeLast : SystemState name key value world error}
  (whole : Transitions wholeFirst wholeLast) where
  constructor MkSelectedEpisodeLocalReplayer
  0 replayDeletedEpisodeHead :
    (ordinal : Nat) -> (live : GenerationEnvironment name) ->
    GenerationEnvironmentNamesUnique live ->
    GenerationEnvironmentStamped live ->
    ((generation : RegistrationGeneration name) -> Elem generation registered ->
      Not (generationName generation = selected)) ->
    (action : Action name key value world error) ->
    (before, afterState, survivor : SystemState name key value world error) ->
    (tag : RuleTag) ->
    (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
      Just (tag, afterState)) ->
    installedAt @{nameEq} selected before = True ->
    installedAt @{nameEq} selected afterState = True ->
    {restFinal : SystemState name key value world error} ->
    (rest : Transitions afterState restFinal) ->
    RegistrationStepDiscipline protocol nameEq action before rest ->
    (noBegin : IsBeginAction action ->
      GenerationOwnedActor nameEq registered ordinal live action -> Void) ->
    (occurs : OccursIn
      (Fired {before = before} {afterState = afterState}
        nameEq keyEq action tag checked) whole) ->
    (boundary : SelectedEpisodeReplayBoundary name key world error value nameEq
      keyEq selected registered ordinal live whole before survivor) ->
    EmptyTableInactivePlan name key world error value nameEq
      (inactiveLeafPlan (completePlanResult
        (selectedBoundaryPlan boundary))) ->
    CurrentRegisteredInactiveFibers name key world error value nameEq registered
      live before ->
    EpisodeGenerationDeletedActor nameEq selected registered ordinal live
      action ->
    SelectedEpisodeReplayBoundary name key world error value nameEq keyEq
      selected registered (S ordinal)
      (advanceGenerationEnvironment @{nameEq} ordinal action live) whole
      afterState survivor
  0 replayRetainedEpisodeHead :
    (ordinal : Nat) -> (live : GenerationEnvironment name) ->
    GenerationEnvironmentNamesUnique live ->
    GenerationEnvironmentStamped live ->
    ((generation : RegistrationGeneration name) -> Elem generation registered ->
      Not (generationName generation = selected)) ->
    (action : Action name key value world error) ->
    (before, afterState, survivor : SystemState name key value world error) ->
    (tag : RuleTag) ->
    (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
      Just (tag, afterState)) ->
    installedAt @{nameEq} selected before = True ->
    installedAt @{nameEq} selected afterState = True ->
    {restFinal : SystemState name key value world error} ->
    (rest : Transitions afterState restFinal) ->
    RegistrationStepDiscipline protocol nameEq action before rest ->
    (noBegin : IsBeginAction action ->
      GenerationOwnedActor nameEq registered ordinal live action -> Void) ->
    (occurs : OccursIn
      (Fired {before = before} {afterState = afterState}
        nameEq keyEq action tag checked) whole) ->
    (boundary : SelectedEpisodeReplayBoundary name key world error value nameEq
      keyEq selected registered ordinal live whole before survivor) ->
    EmptyTableInactivePlan name key world error value nameEq
      (inactiveLeafPlan (completePlanResult
        (selectedBoundaryPlan boundary))) ->
    CurrentRegisteredInactiveFibers name key world error value nameEq registered
      live before ->
    Not (EpisodeGenerationDeletedActor nameEq selected registered ordinal live
      action) ->
    SelectedEpisodeRetainedHead name key world error value nameEq keyEq selected
      registered ordinal live whole action afterState survivor

||| Simultaneous result of the selected interior fold.  Besides executable
||| readiness it retains every scanner/control invariant needed by the closing
||| L-Unload package, avoiding a second proof traversal of the episode.
public export
record SelectedEpisodeInteriorFold
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (selected : name)
  (registered : List (RegistrationGeneration name))
  (ordinal : Nat) (live : GenerationEnvironment name)
  {wholeFirst, wholeLast, originalFirst, originalFinal :
    SystemState name key value world error}
  (whole : Transitions wholeFirst wholeLast)
  (original : Transitions originalFirst originalFinal)
  (survivorFirst : SystemState name key value world error) where
  constructor MkSelectedEpisodeInteriorFold
  interiorFinalOrdinal : Nat
  interiorFinalLive : GenerationEnvironment name
  interiorFinalSurvivor : SystemState name key value world error
  0 interiorScan : GenerationTraceScan nameEq ordinal live original
    interiorFinalOrdinal interiorFinalLive
  0 interiorReady : GenerationReplayReady nameEq keyEq
    (EpisodeGenerationDeletedActor nameEq selected registered)
    ordinal live original survivorFirst
  0 interiorBoundary : SelectedEpisodeReplayBoundary name key world error value
    nameEq keyEq selected registered interiorFinalOrdinal interiorFinalLive whole
    originalFinal interiorFinalSurvivor

0 nextPlanEmptyFromCurrent :
  (nameEq : DecEq name) ->
  (registered : List (RegistrationGeneration name)) ->
  (live : GenerationEnvironment name) ->
  GenerationEnvironmentNamesUnique live ->
  (state : SystemState name key value world error) ->
  (plan : CompleteCurrentRegisteredPlanResult name key world error value nameEq
    registered live (registry state)) ->
  CurrentRegisteredEmptyTables name key world error value nameEq registered live
    state ->
  EmptyTableInactivePlan name key world error value nameEq
    (inactiveLeafPlan (completePlanResult plan))
nextPlanEmptyFromCurrent nameEq registered live unique state plan empty =
  completeCurrentRegisteredPlanHasEmptyTables nameEq registered live unique
    (worldState state) (registry state) plan empty

||| Generic simultaneous induction over the selected episode interior.  The
||| occurrence embedding keeps every local head tied to the immutable whole
||| suffix used by Definition-60 recovery.
public export
0 selectedEpisodeInteriorFold :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  ((generation : RegistrationGeneration name) -> Elem generation registered ->
    Not (generationName generation = selected)) ->
  (whole : Transitions wholeFirst wholeLast) ->
  (local : SelectedEpisodeLocalReplayer name key world error value nameEq keyEq
    selected registered protocol whole) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  GenerationEnvironmentNamesUnique live ->
  GenerationEnvironmentStamped live ->
  (original : Transitions originalFirst originalFinal) ->
  (aligned : AlignedTransitions name key world error value nameEq keyEq
    original) ->
  (installed : InstalledTrace name key world error value nameEq keyEq selected
    original) ->
  (discipline : RegistrationDiscipline protocol nameEq original) ->
  (noRegistered : NoRegisteredEpisode nameEq registered ordinal live original) ->
  (embed : OccurrenceEmbedding original whole) ->
  (survivorFirst : SystemState name key value world error) ->
  (boundary : SelectedEpisodeReplayBoundary name key world error value nameEq
    keyEq selected registered ordinal live whole originalFirst survivorFirst) ->
  CurrentRegisteredInactiveFibers name key world error value nameEq registered
    live originalFirst ->
  CurrentRegisteredEmptyTables name key world error value nameEq registered live
    originalFirst ->
  EmptyTableInactivePlan name key world error value nameEq
    (inactiveLeafPlan (completePlanResult
      (selectedBoundaryPlan boundary))) ->
  SelectedEpisodeInteriorFold name key world error value nameEq keyEq selected
    registered ordinal live whole original survivorFirst
selectedEpisodeInteriorFold protocol nameEq keyEq selected registered
  selectedOutside whole local ordinal live unique stamped NoTransitions
  AlignedEnd (InstalledEnd installedEnd) RegistrationDisciplineEnd
  NoRegisteredEpisodeEnd embed survivorFirst
  boundary inactive empty emptyPlan =
    MkSelectedEpisodeInteriorFold ordinal live survivorFirst
      GenerationTraceScanEnd ReplayReadyEnd boundary
selectedEpisodeInteriorFold protocol nameEq keyEq selected registered
  selectedOutside whole local ordinal live unique stamped
  (MoreTransitions (Fired nameEq keyEq action tag checked) rest)
  (AlignedStep action tag checked rest alignedRest)
  (InstalledStep action tag checked rest sourceInstalled installedRest)
  (RegistrationDisciplineStep
    (Fired nameEq keyEq action tag checked) rest stepDiscipline restDiscipline)
  (NoRegisteredEpisodeStep
    (Fired nameEq keyEq action tag checked) rest noBegin noRegisteredRest)
  embed survivorFirst boundary inactive empty emptyPlan
  with (decEpisodeGenerationDeletedActor nameEq selected registered ordinal live
    action)
  selectedEpisodeInteriorFold protocol nameEq keyEq selected registered
    selectedOutside whole local ordinal live unique stamped
    (MoreTransitions (Fired nameEq keyEq action tag checked) rest)
    (AlignedStep action tag checked rest alignedRest)
    (InstalledStep action tag checked rest sourceInstalled installedRest)
    (RegistrationDisciplineStep
      (Fired nameEq keyEq action tag checked) rest stepDiscipline restDiscipline)
    (NoRegisteredEpisodeStep
      (Fired nameEq keyEq action tag checked) rest noBegin noRegisteredRest)
    embed survivorFirst boundary inactive empty emptyPlan | Yes deleted =
      let 0 raw = checkedActionProjects nameEq keyEq action _ _ tag checked
          0 nextUnique = advanceGenerationEnvironmentPreservesUnique nameEq
            ordinal action live unique
          0 nextStamped = advanceGenerationEnvironmentPreservesStamped nameEq
            ordinal action live stamped
          0 nextInactive = currentRegisteredInactiveStep nameEq keyEq registered
            ordinal live unique action _ _ tag raw noBegin inactive
          0 nextEmpty = currentRegisteredEmptyTableStep nameEq keyEq registered
            ordinal live unique action _ _ tag raw noBegin inactive empty
          0 occurs = embed (Fired nameEq keyEq action tag checked) OccursHere
          0 nextBoundary = replayDeletedEpisodeHead local ordinal live unique
            stamped selectedOutside action _ _ survivorFirst tag checked
            sourceInstalled (installedTraceStart installedRest) rest
            stepDiscipline noBegin occurs boundary emptyPlan inactive deleted
          0 nextEmptyPlan : EmptyTableInactivePlan name key world error value
            nameEq (inactiveLeafPlan (completePlanResult
              (selectedBoundaryPlan nextBoundary)))
          nextEmptyPlan = nextPlanEmptyFromCurrent nameEq registered
            (advanceGenerationEnvironment @{nameEq} ordinal action live)
            nextUnique _ (selectedBoundaryPlan nextBoundary) nextEmpty
          0 tailEmbed : OccurrenceEmbedding rest whole
          tailEmbed later occursLater = embed later (OccursLater occursLater)
          0 folded : SelectedEpisodeInteriorFold name key world error value
            nameEq keyEq selected registered (S ordinal)
            (advanceGenerationEnvironment @{nameEq} ordinal action live) whole
            rest survivorFirst
          folded = selectedEpisodeInteriorFold protocol nameEq keyEq selected
            registered selectedOutside whole local (S ordinal)
            (advanceGenerationEnvironment @{nameEq} ordinal action live)
            nextUnique nextStamped rest alignedRest installedRest restDiscipline
            noRegisteredRest tailEmbed survivorFirst nextBoundary nextInactive
            nextEmpty nextEmptyPlan
      in MkSelectedEpisodeInteriorFold
        (interiorFinalOrdinal folded) (interiorFinalLive folded)
        (interiorFinalSurvivor folded)
        (GenerationTraceScanStep (Fired nameEq keyEq action tag checked) rest (interiorScan folded))
        (ReplayReadyDelete deleted (interiorReady folded))
        (interiorBoundary folded)
  selectedEpisodeInteriorFold protocol nameEq keyEq selected registered
    selectedOutside whole local ordinal live unique stamped
    (MoreTransitions (Fired nameEq keyEq action tag checked) rest)
    (AlignedStep action tag checked rest alignedRest)
    (InstalledStep action tag checked rest sourceInstalled installedRest)
    (RegistrationDisciplineStep
      (Fired nameEq keyEq action tag checked) rest stepDiscipline restDiscipline)
    (NoRegisteredEpisodeStep
      (Fired nameEq keyEq action tag checked) rest noBegin noRegisteredRest)
    embed survivorFirst boundary inactive empty emptyPlan | No retained =
      let 0 raw = checkedActionProjects nameEq keyEq action _ _ tag checked
          0 nextUnique = advanceGenerationEnvironmentPreservesUnique nameEq
            ordinal action live unique
          0 nextStamped = advanceGenerationEnvironmentPreservesStamped nameEq
            ordinal action live stamped
          0 nextInactive = currentRegisteredInactiveStep nameEq keyEq registered
            ordinal live unique action _ _ tag raw noBegin inactive
          0 nextEmpty = currentRegisteredEmptyTableStep nameEq keyEq registered
            ordinal live unique action _ _ tag raw noBegin inactive empty
          0 occurs = embed (Fired nameEq keyEq action tag checked) OccursHere
          replay = replayRetainedEpisodeHead local ordinal live unique stamped
            selectedOutside action _ _ survivorFirst tag checked
            sourceInstalled (installedTraceStart installedRest) rest
            stepDiscipline noBegin occurs boundary emptyPlan inactive retained
      in case replay of
        MkSelectedEpisodeRetainedHead
          named@(MkNamedTransition namedAfter namedTag namedTransition sameAction)
          fired nextBoundary =>
          let 0 nextEmptyPlan : EmptyTableInactivePlan name key world error
                value nameEq (inactiveLeafPlan (completePlanResult
                  (selectedBoundaryPlan nextBoundary)))
              nextEmptyPlan = nextPlanEmptyFromCurrent nameEq registered
                (advanceGenerationEnvironment @{nameEq} ordinal action live)
                nextUnique _ (selectedBoundaryPlan nextBoundary) nextEmpty
              0 tailEmbed : OccurrenceEmbedding rest whole
              tailEmbed later occursLater = embed later (OccursLater occursLater)
              0 folded : SelectedEpisodeInteriorFold name key world error value
                nameEq keyEq selected registered (S ordinal)
                (advanceGenerationEnvironment @{nameEq} ordinal action live)
                whole rest namedAfter
              folded = selectedEpisodeInteriorFold protocol nameEq keyEq
                selected registered selectedOutside whole local (S ordinal)
                (advanceGenerationEnvironment @{nameEq} ordinal action live)
                nextUnique nextStamped rest alignedRest installedRest restDiscipline
                noRegisteredRest tailEmbed namedAfter nextBoundary
                nextInactive nextEmpty nextEmptyPlan
          in MkSelectedEpisodeInteriorFold
            (interiorFinalOrdinal folded) (interiorFinalLive folded)
            (interiorFinalSurvivor folded)
            (GenerationTraceScanStep (Fired nameEq keyEq action tag checked) rest (interiorScan folded))
            (ReplayReadyKeep retained namedAfter namedTag namedTransition
              sameAction fired
              (interiorReady folded))
            (interiorBoundary folded)
