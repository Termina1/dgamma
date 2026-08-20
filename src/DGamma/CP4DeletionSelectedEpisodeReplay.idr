module DGamma.CP4DeletionSelectedEpisodeReplay

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionBoundaryDeleted
import DGamma.CP4DeletionBoundaryPlan
import DGamma.CP4DeletionBoundaryRetained
import DGamma.CP4DeletionControlPlan
import DGamma.CP4DeletionGenerationFilter
import DGamma.CP4DeletionGenerationStamped
import DGamma.CP4DeletionGenerationUnique
import DGamma.CP4DeletionInactiveInvariant
import DGamma.CP4DeletionIndependenceRestriction
import DGamma.CP4DeletionNoEpisodeReplay
import DGamma.CP4DeletionPlanBuilder
import DGamma.CP4DeletionPlanComplete
import DGamma.CP4DeletionPlanEffects
import DGamma.CP4DeletionRetainedAction
import DGamma.CP4DeletionSelectedBoundary
import DGamma.CP4DeletionSelectedDeletedDispatch
import DGamma.CP4DeletionSelectedDeletedOrchestration
import DGamma.CP4DeletionSelectedEpisodeFoldCore
import DGamma.CP4DeletionSelectedForeignLifecycleProviderFrame
import DGamma.CP4DeletionSelectedForeignLifecycleReplay
import DGamma.CP4DeletionSelectedForeignOrchestration
import DGamma.CP4DeletionSelectedForeignOrchestrationStep
import DGamma.CP4DeletionSelectedOwn
import DGamma.CP4DeletionSelectedOwnDispatch
import DGamma.CP4DeletionSelectedRetire
import DGamma.CP4RecoveryModelTrace
import DGamma.CP4RecoverySelectedStep
import Data.List.Elem
import Decidable.Equality

%default total

||| Occurrence-local trace classification required only by retained foreign
||| lifecycle heads.  The structural fold owns all scanner/control data; this
||| interface isolates the temporal provider-anchor reconstruction from the
||| action dispatcher without adding a premise to the public theorem.
public export
record SelectedEpisodeLifecycleAnchorProvider
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (selected : name)
  (registered : List (RegistrationGeneration name))
  {globalFirst, globalLast, selectedPre, selectedAfter :
    SystemState name key value world error}
  (global : Transitions globalFirst globalLast)
  (selectedEpisode : ClosedEpisode name key world error value nameEq keyEq
    selected selectedPre selectedAfter) where
  constructor MkSelectedEpisodeLifecycleAnchorProvider
  0 lifecycleAnchorAt :
    (ordinal : Nat) -> (live : GenerationEnvironment name) ->
    (action : Action name key value world error) ->
    (lifecycle : isLifecycleAction action = True) ->
    (distinct : Not (actionOwner action = selected)) ->
    (before, afterState : SystemState name key value world error) ->
    (tag : RuleTag) ->
    (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
      Just (tag, afterState)) ->
    (rest : Transitions afterState (lastInstalledState selectedEpisode)) ->
    InstalledTrace name key world error value nameEq keyEq selected rest ->
    (occurs : OccursIn
      (Fired {before = before} {afterState = afterState}
        nameEq keyEq action tag checked) global) ->
    {wholeFirst, wholeLast : SystemState name key value world error} ->
    {whole : Transitions wholeFirst wholeLast} ->
    {survivor : SystemState name key value world error} ->
    (boundary : SelectedEpisodeReplayBoundary name key world error value nameEq
      keyEq selected registered ordinal live whole before survivor) ->
    (leftSelected, leftOwner, rightOwner : Fiber name key value world error) ->
    lookupFiber @{nameEq} selected
      (planTarget (completePlanResult (selectedBoundaryPlan boundary))) =
      Just leftSelected ->
    lookupFiber @{nameEq} (actionOwner action)
      (planTarget (completePlanResult (selectedBoundaryPlan boundary))) =
      Just leftOwner ->
    lookupFiber @{nameEq} selected (registry before) = Just leftSelected ->
    lookupFiber @{nameEq} (actionOwner action) (registry before) =
      Just leftOwner ->
    lookupFiber @{nameEq} (actionOwner action) (registry survivor) =
      Just rightOwner ->
    FiberControlRelated leftOwner rightOwner ->
    ForeignLifecycleProviderFrameEvidence name key world error value nameEq keyEq
      global selected (actionOwner action)
      (MkSystemState (worldState before)
        (planTarget (completePlanResult (selectedBoundaryPlan boundary))))
      leftSelected leftOwner

0 selectedPlanExactBoundary :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  GenerationEnvironmentNamesUnique live ->
  (boundary : SelectedEpisodeReplayBoundary name key world error value nameEq
    keyEq selected registered ordinal live whole original survivor) ->
  NoEpisodeReplayBoundary name key world error value nameEq keyEq registered live
    original
    (MkSystemState (worldState original)
      (planTarget (completePlanResult (selectedBoundaryPlan boundary))))
selectedPlanExactBoundary nameEq keyEq unique boundary =
  let 0 plannedWellFormed = inactivePlanPreservesWellFormed nameEq keyEq
        (worldState original) (registry original)
        (planTarget (completePlanResult (selectedBoundaryPlan boundary)))
        (inactiveLeafPlan (completePlanResult
          (selectedBoundaryPlan boundary)))
        (selectedOriginalWellFormed boundary)
  in case original of
    MkSystemState ambient source =>
      MkNoEpisodeReplayBoundary ambient source Refl
        (selectedBoundaryPlan boundary) Refl Refl unique
        (selectedOriginalWellFormed boundary) plannedWellFormed

0 stateEtaEpisodeReplay : (state : SystemState name key value world error) ->
  MkSystemState (worldState state) (registry state) = state
stateEtaEpisodeReplay (MkSystemState ambient fibers) = Refl

0 retireViewTagReplay :
  RetireSuccessView name key world error value nameEq actor ambient source tag
    afterState -> tag = ORetireTag
retireViewTagReplay (MkRetireSuccessView fiber found) = Refl

0 selectedSourceOutsidePlan :
  (nameEq : DecEq name) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (live : GenerationEnvironment name) ->
  GenerationEnvironmentStamped live ->
  ((generation : RegistrationGeneration name) -> Elem generation registered ->
    Not (generationName generation = selected)) ->
  (boundary : SelectedEpisodeReplayBoundary name key world error value nameEq
    keyEq selected registered ordinal live whole original survivor) ->
  ActorOutsideDeletionPlan selected
    (inactiveLeafPlan (completePlanResult (selectedBoundaryPlan boundary)))
selectedSourceOutsidePlan nameEq selected registered live stamped outside
  boundary = selectedOutsideBoundaryPlan selected registered live stamped outside
    (selectedBoundaryPlan boundary)

0 insertAbsentNotInstalled :
  lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} actor source = Nothing ->
  installedAt @{nameEq} actor
    (the (SystemState name key value world error)
      (MkSystemState ambient source)) = True -> Void
insertAbsentNotInstalled {nameEq} {actor} {source} {ambient} absent installed
  with (lookupFiber @{nameEq} actor source)
  insertAbsentNotInstalled {nameEq} {actor} {source} {ambient} Refl Refl |
    Nothing impossible
  insertAbsentNotInstalled {nameEq} {actor} {source} {ambient} Refl installed |
    Just fiber impossible

0 lifecycleNonInsertReplay : (action : Action name key value world error) ->
  isLifecycleAction action = True -> NonInsertAction action
lifecycleNonInsertReplay (OInsert actor parent component) Refl impossible
lifecycleNonInsertReplay (ORetire actor) Refl impossible
lifecycleNonInsertReplay (ORemove actor) Refl impossible
lifecycleNonInsertReplay (LBegin actor) lifecycle = NonInsertBegin
lifecycleNonInsertReplay (LAdvance actor) lifecycle = NonInsertAdvance
lifecycleNonInsertReplay (LDivert actor) lifecycle = NonInsertDivert
lifecycleNonInsertReplay (LLeave actor) lifecycle = NonInsertLeave
lifecycleNonInsertReplay (LUnload actor) lifecycle = NonInsertUnload

0 registeredLifecycleImpossible :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (action : Action name key value world error) ->
  isLifecycleAction action = True ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  (noBegin : IsBeginAction action ->
    GenerationOwnedActor nameEq registered ordinal live action -> Void) ->
  CurrentRegisteredInactiveFibers name key world error value nameEq registered
    live before ->
  GenerationOwnedActor nameEq registered ordinal live action -> Void
registeredLifecycleImpossible nameEq keyEq registered ordinal live
  (OInsert actor parent component) Refl before afterState tag checked noBegin
  inactive owned impossible
registeredLifecycleImpossible nameEq keyEq registered ordinal live
  (ORetire actor) Refl before afterState tag checked noBegin inactive owned
  impossible
registeredLifecycleImpossible nameEq keyEq registered ordinal live
  (ORemove actor) Refl before afterState tag checked noBegin inactive owned
  impossible
registeredLifecycleImpossible nameEq keyEq registered ordinal live
  (LBegin actor) lifecycle before afterState tag checked noBegin inactive owned =
    noBegin ItIsLBegin owned
registeredLifecycleImpossible nameEq keyEq registered ordinal live
  (LAdvance actor) lifecycle before afterState tag checked noBegin inactive
  (generation ** (current, member)) =
    inactiveCannotAdvance nameEq keyEq actor before afterState tag
      (checkedActionProjects nameEq keyEq (LAdvance actor) before afterState tag
        checked)
      (inactive actor generation member current)
registeredLifecycleImpossible nameEq keyEq registered ordinal live
  (LDivert actor) lifecycle before afterState tag checked noBegin inactive
  (generation ** (current, member)) =
    inactiveCannotDivert nameEq keyEq actor before afterState tag
      (checkedActionProjects nameEq keyEq (LDivert actor) before afterState tag
        checked)
      (inactive actor generation member current)
registeredLifecycleImpossible nameEq keyEq registered ordinal live
  (LLeave actor) lifecycle before afterState tag checked noBegin inactive
  (generation ** (current, member)) =
    inactiveCannotLeave nameEq keyEq actor before afterState tag
      (checkedActionProjects nameEq keyEq (LLeave actor) before afterState tag
        checked)
      (inactive actor generation member current)
registeredLifecycleImpossible nameEq keyEq registered ordinal live
  (LUnload actor) lifecycle before afterState tag checked noBegin inactive
  (generation ** (current, member)) =
    inactiveCannotUnload nameEq keyEq actor before afterState tag
      (checkedActionProjects nameEq keyEq (LUnload actor) before afterState tag
        checked)
      (inactive actor generation member current)

record LocatedRegistrationStep
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name)
  {globalFirst, globalLast, stepBefore, stepAfter :
    SystemState name key value world error}
  (transition : Transition stepBefore stepAfter)
  (global : Transitions globalFirst globalLast) where
  constructor MkLocatedRegistrationStep
  registrationFuture : Transitions stepAfter globalLast
  0 registrationStepAtOccurrence : RegistrationStepDiscipline protocol nameEq
    (transitionAction transition) stepBefore registrationFuture

0 registrationDisciplineAtOccurrence :
  (transition : Transition stepBefore stepAfter) ->
  (global : Transitions globalFirst globalLast) ->
  RegistrationDiscipline protocol nameEq global ->
  OccursIn transition global ->
  LocatedRegistrationStep protocol nameEq transition global
registrationDisciplineAtOccurrence transition
  (MoreTransitions transition rest)
  (RegistrationDisciplineStep transition rest stepDiscipline tailDiscipline)
  OccursHere = MkLocatedRegistrationStep rest stepDiscipline
registrationDisciplineAtOccurrence wanted
  (MoreTransitions head rest)
  (RegistrationDisciplineStep head rest stepDiscipline tailDiscipline)
  (OccursLater later) = case registrationDisciplineAtOccurrence wanted rest
    tailDiscipline later of
    MkLocatedRegistrationStep future futureDiscipline =>
      MkLocatedRegistrationStep future futureDiscipline

||| Concrete per-head dispatcher used by the simultaneous fold.  Every action
||| branch delegates to an already checked local theorem; no evaluator is
||| duplicated here.
public export
0 selectedEpisodeLocalReplayer :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  ((generation : RegistrationGeneration name) -> Elem generation registered ->
    Not (generationName generation = selected)) ->
  (global : Transitions globalFirst globalLast) ->
  AlignedTransitions name key world error value nameEq keyEq global ->
  RegistrationDiscipline protocol nameEq global ->
  NoDependentClosingEpisode {nameEq = nameEq} {keyEq = keyEq} selected global ->
  TraceIndependent name key world error value keyEq global ->
  (whole : Transitions wholeFirst wholeLast) ->
  (selectedEpisode : ClosedEpisode name key world error value nameEq keyEq
    selected selectedPre selectedAfter) ->
  (wholeInGlobal : OccurrenceEmbedding whole global) ->
  SelectedEpisodeLifecycleAnchorProvider name key world error value nameEq keyEq
    selected registered global selectedEpisode ->
  SelectedEpisodeLocalReplayer name key world error value nameEq keyEq selected
    registered protocol whole (lastInstalledState selectedEpisode)
selectedEpisodeLocalReplayer {name} {key} {world} {error} {value}
  protocol nameEq keyEq selected registered
  selectedOutside global aligned globalDiscipline noDependent independent whole
  selectedEpisode wholeInGlobal
  anchors = MkSelectedEpisodeLocalReplayer replayDeleted replayRetained
  where
  0 replayDeleted :
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
  replayDeleted ordinal live unique stamped outside action before afterState
    survivor tag checked sourceInstalled targetInstalled rest noBegin
    occurs boundary oldEmpty inactive
    (DeleteEpisodeGenerationLifecycle owner lifecycle) = case action of
      OInsert actor parent component => case lifecycle of Refl impossible
      ORetire actor => case lifecycle of Refl impossible
      ORemove actor => case lifecycle of Refl impossible
      LBegin actor => case owner of
        Refl => deletedSelectedInstalledHeadPreservesEpisodeBoundary nameEq keyEq selected
          registered ordinal live stamped outside (LBegin selected) tag before
          afterState checked Refl Refl whole occurs targetInstalled survivor
          boundary
      LAdvance actor => case owner of
        Refl => deletedSelectedInstalledHeadPreservesEpisodeBoundary nameEq keyEq selected
          registered ordinal live stamped outside (LAdvance selected) tag before
          afterState checked Refl Refl whole occurs targetInstalled survivor
          boundary
      LDivert actor => case owner of
        Refl => deletedSelectedInstalledHeadPreservesEpisodeBoundary nameEq keyEq selected
          registered ordinal live stamped outside (LDivert selected) tag before
          afterState checked Refl Refl whole occurs targetInstalled survivor
          boundary
      LLeave actor => case owner of
        Refl => deletedSelectedInstalledHeadPreservesEpisodeBoundary nameEq keyEq selected
          registered ordinal live stamped outside (LLeave selected) tag before
          afterState checked Refl Refl whole occurs targetInstalled survivor
          boundary
      LUnload actor => case owner of
        Refl => deletedSelectedInstalledHeadPreservesEpisodeBoundary nameEq keyEq selected
          registered ordinal live stamped outside (LUnload selected) tag before
          afterState checked Refl Refl whole occurs targetInstalled survivor
          boundary
  replayDeleted ordinal live unique stamped outside action before afterState
    survivor tag checked sourceInstalled targetInstalled rest noBegin
    occurs boundary oldEmpty inactive (DeleteRegisteredGeneration owned)
    with (isLifecycleAction action) proof kind
    replayDeleted ordinal live unique stamped outside action before afterState
      survivor tag checked sourceInstalled targetInstalled rest noBegin
      occurs boundary oldEmpty inactive (DeleteRegisteredGeneration owned) |
      True = void (registeredLifecycleImpossible nameEq keyEq registered ordinal
        live action kind before afterState tag checked noBegin inactive owned)
    replayDeleted ordinal live unique stamped outside action before afterState
      survivor tag checked sourceInstalled targetInstalled rest noBegin
      occurs boundary oldEmpty inactive (DeleteRegisteredGeneration owned) |
      False = case registrationDisciplineAtOccurrence
        (Fired nameEq keyEq action tag checked) global globalDiscipline
        (wholeInGlobal (Fired nameEq keyEq action tag checked) occurs) of
        MkLocatedRegistrationStep future futureDiscipline => case
          deletedRegisteredOrchestrationHeadPreservesEpisodeBoundary protocol
            nameEq keyEq selected registered ordinal live unique stamped outside
            action kind before afterState tag checked future futureDiscipline
            whole survivor boundary oldEmpty owned of
          MkDeletedRegisteredEpisodeBoundaryStep nextBoundary nextEmpty =>
            nextBoundary

  0 replayRetained :
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
    (rest : Transitions afterState (lastInstalledState selectedEpisode)) ->
    InstalledTrace name key world error value nameEq keyEq selected rest ->
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
  replayRetained ordinal live unique stamped outside action before afterState
    survivor tag checked sourceInstalled targetInstalled rest selectedRest
    noBegin occurs boundary emptyPlan inactive retained =
      case decEq @{nameEq} (actionOwner action) selected of
        Yes ownerSelected => selectedCase ownerSelected
        No ownerDistinct => foreignCase ownerDistinct
    where
    exactStep :
      Not (GenerationOwnedActor nameEq registered ordinal live action) ->
      RetainedNoEpisodeBoundaryStep name key world error value nameEq keyEq
        registered
        (advanceGenerationEnvironment @{nameEq} ordinal action live)
        action tag afterState
        (MkSystemState (worldState before)
          (planTarget (completePlanResult
            (selectedBoundaryPlan boundary))))
    exactStep notOwned = case registrationDisciplineAtOccurrence
      (Fired nameEq keyEq action tag checked) global globalDiscipline
      (wholeInGlobal (Fired nameEq keyEq action tag checked) occurs) of
      MkLocatedRegistrationStep future futureDiscipline =>
        retainedSuffixHeadPreservesNoEpisodeBoundary protocol nameEq keyEq
          registered ordinal live action before
          (MkSystemState (worldState before)
            (planTarget (completePlanResult
              (selectedBoundaryPlan boundary))))
          (selectedPlanExactBoundary nameEq keyEq unique boundary) tag checked
          future futureDiscipline notOwned

    0 selectedCase :
      actionOwner action = selected ->
      SelectedEpisodeRetainedHead name key world error value nameEq keyEq
        selected registered ordinal live whole action afterState survivor
    selectedCase ownerSelected = case action of
      OInsert actor parent component => case ownerSelected of
        Refl =>
          let raw = checkedActionProjects nameEq keyEq
                (OInsert selected parent component) before afterState tag checked
          in case before of
            MkSystemState ambient source =>
              case foreignInsertPlanView nameEq keyEq selected parent component
                ambient source tag afterState raw of
                MkForeignInsertPlanView absent guards =>
                  void (insertAbsentNotInstalled absent sourceInstalled)
      ORetire actor => case ownerSelected of
        Refl =>
          let notOwned : Not (GenerationOwnedActor nameEq registered ordinal live
                (the (Action name key value world error) (ORetire selected)))
              notOwned owned = retained (DeleteRegisteredGeneration owned)
              0 step : RetainedNoEpisodeBoundaryStep name key world error value
                nameEq keyEq registered live
                (the (Action name key value world error) (ORetire selected)) tag
                afterState
                (MkSystemState (worldState before)
                  (planTarget (completePlanResult
                    (selectedBoundaryPlan boundary))))
              step = case registrationDisciplineAtOccurrence
                (Fired nameEq keyEq (ORetire selected) tag checked) global
                globalDiscipline
                (wholeInGlobal
                  (Fired nameEq keyEq (ORetire selected) tag checked) occurs) of
                MkLocatedRegistrationStep future futureDiscipline =>
                  retainedSuffixHeadPreservesNoEpisodeBoundary protocol nameEq
                    keyEq registered ordinal live (ORetire selected) before
                    (MkSystemState (worldState before)
                      (planTarget (completePlanResult
                        (selectedBoundaryPlan boundary))))
                    (selectedPlanExactBoundary nameEq keyEq unique boundary) tag
                    checked future futureDiscipline notOwned
              0 raw : applyAction @{nameEq} @{keyEq} (ORetire selected) before =
                Just (tag, afterState)
              raw = checkedActionProjects nameEq keyEq (ORetire selected)
                before afterState tag checked
              0 rawEta : applyAction @{nameEq} @{keyEq} (ORetire selected)
                (MkSystemState (worldState before) (registry before)) =
                Just (tag, afterState)
              rawEta = trans (cong (applyAction @{nameEq} @{keyEq}
                (the (Action name key value world error) (ORetire selected)))
                (stateEtaEpisodeReplay before)) raw
              0 tagSame : tag = ORetireTag
              tagSame = retireViewTagReplay
                (retireSuccessView nameEq keyEq selected (worldState before)
                  (registry before) tag afterState rawEta)
              0 checkedAt : checkedApplyAction @{nameEq} @{keyEq}
                (ORetire selected) before = Just (ORetireTag, afterState)
              checkedAt = replace
                {p = \observed => checkedApplyAction @{nameEq} @{keyEq}
                  (ORetire selected) before = Just (observed, afterState)}
                tagSame checked
              0 stepAt : RetainedNoEpisodeBoundaryStep name key world error value
                nameEq keyEq registered live (ORetire selected) ORetireTag
                afterState
                (MkSystemState (worldState before)
                  (planTarget (completePlanResult
                    (selectedBoundaryPlan boundary))))
              stepAt = replace
                {p = \observed => RetainedNoEpisodeBoundaryStep name key world
                  error value nameEq keyEq registered live (ORetire selected)
                  observed afterState
                  (MkSystemState (worldState before)
                    (planTarget (completePlanResult
                      (selectedBoundaryPlan boundary))))}
                tagSame step
          in case retainedSelectedRetirePreservesEpisodeBoundary nameEq keyEq
            selected registered ordinal live whole before afterState survivor
            checkedAt boundary stepAt of
            MkSelectedRetainedEpisodeStep named fired nextBoundary =>
              MkSelectedEpisodeRetainedHead named fired nextBoundary
      ORemove actor => case ownerSelected of
        Refl => void (removeCannotInstalled nameEq keyEq selected before afterState tag
          (checkedActionProjects nameEq keyEq (ORemove selected) before afterState
            tag checked) sourceInstalled)
      LBegin actor => case ownerSelected of
        Refl => void (retained (DeleteEpisodeGenerationLifecycle Refl Refl))
      LAdvance actor => case ownerSelected of
        Refl => void (retained (DeleteEpisodeGenerationLifecycle Refl Refl))
      LDivert actor => case ownerSelected of
        Refl => void (retained (DeleteEpisodeGenerationLifecycle Refl Refl))
      LLeave actor => case ownerSelected of
        Refl => void (retained (DeleteEpisodeGenerationLifecycle Refl Refl))
      LUnload actor => case ownerSelected of
        Refl => void (retained (DeleteEpisodeGenerationLifecycle Refl Refl))

    0 foreignCase :
      Not (actionOwner action = selected) ->
      SelectedEpisodeRetainedHead name key world error value nameEq keyEq
        selected registered ordinal live whole action afterState survivor
    foreignCase distinct with (isLifecycleAction action) proof kind
      foreignCase distinct | False =
        let notOwned : Not (GenerationOwnedActor nameEq registered ordinal live
              action)
            notOwned owned = retained (DeleteRegisteredGeneration owned)
            0 step : RetainedNoEpisodeBoundaryStep name key world error value
              nameEq keyEq registered
              (advanceGenerationEnvironment @{nameEq} ordinal action live)
              action tag afterState
              (MkSystemState (worldState before)
                (planTarget (completePlanResult
                  (selectedBoundaryPlan boundary))))
            step = exactStep notOwned
        in case retainedForeignOrchestrationPreservesEpisodeBoundary nameEq keyEq
          selected registered ordinal live action kind distinct whole before
          afterState survivor tag checked occurs
          (restrictTraceIndependent
            (\transition, occurrence => wholeInGlobal transition occurrence)
            independent)
          boundary step of
          MkForeignRetainedEpisodeStep named fired nextBoundary =>
            MkSelectedEpisodeRetainedHead named fired nextBoundary
      foreignCase distinct | True =
        let notOwned : Not (GenerationOwnedActor nameEq registered ordinal live
              action)
            notOwned owned = retained (DeleteRegisteredGeneration owned)
            0 step : RetainedNoEpisodeBoundaryStep name key world error value
              nameEq keyEq registered
              (advanceGenerationEnvironment @{nameEq} ordinal action live)
              action tag afterState
              (MkSystemState (worldState before)
                (planTarget (completePlanResult
                  (selectedBoundaryPlan boundary))))
            step = exactStep notOwned
            0 selectedPlanOutside : ActorOutsideDeletionPlan selected
              (inactiveLeafPlan (completePlanResult
                (selectedBoundaryPlan boundary)))
            selectedPlanOutside = selectedSourceOutsidePlan nameEq selected
              registered live stamped outside boundary
            0 strongOwnerOutside : (candidate : name) ->
              (generation : RegistrationGeneration name) ->
              Elem (candidate, generation) live -> Elem generation registered ->
              Not (actionOwner action = candidate)
            strongOwnerOutside = retainedNonInsertOutsideCurrentRegistered nameEq
              registered ordinal live unique action
              (lifecycleNonInsertReplay action kind) notOwned
            0 ownerPlanOutside : ActorOutsideDeletionPlan (actionOwner action)
              (inactiveLeafPlan (completePlanResult
                (selectedBoundaryPlan boundary)))
            ownerPlanOutside = actorOutsidePlan
              (completePlanResult (selectedBoundaryPlan boundary))
              (actionOwner action) strongOwnerOutside
            0 evidence :
              (leftSelected, leftOwner, rightOwner :
                Fiber name key value world error) ->
              lookupFiber @{nameEq} selected
                (planTarget (completePlanResult
                  (selectedBoundaryPlan boundary))) = Just leftSelected ->
              lookupFiber @{nameEq} (actionOwner action)
                (planTarget (completePlanResult
                  (selectedBoundaryPlan boundary))) = Just leftOwner ->
              lookupFiber @{nameEq} (actionOwner action) (registry survivor) =
                Just rightOwner ->
              FiberControlRelated leftOwner rightOwner ->
              ForeignLifecycleProviderFrameEvidence name key world error value
                nameEq keyEq global selected (actionOwner action)
                (MkSystemState (worldState before)
                  (planTarget (completePlanResult
                    (selectedBoundaryPlan boundary))))
                leftSelected leftOwner
            evidence = \leftSelected, leftOwner, rightOwner, selectedFound,
              leftFound, rightFound, controls => lifecycleAnchorAt anchors ordinal
                live action kind distinct before afterState tag checked rest
                selectedRest
                (wholeInGlobal (Fired nameEq keyEq action tag checked) occurs)
                boundary leftSelected leftOwner rightOwner selectedFound leftFound
                (trans (sym (lookupOutsideInactivePlan nameEq selected
                  (registry before)
                  (planTarget (completePlanResult
                    (selectedBoundaryPlan boundary)))
                  (inactiveLeafPlan (completePlanResult
                    (selectedBoundaryPlan boundary))) selectedPlanOutside))
                  selectedFound)
                (trans (sym (lookupOutsideInactivePlan nameEq
                  (actionOwner action) (registry before)
                  (planTarget (completePlanResult
                    (selectedBoundaryPlan boundary)))
                  (inactiveLeafPlan (completePlanResult
                    (selectedBoundaryPlan boundary))) ownerPlanOutside))
                  leftFound)
                rightFound controls
        in case retainedForeignLifecyclePreservesEpisodeBoundary nameEq keyEq
          selected registered ordinal live action kind distinct global noDependent
          whole before afterState survivor tag checked occurs
          (restrictTraceIndependent
            (\transition, occurrence => wholeInGlobal transition occurrence)
            independent)
          boundary emptyPlan selectedPlanOutside ownerPlanOutside step evidence of
          MkForeignRetainedEpisodeStep named fired nextBoundary =>
            MkSelectedEpisodeRetainedHead named fired nextBoundary
