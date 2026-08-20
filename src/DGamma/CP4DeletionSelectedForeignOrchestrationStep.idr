module DGamma.CP4DeletionSelectedForeignOrchestrationStep

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionBoundaryDeleted
import DGamma.CP4DeletionBoundaryRetained
import DGamma.CP4DeletionGenerationFilter
import DGamma.CP4DeletionNoEpisodeReplay
import DGamma.CP4DeletionPlanBuilder
import DGamma.CP4DeletionPlanComplete
import DGamma.CP4DeletionSelectedBoundary
import DGamma.CP4DeletionSelectedEffectCore
import DGamma.CP4DeletionSelectedEffectForeign
import DGamma.CP4DeletionSelectedForeignOrchestration
import DGamma.CP4DeletionSelectedRetire
import Decidable.Equality

%default total

public export
record NamedForeignOrchestrationReplay
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (action : Action name key value world error)
  (before, target : SystemState name key value world error) where
  constructor MkNamedForeignOrchestrationReplay
  orchestrationNamed : NamedTransition name key world error value action before
  0 orchestrationFires : fireNamed nameEq keyEq action before =
    Just orchestrationNamed
  0 orchestrationNamedAfter : namedAfter orchestrationNamed = target

public export
foreignOrchestrationReplayNamed :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  (before : SystemState name key value world error) ->
  (replay : ForeignOrchestrationControlReplay name key world error value nameEq
    keyEq selected action tag planAfter before) ->
  NamedForeignOrchestrationReplay name key world error value nameEq keyEq action
    before (foreignControlAfter replay)
foreignOrchestrationReplayNamed nameEq keyEq action before replay
  with (fireNamed nameEq keyEq action before) proof fired
  foreignOrchestrationReplayNamed nameEq keyEq action before replay | Nothing =
    case replay of
    MkForeignOrchestrationControlReplay after raw checked ordered =>
      let 0 checkedNothing : (checkedApplyAction @{nameEq} @{keyEq} action
            before = Nothing)
          checkedNothing = fireNamedNothingImpliesCheckedNothing nameEq keyEq
            action before fired
      in void (nothingIsNotJust (trans (sym checkedNothing) checked))
  foreignOrchestrationReplayNamed nameEq keyEq action before replay |
    Just named = case replay of
      MkForeignOrchestrationControlReplay after raw checked ordered =>
        let 0 namedRaw = namedFireProjectsRaw nameEq keyEq action before named
              fired
            0 pairSame : ((namedTag named, namedAfter named) = (tag, after))
            pairSame = justInjective (trans (sym namedRaw) raw)
        in MkNamedForeignOrchestrationReplay named fired (cong snd pairSame)

public export
record ForeignRetainedEpisodeStep
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (selected : name)
  (registered : List (RegistrationGeneration name))
  (ordinal : Nat) (live : GenerationEnvironment name)
  {wholeFirst, wholeLast : SystemState name key value world error}
  (whole : Transitions wholeFirst wholeLast)
  (action : Action name key value world error)
  (originalAfter, survivorBefore : SystemState name key value world error) where
  constructor MkForeignRetainedEpisodeStep
  foreignRetainedNamed : NamedTransition name key world error value action
    survivorBefore
  0 foreignRetainedFires : fireNamed nameEq keyEq action survivorBefore =
    Just foreignRetainedNamed
  0 foreignRetainedBoundary : SelectedEpisodeReplayBoundary name key world error
    value nameEq keyEq selected registered (S ordinal)
    (advanceGenerationEnvironment @{nameEq} ordinal action live) whole
    originalAfter (namedAfter foreignRetainedNamed)

0 orchestrationSuccessfulTagsSame :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  isLifecycleAction action = False ->
  (leftBefore, rightBefore : SystemState name key value world error) ->
  (leftTag, rightTag : RuleTag) ->
  (leftAfter, rightAfter : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq} action leftBefore =
    Just (leftTag, leftAfter) ->
  applyAction @{nameEq} @{keyEq} action rightBefore =
    Just (rightTag, rightAfter) ->
  leftTag = rightTag
orchestrationSuccessfulTagsSame nameEq keyEq
  (OInsert actor parent component) orchestration
  (MkSystemState leftWorld leftRegistry)
  (MkSystemState rightWorld rightRegistry) leftTag rightTag leftAfter rightAfter
  leftRaw rightRaw =
    case foreignInsertPlanView nameEq keyEq actor parent component leftWorld
      leftRegistry leftTag leftAfter leftRaw of
      MkForeignInsertPlanView leftAbsent leftGuards =>
        case foreignInsertPlanView nameEq keyEq actor parent component rightWorld
          rightRegistry rightTag rightAfter rightRaw of
          MkForeignInsertPlanView rightAbsent rightGuards => Refl
orchestrationSuccessfulTagsSame nameEq keyEq (ORetire actor) orchestration
  (MkSystemState leftWorld leftRegistry)
  (MkSystemState rightWorld rightRegistry) leftTag rightTag leftAfter rightAfter
  leftRaw rightRaw =
    case retireSuccessView nameEq keyEq actor leftWorld leftRegistry leftTag
      leftAfter leftRaw of
      MkRetireSuccessView leftFiber leftFound =>
        case retireSuccessView nameEq keyEq actor rightWorld rightRegistry
          rightTag rightAfter rightRaw of
          MkRetireSuccessView rightFiber rightFound => Refl
orchestrationSuccessfulTagsSame nameEq keyEq (ORemove actor) orchestration
  (MkSystemState leftWorld leftRegistry)
  (MkSystemState rightWorld rightRegistry) leftTag rightTag leftAfter rightAfter
  leftRaw rightRaw =
    case removeSuccessView nameEq keyEq actor leftWorld leftRegistry leftTag
      leftAfter leftRaw of
      MkRemoveSuccessView leftFiber leftFound leftGuard leftNoChild =>
        case removeSuccessView nameEq keyEq actor rightWorld rightRegistry
          rightTag rightAfter rightRaw of
          MkRemoveSuccessView rightFiber rightFound rightGuard rightNoChild =>
            Refl
orchestrationSuccessfulTagsSame nameEq keyEq (LBegin actor) Refl left right
  leftTag rightTag leftAfter rightAfter leftRaw rightRaw impossible
orchestrationSuccessfulTagsSame nameEq keyEq (LAdvance actor) Refl left right
  leftTag rightTag leftAfter rightAfter leftRaw rightRaw impossible
orchestrationSuccessfulTagsSame nameEq keyEq (LDivert actor) Refl left right
  leftTag rightTag leftAfter rightAfter leftRaw rightRaw impossible
orchestrationSuccessfulTagsSame nameEq keyEq (LLeave actor) Refl left right
  leftTag rightTag leftAfter rightAfter leftRaw rightRaw impossible
orchestrationSuccessfulTagsSame nameEq keyEq (LUnload actor) Refl left right
  leftTag rightTag leftAfter rightAfter leftRaw rightRaw impossible

0 stateRuntimeEta : (state : SystemState name key value world error) ->
  MkSystemState (worldState state) (registry state) = state
stateRuntimeEta (MkSystemState ambient fibers) = Refl

0 distinctSymmetric : Not (left = right) -> Not (right = left)
distinctSymmetric distinct Refl = distinct Refl

public export
0 foreignActionPreservesCleanInactive :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (action : Action name key value world error) ->
  Not (actionOwner action = selected) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} action before = Just (tag, afterState) ->
  SelectedSurvivorCleanInactive name key world error value nameEq selected
    before ->
  SelectedSurvivorCleanInactive name key world error value nameEq selected
    afterState
foreignActionPreservesCleanInactive nameEq keyEq selected action distinct before
  afterState tag raw clean =
    let 0 update = applyActionLocalUpdate nameEq keyEq action before afterState
          tag raw
        0 selectedDifferent : Not (selected = actionOwner action)
        selectedDifferent = distinctSymmetric distinct
        0 lookupSame : lookupFiber @{nameEq} {name = name} {key = key}
          {value = value} {world = world} {error = error} selected
          (registry afterState) = lookupFiber @{nameEq} selected
            (registry before)
        lookupSame = systemLocalUpdateForeign nameEq selected
          (actionOwner action) selectedDifferent before afterState update
    in case clean of
      SelectedCleanInactiveWitness component parent retiredFlag table found =>
        SelectedCleanInactiveWitness component parent retiredFlag table
          (trans lookupSame found)

packageForeignOrchestrationStep :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (action : Action name key value world error) ->
  (orchestration : isLifecycleAction action = False) ->
  (distinct : Not (actionOwner action = selected)) ->
  (whole : Transitions wholeFirst wholeLast) ->
  (before, afterState, survivor : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  (occurs : OccursIn
    (Fired {before = before} {afterState = afterState}
      nameEq keyEq action tag checked) whole) ->
  TraceIndependent name key world error value keyEq whole ->
  (boundary : SelectedEpisodeReplayBoundary name key world error value nameEq
    keyEq selected registered ordinal live whole before survivor) ->
  (exactStep : RetainedNoEpisodeBoundaryStep name key world error value nameEq
    keyEq registered
    (advanceGenerationEnvironment @{nameEq} ordinal action live) action tag
    afterState
    (MkSystemState (worldState before)
      (planTarget (completePlanResult (selectedBoundaryPlan boundary))))) ->
  (control : ForeignOrchestrationControlReplay name key world error value nameEq
    keyEq selected action
    (namedTag (retainedBoundaryNamed exactStep))
    (namedAfter (retainedBoundaryNamed exactStep)) survivor) ->
  ForeignRetainedEpisodeStep name key world error value nameEq keyEq selected
    registered ordinal live whole action afterState survivor
packageForeignOrchestrationStep nameEq keyEq selected registered ordinal live
  action orchestration distinct whole before afterState
  survivor@(MkSystemState survivorWorld survivorRegistry) tag checked
  occurs independent boundary exactStep control =
    let 0 originalRaw : (applyAction @{nameEq} @{keyEq} action before =
          Just (tag, afterState))
        originalRaw = checkedActionProjects nameEq keyEq action before
          afterState tag checked
        0 planRaw : (applyAction @{nameEq} @{keyEq} action
          (MkSystemState (worldState before)
            (planTarget (completePlanResult
              (selectedBoundaryPlan boundary)))) =
          Just (namedTag (retainedBoundaryNamed exactStep),
            namedAfter (retainedBoundaryNamed exactStep)))
        planRaw = namedFireProjectsRaw nameEq keyEq action (MkSystemState (worldState before)
            (planTarget (completePlanResult (selectedBoundaryPlan boundary))))
          (retainedBoundaryNamed exactStep) (retainedBoundaryFires exactStep)
        0 planTagSame : (namedTag (retainedBoundaryNamed exactStep) = tag)
        planTagSame = orchestrationSuccessfulTagsSame nameEq keyEq action
          orchestration (MkSystemState (worldState before)
            (planTarget (completePlanResult (selectedBoundaryPlan boundary)))) before
          (namedTag (retainedBoundaryNamed exactStep)) tag
          (namedAfter (retainedBoundaryNamed exactStep)) afterState planRaw
          originalRaw
        controlAtTag : ForeignOrchestrationControlReplay name key world error
          value nameEq keyEq selected action tag
          (namedAfter (retainedBoundaryNamed exactStep)) survivor
        controlAtTag = replace
          {p = \observed => ForeignOrchestrationControlReplay name key world error
            value nameEq keyEq selected action observed
            (namedAfter (retainedBoundaryNamed exactStep)) survivor}
          planTagSame control
        0 transition : Transition before afterState
        transition = Fired nameEq keyEq action tag checked
        0 effectStep : ForeignSelectedEffectStep name key world error value
          nameEq keyEq selected before afterState survivor transition whole
        effectStep = foreignStepTransposesSelectedEffectBoundary nameEq keyEq
          selected action tag before afterState checked whole occurs independent
          survivor (selectedBoundaryEffects boundary) (distinctSymmetric distinct)
        0 nextEffects : SelectedEffectReplayBoundary name key world error value
          nameEq keyEq selected whole afterState
          (foreignControlAfter controlAtTag)
        nextEffects = foreignOrchestrationControlGivesNextEffectBoundary nameEq
          keyEq selected action orchestration tag before afterState survivor
          checked whole effectStep (namedAfter (retainedBoundaryNamed exactStep))
          controlAtTag
        nextPackage : RetainedNextPlanPackage name key world error value nameEq
          registered (advanceGenerationEnvironment @{nameEq} ordinal action live)
          afterState (namedAfter (retainedBoundaryNamed exactStep))
        nextPackage = retainedStepNextPlanPackage exactStep
        nextComplete : CompleteCurrentRegisteredPlanResult name key world error
          value nameEq registered
          (advanceGenerationEnvironment @{nameEq} ordinal action live)
          (registry afterState)
        nextComplete = retainedPackagePlan nextPackage
        0 nextPlanBindings : bindings
          (planTarget (completePlanResult nextComplete)) =
          bindings (registry (namedAfter (retainedBoundaryNamed exactStep)))
        nextPlanBindings = retainedPackageBindings nextPackage
        0 nextOrdered : SelectedOrderedRegistryControlsRelated name key world
          error value selected
          (bindings (planTarget (completePlanResult nextComplete)))
          (bindings (registry (foreignControlAfter controlAtTag)))
        nextOrdered = selectedOrderedTransport (sym nextPlanBindings) Refl
          (foreignControlOrdered controlAtTag)
        0 nextClean : SelectedSurvivorCleanInactive name key world error value
          nameEq selected (foreignControlAfter controlAtTag)
        nextClean = foreignActionPreservesCleanInactive nameEq keyEq selected
          action distinct survivor (foreignControlAfter controlAtTag) tag
          (foreignControlRaw controlAtTag)
          (selectedBoundarySurvivorCleanInactive boundary)
        0 originalAfterWellFormed : registryWellFormed @{nameEq} @{keyEq}
          afterState = True
        originalAfterWellFormed = preservationTheoremProof nameEq keyEq action
          before afterState tag (selectedOriginalWellFormed boundary)
          (checkedActionProjects nameEq keyEq action before afterState tag checked)
        0 survivorAfterWellFormed : registryWellFormed @{nameEq} @{keyEq}
          (foreignControlAfter controlAtTag) = True
        survivorAfterWellFormed = preservationTheoremProof nameEq keyEq action
          survivor (foreignControlAfter controlAtTag) tag
          (selectedSurvivorWellFormed boundary) (foreignControlRaw controlAtTag)
        nextBoundary = MkSelectedEpisodeReplayBoundary nextEffects nextComplete
          nextOrdered nextClean originalAfterWellFormed survivorAfterWellFormed
        namedReplay = foreignOrchestrationReplayNamed nameEq keyEq action
          survivor controlAtTag
    in case namedReplay of
      MkNamedForeignOrchestrationReplay named fires namedAfterSame =>
        let 0 namedBoundary : SelectedEpisodeReplayBoundary name key world error
              value nameEq keyEq selected registered (S ordinal)
              (advanceGenerationEnvironment @{nameEq} ordinal action live) whole
              afterState (namedAfter named)
            namedBoundary = replace
              {p = \observed => SelectedEpisodeReplayBoundary name key world error
                value nameEq keyEq selected registered (S ordinal)
                (advanceGenerationEnvironment @{nameEq} ordinal action live)
                whole afterState observed}
              (sym namedAfterSame) nextBoundary
        in MkForeignRetainedEpisodeStep named fires namedBoundary

||| Exhaustive retained foreign orchestration replay at a selected quotient
||| boundary.  The exact plan-side head is supplied by the existing current-R
||| commutation theorem.
public export
0 retainedForeignOrchestrationPreservesEpisodeBoundary :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (action : Action name key value world error) ->
  (orchestration : isLifecycleAction action = False) ->
  (distinct : Not (actionOwner action = selected)) ->
  (whole : Transitions wholeFirst wholeLast) ->
  (before, afterState, survivor : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  (occurs : OccursIn
    (Fired {before = before} {afterState = afterState}
      nameEq keyEq action tag checked) whole) ->
  TraceIndependent name key world error value keyEq whole ->
  (boundary : SelectedEpisodeReplayBoundary name key world error value nameEq
    keyEq selected registered ordinal live whole before survivor) ->
  (exactStep : RetainedNoEpisodeBoundaryStep name key world error value nameEq
    keyEq registered
    (advanceGenerationEnvironment @{nameEq} ordinal action live) action tag
    afterState
    (MkSystemState (worldState before)
      (planTarget (completePlanResult (selectedBoundaryPlan boundary))))) ->
  ForeignRetainedEpisodeStep name key world error value nameEq keyEq selected
    registered ordinal live whole action afterState survivor
retainedForeignOrchestrationPreservesEpisodeBoundary nameEq keyEq selected
  registered ordinal live (OInsert actor parent component) orchestration distinct
  whole before afterState survivor tag checked occurs independent boundary
  exactStep =
    let planRaw = namedFireProjectsRaw nameEq keyEq
          (OInsert actor parent component)
          (MkSystemState (worldState before)
            (planTarget (completePlanResult (selectedBoundaryPlan boundary))))
          (retainedBoundaryNamed exactStep) (retainedBoundaryFires exactStep)
        control = replayForeignInsertControls nameEq keyEq selected actor distinct
          parent component (worldState before) (worldState survivor)
          (planTarget (completePlanResult (selectedBoundaryPlan boundary)))
          (registry survivor) (selectedBoundaryOrderedControls boundary)
          (namedTag (retainedBoundaryNamed exactStep)) (namedAfter (retainedBoundaryNamed exactStep)) planRaw
          (selectedSurvivorWellFormed boundary)
        controlExact : ForeignOrchestrationControlReplay name key world error
          value nameEq keyEq selected (OInsert actor parent component)
          (namedTag (retainedBoundaryNamed exactStep))
          (namedAfter (retainedBoundaryNamed exactStep)) survivor
        controlExact = replace
          {p = \state => ForeignOrchestrationControlReplay name key world error
            value nameEq keyEq selected (OInsert actor parent component)
            (namedTag (retainedBoundaryNamed exactStep))
            (namedAfter (retainedBoundaryNamed exactStep)) state}
          (stateRuntimeEta survivor) control
    in packageForeignOrchestrationStep nameEq keyEq selected registered ordinal
      live (OInsert actor parent component) orchestration distinct whole before
      afterState survivor tag checked occurs independent boundary exactStep controlExact
retainedForeignOrchestrationPreservesEpisodeBoundary nameEq keyEq selected
  registered ordinal live (ORetire actor) orchestration distinct whole before
  afterState survivor tag checked occurs independent boundary exactStep =
    let planRaw = namedFireProjectsRaw nameEq keyEq (ORetire actor)
          (MkSystemState (worldState before)
            (planTarget (completePlanResult (selectedBoundaryPlan boundary))))
          (retainedBoundaryNamed exactStep) (retainedBoundaryFires exactStep)
        control = replayForeignRetireControls nameEq keyEq selected actor distinct
          (worldState before) (worldState survivor)
          (planTarget (completePlanResult (selectedBoundaryPlan boundary)))
          (registry survivor) (selectedBoundaryOrderedControls boundary)
          (namedTag (retainedBoundaryNamed exactStep)) (namedAfter (retainedBoundaryNamed exactStep)) planRaw
          (selectedSurvivorWellFormed boundary)
        controlExact : ForeignOrchestrationControlReplay name key world error
          value nameEq keyEq selected (ORetire actor)
          (namedTag (retainedBoundaryNamed exactStep))
          (namedAfter (retainedBoundaryNamed exactStep)) survivor
        controlExact = replace
          {p = \state => ForeignOrchestrationControlReplay name key world error
            value nameEq keyEq selected (ORetire actor)
            (namedTag (retainedBoundaryNamed exactStep))
            (namedAfter (retainedBoundaryNamed exactStep)) state}
          (stateRuntimeEta survivor) control
    in packageForeignOrchestrationStep nameEq keyEq selected registered ordinal
      live (ORetire actor) orchestration distinct whole before afterState survivor
      tag checked occurs independent boundary exactStep controlExact
retainedForeignOrchestrationPreservesEpisodeBoundary nameEq keyEq selected
  registered ordinal live (ORemove actor) orchestration distinct whole before
  afterState survivor tag checked occurs independent boundary exactStep =
    let planRaw = namedFireProjectsRaw nameEq keyEq (ORemove actor)
          (MkSystemState (worldState before)
            (planTarget (completePlanResult (selectedBoundaryPlan boundary))))
          (retainedBoundaryNamed exactStep) (retainedBoundaryFires exactStep)
        control = replayForeignRemoveControls nameEq keyEq selected actor distinct
          (worldState before) (worldState survivor)
          (planTarget (completePlanResult (selectedBoundaryPlan boundary)))
          (registry survivor) (selectedBoundaryOrderedControls boundary)
          (namedTag (retainedBoundaryNamed exactStep)) (namedAfter (retainedBoundaryNamed exactStep)) planRaw
          (selectedSurvivorWellFormed boundary)
        controlExact : ForeignOrchestrationControlReplay name key world error
          value nameEq keyEq selected (ORemove actor)
          (namedTag (retainedBoundaryNamed exactStep))
          (namedAfter (retainedBoundaryNamed exactStep)) survivor
        controlExact = replace
          {p = \state => ForeignOrchestrationControlReplay name key world error
            value nameEq keyEq selected (ORemove actor)
            (namedTag (retainedBoundaryNamed exactStep))
            (namedAfter (retainedBoundaryNamed exactStep)) state}
          (stateRuntimeEta survivor) control
    in packageForeignOrchestrationStep nameEq keyEq selected registered ordinal
      live (ORemove actor) orchestration distinct whole before afterState survivor
      tag checked occurs independent boundary exactStep controlExact
retainedForeignOrchestrationPreservesEpisodeBoundary nameEq keyEq selected
  registered ordinal live (LBegin actor) Refl distinct whole before afterState
  survivor tag checked occurs independent boundary exactStep impossible
retainedForeignOrchestrationPreservesEpisodeBoundary nameEq keyEq selected
  registered ordinal live (LAdvance actor) Refl distinct whole before afterState
  survivor tag checked occurs independent boundary exactStep impossible
retainedForeignOrchestrationPreservesEpisodeBoundary nameEq keyEq selected
  registered ordinal live (LDivert actor) Refl distinct whole before afterState
  survivor tag checked occurs independent boundary exactStep impossible
retainedForeignOrchestrationPreservesEpisodeBoundary nameEq keyEq selected
  registered ordinal live (LLeave actor) Refl distinct whole before afterState
  survivor tag checked occurs independent boundary exactStep impossible
retainedForeignOrchestrationPreservesEpisodeBoundary nameEq keyEq selected
  registered ordinal live (LUnload actor) Refl distinct whole before afterState
  survivor tag checked occurs independent boundary exactStep impossible
