module DGamma.CP4DeletionPostCloseLifecycle

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionBoundaryLifecycleCore
import DGamma.CP4DeletionBoundaryRetained
import DGamma.CP4DeletionFrameCore
import DGamma.CP4DeletionGenerationFilter
import DGamma.CP4DeletionGenerationUnique
import DGamma.CP4DeletionInactiveInvariant
import DGamma.CP4DeletionNoEpisodeReplay
import DGamma.CP4DeletionPlanBuilder
import DGamma.CP4DeletionPlanComplete
import DGamma.CP4DeletionPostCloseEffectReplay
import DGamma.CP4DeletionPostCloseOrchestration
import DGamma.CP4DeletionRelationalBoundary
import DGamma.CP4DeletionRelationalLifecycleAdvance
import DGamma.CP4DeletionRelationalLifecycleCore
import DGamma.CP4DeletionSelectedBoundary
import DGamma.CP4DeletionSelectedCloseBoundary
import DGamma.CP4DeletionSelectedForeignControlCore
import DGamma.CP4DeletionSelectedForeignLifecycleAdvanceDispatchCore
import DGamma.CP4DeletionSelectedForeignLifecycleCore
import DGamma.CP4DeletionSelectedForeignLifecycleDispatch
import DGamma.CP4DeletionSelectedForeignLifecycleProviderFrame
import DGamma.CP4DeletionSelectedForeignLifecycleReplayCore
import DGamma.CP4DeletionSelectedForeignOrchestration
import DGamma.CP4DeletionSelectedForeignOrchestrationStep
import DGamma.CP4DeletionSelectedForeignTables
import DGamma.CP4RecoveryEffectRespect
import DGamma.CP4RuntimeBindings
import Data.List.Elem
import Decidable.Equality

%default total

0 postCloseForeignTables :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (left, right : SystemState name key value world error) ->
  EffectStateRelated keyEq (projectEffectState @{nameEq} left)
    (projectEffectState @{nameEq} right) ->
  (actor : name) ->
  {leftFiber, rightFiber : Fiber name key value world error} ->
  Elem (Bind actor leftFiber) (bindings (registry left)) ->
  Elem (Bind actor rightFiber) (bindings (registry right)) ->
  bindings (ownedValues (fiberTable leftFiber)) =
    bindings (ownedValues (fiberTable rightFiber))
postCloseForeignTables nameEq keyEq left right effects actor leftMember
  rightMember =
    let leftFound = registryLookupFromMember nameEq (registry left) leftMember
        rightFound = registryLookupFromMember nameEq (registry right) rightMember
        leftProjected = projectedActorTable nameEq actor left leftFiber leftFound
        rightProjected = projectedActorTable nameEq actor right rightFiber
          rightFound
    in trans (cong bindings (sym leftProjected))
      (trans (tablesExact effects actor) (cong bindings rightProjected))

0 inactiveProviderExcluded :
  (keyEq : DecEq key) ->
  (selectedFiber : Fiber name key value world error) ->
  isInactive (fiberLifecycle selectedFiber) = True ->
  (wanted : key) ->
  Elem wanted (dependencies
    (componentDependencies (fiberComponent ownerFiber))) ->
  providerCandidate @{keyEq} wanted selectedFiber = False
inactiveProviderExcluded keyEq
  (MkFiber component parent retiredFlag table (Inactive outcome)) Refl wanted
  declares = Refl
inactiveProviderExcluded keyEq
  (MkFiber component parent retiredFlag table (Reloading remaining accumulator view))
  Refl wanted declares impossible
inactiveProviderExcluded keyEq
  (MkFiber component parent retiredFlag table (Active accumulator view)) Refl
  wanted declares impossible
inactiveProviderExcluded keyEq
  (MkFiber component parent retiredFlag table (Unloading accumulator view outcome))
  Refl wanted declares impossible

||| Replay one retained foreign lifecycle head after selected close. The plan's
||| selected Inactive witness gives the direct provider exclusion; standard
||| related effects give exact L-Advance outcome agreement.
public export
0 retainedForeignPostCloseLifecycle :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {initial, finalState : SystemState name key value world error} ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  GenerationEnvironmentNamesUnique live ->
  (action : Action name key value world error) ->
  (lifecycle : isLifecycleAction action = True) ->
  (actorDistinct : Not (actionOwner action = selected)) ->
  (global : Transitions initial finalState) ->
  NoDependentClosingEpisode {nameEq = nameEq} {keyEq = keyEq} selected global ->
  (original, originalAfter, originalFinal, survivor :
    SystemState name key value world error) ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action original =
    Just (tag, originalAfter)) ->
  (rest : Transitions originalAfter originalFinal) ->
  RegistrationStepDiscipline protocol nameEq action original rest ->
  (retained : Not
    (GenerationOwnedActor nameEq registered ordinal live action)) ->
  (noBegin : IsBeginAction action ->
    GenerationOwnedActor nameEq registered ordinal live action -> Void) ->
  (boundary : PostCloseSelectedBoundary name key world error value nameEq keyEq
    selected registered ordinal live original survivor) ->
  PostCloseOrchestrationStep name key world error value nameEq keyEq selected
    registered (S ordinal)
    (advanceGenerationEnvironment @{nameEq} ordinal action live)
    action originalAfter survivor
retainedForeignPostCloseLifecycle {name} {key} {world} {error} {value}
  protocol nameEq keyEq selected registered ordinal live unique action lifecycle
  actorDistinct global noDependent original originalAfter originalFinal survivor
  tag checked rest discipline retained noBegin boundary =
    let exactBefore = postClosePlanExactBoundary nameEq keyEq unique boundary
        exactStep = retainedSuffixHeadPreservesNoEpisodeBoundary protocol nameEq
          keyEq registered ordinal live action original
          (plannedSystemState original
            (completePlanResult (postClosePlan boundary)))
          exactBefore tag checked rest discipline retained
        0 planRaw = namedFireProjectsRaw nameEq keyEq action (plannedSystemState original (completePlanResult (postClosePlan boundary))) (retainedBoundaryNamed exactStep)
          (retainedBoundaryFires exactStep)
        (leftOwner ** leftFound) = lifecycleOwnerPresent nameEq keyEq action
          lifecycle (plannedSystemState original (completePlanResult (postClosePlan boundary))) (namedAfter (retainedBoundaryNamed exactStep)) (namedTag (retainedBoundaryNamed exactStep)) planRaw
        maybeOwner = selectedOrderedForeignLookupControls nameEq selected
          (actionOwner action) actorDistinct
          (planTarget (completePlanResult (postClosePlan boundary)))
          (registry survivor) (postCloseControls boundary)
    in case foreignControlLookupFound nameEq (actionOwner action)
      (planTarget (completePlanResult (postClosePlan boundary)))
      (registry survivor) leftOwner leftFound maybeOwner of
      MkForeignRelatedFiberFound rightOwner rightFound ownersRelated =>
        case postClosePlanSelectedInactive boundary of
          leftInactive@(MkInactiveFiberAt selectedComponent selectedParent
            selectedRetired selectedTable selectedOutcome selectedFound) =>
            let 0 selectedExcluded : ((wanted : key) -> Elem wanted
                  (dependencies (componentDependencies
                    (fiberComponent leftOwner))) ->
                  providerCandidate @{keyEq} wanted (MkFiber selectedComponent selectedParent selectedRetired selectedTable
                    (Inactive selectedOutcome)) = False)
                selectedExcluded wanted ownerDeclares = Refl
                0 evidence : (ForeignLifecycleProviderFrameEvidence name key
                  world error value nameEq keyEq global selected
                  (actionOwner action)
                  (plannedSystemState original
                    (completePlanResult (postClosePlan boundary)))
                  (MkFiber selectedComponent selectedParent selectedRetired selectedTable
                    (Inactive selectedOutcome)) leftOwner)
                evidence = DirectProviderFrameEvidence selectedExcluded
                0 foreignTables : ((current : name) ->
                  Not (current = selected) ->
                  {leftFiber, rightFiber : Fiber name key value world error} ->
                  Elem (Bind current leftFiber)
                    (bindings (planTarget (completePlanResult
                      (postClosePlan boundary)))) ->
                  Elem (Bind current rightFiber) (bindings (registry survivor)) ->
                  FiberControlRelated leftFiber rightFiber ->
                  bindings (ownedValues (fiberTable leftFiber)) =
                    bindings (ownedValues (fiberTable rightFiber)))
                foreignTables = \current, currentDistinct,
                  leftMember, rightMember, controls =>
                    postCloseForeignTables nameEq keyEq (plannedSystemState original (completePlanResult (postClosePlan boundary))) survivor
                      (postCloseEffects boundary) current leftMember rightMember
                0 planChecked : (checkedApplyAction @{nameEq} @{keyEq} action
                  (plannedSystemState original
                    (completePlanResult (postClosePlan boundary))) =
                  Just (namedTag (retainedBoundaryNamed exactStep),
                    namedAfter (retainedBoundaryNamed exactStep)))
                planChecked = rewrite planRaw in
                  rewrite survivorBoundaryWellFormed
                    (retainedNextBoundary exactStep) in Refl
                0 effectsEta : (EffectStateRelated keyEq
                  (projectEffectState @{nameEq}
                    (plannedSystemState original
                      (completePlanResult (postClosePlan boundary))))
                  (projectEffectState @{nameEq}
                    (the (SystemState name key value world error)
                      (MkSystemState (worldState survivor)
                        (registry survivor)))))
                effectsEta = replace
                  {p = \observed => EffectStateRelated keyEq
                    (projectEffectState @{nameEq}
                      (plannedSystemState original
                        (completePlanResult (postClosePlan boundary))))
                    (projectEffectState @{nameEq} observed)}
                  (sym (systemEtaPost survivor)) (postCloseEffects boundary)
                outcomes : ForeignAdvanceOutcomeProvider name key world error
                  value nameEq keyEq action (worldState original)
                  (worldState survivor)
                  (planTarget (completePlanResult (postClosePlan boundary)))
                  (registry survivor)
                outcomes = case action of
                  LAdvance actor => \component, leftTable, rightTable, step,
                    remaining, view, leftParent, rightParent, retiredFlag,
                    leftAccumulator, rightAccumulator, concreteLeftFound,
                    concreteRightFound =>
                      let singleton : Transitions
                            (plannedSystemState original
                              (completePlanResult (postClosePlan boundary)))
                            (namedAfter (retainedBoundaryNamed exactStep))
                          singleton = MoreTransitions
                            (Fired nameEq keyEq (LAdvance actor)
                              (namedTag (retainedBoundaryNamed exactStep))
                              planChecked) NoTransitions
                          stage : IteratorStage name key world error value actor
                            singleton
                          stage = StageFromAdvance nameEq keyEq actor
                            (namedTag (retainedBoundaryNamed exactStep))
                            planChecked
                            OccursHere
                            (MkFiber component leftParent retiredFlag leftTable
                              (Reloading (step :: remaining) leftAccumulator
                                view)) concreteLeftFound
                            (step :: remaining) leftAccumulator view Refl step
                            remaining SuffixHere
                          0 survivorToPlan : EffectStateRelated keyEq
                            (projectEffectState @{nameEq}
                              (the (SystemState name key value world error)
                                (MkSystemState (worldState survivor)
                                  (registry survivor))))
                            (projectEffectState @{nameEq}
                              (plannedSystemState original
                                (completePlanResult
                                  (postClosePlan boundary))))
                          survivorToPlan = case effectsEta of
                            MkEffectStateRelated ambient tables =>
                              MkEffectStateRelated (sym ambient)
                                (\current => sym (tables current))
                      in iteratorStageOutcomeRelated keyEq stage
                        (projectEffectState @{nameEq}
                          (the (SystemState name key value world error)
                            (MkSystemState (worldState survivor)
                              (registry survivor))))
                        (projectEffectState @{nameEq}
                          (plannedSystemState original
                            (completePlanResult (postClosePlan boundary))))
                        survivorToPlan
                  OInsert actor parent component => ()
                  ORetire actor => ()
                  ORemove actor => ()
                  LBegin actor => ()
                  LDivert actor => ()
                  LLeave actor => ()
                  LUnload actor => ()
                0 controlEta : (ForeignLifecycleControlReplay name key world
                  error value nameEq keyEq selected action
                  (namedTag (retainedBoundaryNamed exactStep))
                  (namedAfter (retainedBoundaryNamed exactStep))
                  (MkSystemState (worldState survivor) (registry survivor)))
                controlEta = replayForeignLifecycleControlsFromProviderEvidence
                  nameEq keyEq selected action actorDistinct lifecycle global
                  noDependent (worldState original) (worldState survivor)
                  (planTarget (completePlanResult (postClosePlan boundary)))
                  (registry survivor) leftOwner rightOwner (MkFiber selectedComponent selectedParent selectedRetired selectedTable
                    (Inactive selectedOutcome))
                  selectedFound leftFound rightFound evidence
                  (replace
                    {p = \observed => SelectedSurvivorCleanInactive name key
                      world error value nameEq selected observed}
                    (sym (systemEtaPost survivor))
                    (postCloseCleanInactive boundary))
                  (postCloseControls boundary) foreignTables
                  (namedTag (retainedBoundaryNamed exactStep)) (namedAfter (retainedBoundaryNamed exactStep)) planRaw
                  (postCloseSurvivorWellFormed boundary) outcomes
                0 control : ForeignLifecycleControlReplay name key world error
                  value nameEq keyEq selected action (namedTag (retainedBoundaryNamed exactStep))
                  (namedAfter (retainedBoundaryNamed exactStep)) survivor
                control = replace
                  {p = \observed => ForeignLifecycleControlReplay name key world
                    error value nameEq keyEq selected action (namedTag (retainedBoundaryNamed exactStep))
                    (namedAfter (retainedBoundaryNamed exactStep)) observed}
                  (systemEtaPost survivor) controlEta
                0 orchestrationControl : (ForeignOrchestrationControlReplay
                  name key world error value nameEq keyEq selected action
                  (namedTag (retainedBoundaryNamed exactStep))
                  (namedAfter (retainedBoundaryNamed exactStep)) survivor)
                orchestrationControl = MkForeignOrchestrationControlReplay
                  (foreignLifecycleAfter control) (foreignLifecycleRaw control)
                  (foreignLifecycleChecked control)
                  (foreignLifecycleOrdered control)
                0 planInactive : (InactiveFiberAt name key world error value
                  nameEq selected
                  (namedAfter (retainedBoundaryNamed exactStep)))
                planInactive = inactiveForeignPost nameEq keyEq selected action
                  (\same => actorDistinct (sym same)) (plannedSystemState original (completePlanResult (postClosePlan boundary)))
                  (namedAfter (retainedBoundaryNamed exactStep)) (namedTag (retainedBoundaryNamed exactStep)) planRaw leftInactive
                0 clean : (SelectedSurvivorCleanInactive name key world error
                  value nameEq selected (foreignLifecycleAfter control))
                clean = foreignActionPreservesCleanInactive nameEq keyEq
                  selected action actorDistinct survivor
                  (foreignLifecycleAfter control) (namedTag (retainedBoundaryNamed exactStep))
                  (foreignLifecycleRaw control) (postCloseCleanInactive boundary)
                0 headEffects : (EffectStateRelated keyEq
                  (projectEffectState @{nameEq}
                    (namedAfter (retainedBoundaryNamed exactStep)))
                  (projectEffectState @{nameEq}
                    (foreignLifecycleAfter control)))
                headEffects = postCloseLifecycleEffects nameEq keyEq action
                  lifecycle (namedTag (retainedBoundaryNamed exactStep)) (plannedSystemState original (completePlanResult (postClosePlan boundary))) (namedAfter (retainedBoundaryNamed exactStep))
                  survivor (foreignLifecycleAfter control) planChecked
                  (foreignLifecycleChecked control) (postCloseEffects boundary)
                  leftOwner rightOwner leftFound rightFound ownersRelated
            in packagePostCloseOrchestrationWithInvariants protocol nameEq keyEq
              selected registered ordinal live unique action original
              originalAfter originalFinal survivor tag checked rest discipline
              retained noBegin (postCloseCurrentInactive boundary)
              (postCloseCurrentEmpty boundary) boundary exactStep
              orchestrationControl planInactive clean headEffects
