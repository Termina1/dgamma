module DGamma.CP4DeletionPostCloseOrchestration

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionBoundaryRetained
import DGamma.CP4DeletionControlPlan
import DGamma.CP4DeletionEmptyTableInvariant
import DGamma.CP4DeletionGenerationFilter
import DGamma.CP4DeletionGenerationUnique
import DGamma.CP4DeletionInactiveInvariant
import DGamma.CP4DeletionNoEpisodeReplay
import DGamma.CP4DeletionPlanBuilder
import DGamma.CP4DeletionPlanComplete
import DGamma.CP4DeletionPlanEffects
import DGamma.CP4DeletionPlanEmpty
import DGamma.CP4DeletionPostCloseEffectReplay
import DGamma.CP4DeletionRelationalActionCore
import DGamma.CP4DeletionRelationalBoundary
import DGamma.CP4DeletionRelationalSuffixFold
import DGamma.CP4DeletionSelectedBoundary
import DGamma.CP4DeletionSelectedCloseBoundary
import DGamma.CP4DeletionSelectedForeignOrchestration
import DGamma.CP4DeletionSelectedForeignOrchestrationStep
import DGamma.CP4DeletionSelectedRetire
import DGamma.CP4RuntimeBindings
import Decidable.Equality

%default total

0 effectTransitivePostOrchestration :
  EffectStateRelated keyEq first middle ->
  EffectStateRelated keyEq middle finalState ->
  EffectStateRelated keyEq first finalState
effectTransitivePostOrchestration
  (MkEffectStateRelated firstAmbient firstTables)
  (MkEffectStateRelated secondAmbient secondTables) =
    MkEffectStateRelated (trans firstAmbient secondAmbient)
      (\actor => trans (firstTables actor) (secondTables actor))

0 effectTableReproofPost :
  (nameEq : DecEq name) -> (actor : name) -> (ambient : world) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (leftUnique, rightUnique : UniqueKeys (bindingKeys entries)) ->
  bindings (effectTables (projectEffectState @{nameEq}
    (the (SystemState name key value world error)
      (MkSystemState ambient (MkCoeffectContext entries leftUnique)))) actor) =
  bindings (effectTables (projectEffectState @{nameEq}
    (the (SystemState name key value world error)
      (MkSystemState ambient (MkCoeffectContext entries rightUnique)))) actor)
effectTableReproofPost nameEq actor ambient entries leftUnique rightUnique
  with (lookupEntries @{nameEq} actor entries)
  effectTableReproofPost nameEq actor ambient entries leftUnique rightUnique |
    Nothing = Refl
  effectTableReproofPost nameEq actor ambient entries leftUnique rightUnique |
    Just fiber = Refl

0 effectFromWorldBindingsPost :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (left, right : SystemState name key value world error) ->
  worldState left = worldState right ->
  bindings (registry left) = bindings (registry right) ->
  EffectStateRelated keyEq (projectEffectState @{nameEq} left)
    (projectEffectState @{nameEq} right)
effectFromWorldBindingsPost nameEq keyEq
  (MkSystemState leftWorld (MkCoeffectContext leftEntries leftUnique))
  (MkSystemState rightWorld (MkCoeffectContext rightEntries rightUnique))
  worldSame entriesSame = case worldSame of
    Refl => case entriesSame of
      Refl => MkEffectStateRelated Refl (\actor =>
        effectTableReproofPost nameEq actor leftWorld rightEntries leftUnique
          rightUnique)

0 postClosePlanExactBoundary :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  GenerationEnvironmentNamesUnique live ->
  (boundary : PostCloseSelectedBoundary name key world error value nameEq keyEq
    selected registered ordinal live original survivor) ->
  NoEpisodeReplayBoundary name key world error value nameEq keyEq registered live
    original
    (plannedSystemState original
      (completePlanResult (postClosePlan boundary)))
postClosePlanExactBoundary nameEq keyEq unique boundary =
  let 0 plannedWellFormed = inactivePlanPreservesWellFormed nameEq keyEq
        (worldState original) (registry original)
        (planTarget (completePlanResult (postClosePlan boundary)))
        (inactiveLeafPlan (completePlanResult (postClosePlan boundary)))
        (postCloseOriginalWellFormed boundary)
  in case original of
    MkSystemState ambient source =>
      MkNoEpisodeReplayBoundary ambient source Refl (postClosePlan boundary)
        Refl Refl unique (postCloseOriginalWellFormed boundary)
        plannedWellFormed

0 inactiveForeignPost :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (action : Action name key value world error) ->
  Not (selected = actionOwner action) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} action before = Just (tag, afterState) ->
  InactiveFiberAt name key world error value nameEq selected before ->
  InactiveFiberAt name key world error value nameEq selected afterState
inactiveForeignPost nameEq keyEq selected action distinct before afterState tag
  raw (MkInactiveFiberAt component parent retiredFlag table outcome found) =
    let 0 lookupSame = systemLocalUpdateForeign nameEq selected
          (actionOwner action) distinct before afterState
          (applyActionLocalUpdate nameEq keyEq action before afterState tag raw)
    in MkInactiveFiberAt component parent retiredFlag table outcome
      (trans lookupSame found)

0 lookupFiberFromRuntimeBindings :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {fiber : Fiber name key value world error} ->
  (nameEq : DecEq name) -> (actor : name) ->
  (left, right : Registry name key value world error) ->
  bindings left = bindings right ->
  lookupFiber @{nameEq} actor right = Just fiber ->
  lookupFiber @{nameEq} actor left = Just fiber
lookupFiberFromRuntimeBindings nameEq actor left right bindingsSame rightFound =
  trans (lookupFiberAsEntries nameEq actor left)
    (trans (cong (lookupEntries @{nameEq} actor) bindingsSame)
      (trans (sym (lookupFiberAsEntries nameEq actor right)) rightFound))

0 systemEtaPost : (state : SystemState name key value world error) ->
  MkSystemState (worldState state) (registry state) = state
systemEtaPost (MkSystemState ambient fibers) = Refl

public export
record PostCloseOrchestrationStep
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (selected : name)
  (registered : List (RegistrationGeneration name))
  (nextOrdinal : Nat) (nextLive : GenerationEnvironment name)
  (action : Action name key value world error)
  (originalAfter, survivorBefore : SystemState name key value world error) where
  constructor MkPostCloseOrchestrationStep
  postCloseOrchestrationNamed : NamedTransition name key world error value action
    survivorBefore
  0 postCloseOrchestrationFires : fireNamed nameEq keyEq action survivorBefore =
    Just postCloseOrchestrationNamed
  0 postCloseOrchestrationBoundary : PostCloseSelectedBoundary name key world
    error value nameEq keyEq selected registered nextOrdinal nextLive
    originalAfter (namedAfter postCloseOrchestrationNamed)

packageForeignPostCloseOrchestration :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  GenerationEnvironmentNamesUnique live ->
  (action : Action name key value world error) ->
  (orchestration : isLifecycleAction action = False) ->
  (actorDistinct : Not (actionOwner action = selected)) ->
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
  CurrentRegisteredInactiveFibers name key world error value nameEq registered
    live original ->
  CurrentRegisteredEmptyTables name key world error value nameEq registered live
    original ->
  (boundary : PostCloseSelectedBoundary name key world error value nameEq keyEq
    selected registered ordinal live original survivor) ->
  (exactStep : RetainedNoEpisodeBoundaryStep name key world error value nameEq
    keyEq registered
    (advanceGenerationEnvironment @{nameEq} ordinal action live) action tag
    originalAfter
    (plannedSystemState original
      (completePlanResult (postClosePlan boundary)))) ->
  (control : ForeignOrchestrationControlReplay name key world error value nameEq
    keyEq selected action (namedTag (retainedBoundaryNamed exactStep))
    (namedAfter (retainedBoundaryNamed exactStep)) survivor) ->
  PostCloseOrchestrationStep name key world error value nameEq keyEq selected
    registered (S ordinal)
    (advanceGenerationEnvironment @{nameEq} ordinal action live)
    action originalAfter survivor
packageForeignPostCloseOrchestration protocol nameEq keyEq selected registered
  ordinal live unique action orchestration actorDistinct original originalAfter
  originalFinal survivor tag checked rest discipline retained noBegin
  sourceInactive sourceEmpty boundary exactStep control =
    let 0 planRaw = namedFireProjectsRaw nameEq keyEq action (plannedSystemState original
          (completePlanResult (postClosePlan boundary))) (retainedBoundaryNamed exactStep)
          (retainedBoundaryFires exactStep)
        controlAtNamed : ForeignOrchestrationControlReplay name key world error
          value nameEq keyEq selected action
          (namedTag (retainedBoundaryNamed exactStep))
          (namedAfter (retainedBoundaryNamed exactStep)) survivor
        controlAtNamed = control
        0 planChecked : (checkedApplyAction @{nameEq} @{keyEq} action
          (plannedSystemState original
            (completePlanResult (postClosePlan boundary))) =
          Just (namedTag (retainedBoundaryNamed exactStep),
            namedAfter (retainedBoundaryNamed exactStep)))
        planChecked = rewrite planRaw in
          rewrite survivorBoundaryWellFormed (retainedNextBoundary exactStep) in
          Refl
        0 nextHeadEffects : (EffectStateRelated keyEq
          (projectEffectState @{nameEq} (namedAfter
            (retainedBoundaryNamed exactStep)))
          (projectEffectState @{nameEq}
            (foreignControlAfter controlAtNamed)))
        nextHeadEffects = postCloseOrchestrationEffects nameEq keyEq action
          orchestration (namedTag (retainedBoundaryNamed exactStep)) (plannedSystemState original
          (completePlanResult (postClosePlan boundary))) (namedAfter (retainedBoundaryNamed exactStep))
          survivor (foreignControlAfter controlAtNamed) planChecked
          (foreignControlChecked controlAtNamed) (postCloseEffects boundary)
        nextPackage : RetainedNextPlanPackage name key world error value nameEq
          registered
          (advanceGenerationEnvironment @{nameEq} ordinal action live)
          originalAfter (namedAfter (retainedBoundaryNamed exactStep))
        nextPackage = retainedStepNextPlanPackage exactStep
        nextPlan : CompleteCurrentRegisteredPlanResult name key world error value
          nameEq registered
          (advanceGenerationEnvironment @{nameEq} ordinal action live)
          (registry originalAfter)
        nextPlan = retainedPackagePlan nextPackage
        0 originalWorldToBoundary : (worldState originalAfter =
          boundaryAmbient (retainedNextBoundary exactStep))
        originalWorldToBoundary = cong worldState
          (originalBoundaryShape (retainedNextBoundary exactStep))
        0 nextWorldSame : (worldState
              (plannedSystemState originalAfter
                (completePlanResult nextPlan)) =
            worldState (namedAfter (retainedBoundaryNamed exactStep)))
        nextWorldSame = trans originalWorldToBoundary
          (sym (survivorBoundaryAmbient (retainedNextBoundary exactStep)))
        0 nextPlanToNamed : (EffectStateRelated keyEq
          (projectEffectState @{nameEq}
            (plannedSystemState originalAfter (completePlanResult nextPlan)))
          (projectEffectState @{nameEq}
            (namedAfter (retainedBoundaryNamed exactStep))))
        nextPlanToNamed = effectFromWorldBindingsPost nameEq keyEq
          (plannedSystemState originalAfter (completePlanResult nextPlan))
          (namedAfter (retainedBoundaryNamed exactStep)) nextWorldSame
          (retainedPackageBindings nextPackage)
        0 nextEffects : EffectStateRelated keyEq
          (projectEffectState @{nameEq}
            (plannedSystemState originalAfter (completePlanResult nextPlan)))
          (projectEffectState @{nameEq} (foreignControlAfter controlAtNamed))
        nextEffects = effectTransitivePostOrchestration
          nextPlanToNamed nextHeadEffects
        0 nextControls : SelectedOrderedRegistryControlsRelated name key world
          error value selected
          (bindings (planTarget (completePlanResult nextPlan)))
          (bindings (registry (foreignControlAfter controlAtNamed)))
        nextControls = selectedOrderedTransport
          (sym (retainedPackageBindings nextPackage)) Refl
          (foreignControlOrdered controlAtNamed)
        0 selectedDifferent : Not (selected = actionOwner action)
        selectedDifferent same = actorDistinct (sym same)
        0 namedSelectedInactive : (InactiveFiberAt name key world error value
          nameEq selected (namedAfter (retainedBoundaryNamed exactStep)))
        namedSelectedInactive = inactiveForeignPost nameEq keyEq selected action
          selectedDifferent (plannedSystemState original
          (completePlanResult (postClosePlan boundary))) (namedAfter (retainedBoundaryNamed exactStep))
          (namedTag (retainedBoundaryNamed exactStep)) planRaw (postClosePlanSelectedInactive boundary)
        0 nextPlanSelectedInactive : InactiveFiberAt name key world error value
          nameEq selected
          (plannedSystemState originalAfter (completePlanResult nextPlan))
        nextPlanSelectedInactive = case namedSelectedInactive of
          MkInactiveFiberAt component parent retiredFlag table outcome found =>
            MkInactiveFiberAt component parent retiredFlag table outcome
              (lookupFiberFromRuntimeBindings nameEq selected
                (planTarget (completePlanResult nextPlan))
                (registry (namedAfter (retainedBoundaryNamed exactStep)))
                (retainedPackageBindings nextPackage) found)
        0 nextClean : (SelectedSurvivorCleanInactive name key world error value
          nameEq selected (foreignControlAfter controlAtNamed))
        nextClean = foreignActionPreservesCleanInactive nameEq keyEq selected
          action actorDistinct survivor (foreignControlAfter controlAtNamed)
          (namedTag (retainedBoundaryNamed exactStep)) (foreignControlRaw controlAtNamed)
          (postCloseCleanInactive boundary)
        0 raw : (applyAction @{nameEq} @{keyEq} action original =
          Just (tag, originalAfter))
        raw = checkedActionProjects nameEq keyEq action original originalAfter
          tag checked
        0 nextInactive : (CurrentRegisteredInactiveFibers name key world error
          value nameEq registered
          (advanceGenerationEnvironment @{nameEq} ordinal action live)
          originalAfter)
        nextInactive = currentRegisteredInactiveStep nameEq keyEq registered
          ordinal live unique action original originalAfter tag raw noBegin
          sourceInactive
        0 nextEmpty : (CurrentRegisteredEmptyTables name key world error value
          nameEq registered
          (advanceGenerationEnvironment @{nameEq} ordinal action live)
          originalAfter)
        nextEmpty = currentRegisteredEmptyTableStep nameEq keyEq registered
          ordinal live unique action original originalAfter tag raw noBegin
          sourceInactive sourceEmpty
        0 nextUnique : (GenerationEnvironmentNamesUnique
          (advanceGenerationEnvironment @{nameEq} ordinal action live))
        nextUnique = advanceGenerationEnvironmentPreservesUnique nameEq ordinal
          action live unique
        0 nextPlanEmpty : (EmptyTableInactivePlan name key world error value
          nameEq (inactiveLeafPlan (completePlanResult nextPlan)))
        nextPlanEmpty = completeCurrentRegisteredPlanHasEmptyTables nameEq
          registered (advanceGenerationEnvironment @{nameEq} ordinal action live)
          nextUnique (worldState originalAfter) (registry originalAfter) nextPlan
          nextEmpty
        0 nextOriginalWf : (registryWellFormed @{nameEq} @{keyEq}
          originalAfter = True)
        nextOriginalWf = preservationTheoremProof nameEq keyEq action original
          originalAfter tag (postCloseOriginalWellFormed boundary) raw
        0 nextSurvivorWf : (registryWellFormed @{nameEq} @{keyEq}
          (foreignControlAfter controlAtNamed) = True)
        nextSurvivorWf = preservationTheoremProof nameEq keyEq action survivor
          (foreignControlAfter controlAtNamed) (namedTag (retainedBoundaryNamed exactStep))
          (postCloseSurvivorWellFormed boundary)
          (foreignControlRaw controlAtNamed)
        0 nextBoundary : (PostCloseSelectedBoundary name key world error value
          nameEq keyEq selected registered (S ordinal)
          (advanceGenerationEnvironment @{nameEq} ordinal action live)
          originalAfter (foreignControlAfter controlAtNamed))
        nextBoundary = MkPostCloseSelectedBoundary nextPlan nextEffects
          nextControls nextPlanSelectedInactive nextClean nextOriginalWf
          nextSurvivorWf nextInactive nextEmpty nextPlanEmpty
        namedReplay = foreignOrchestrationReplayNamed nameEq keyEq action survivor
          controlAtNamed
    in case namedReplay of
      MkNamedForeignOrchestrationReplay named fires afterSame =>
        MkPostCloseOrchestrationStep named fires
          (replace
            {p = \observed => PostCloseSelectedBoundary name key world error value
              nameEq keyEq selected registered (S ordinal)
              (advanceGenerationEnvironment @{nameEq} ordinal action live)
              originalAfter observed}
            (sym afterSame) nextBoundary)

||| Replay one retained foreign orchestration head while preserving the
||| selected-static post-close quotient.
public export
0 retainedForeignPostCloseOrchestration :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  GenerationEnvironmentNamesUnique live ->
  (action : Action name key value world error) ->
  (orchestration : isLifecycleAction action = False) ->
  (actorDistinct : Not (actionOwner action = selected)) ->
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
retainedForeignPostCloseOrchestration protocol nameEq keyEq selected registered
  ordinal live unique action orchestration actorDistinct original originalAfter
  originalFinal survivor tag checked rest discipline retained noBegin boundary =
    let exactBefore = postClosePlanExactBoundary nameEq keyEq unique boundary
        exactStep = retainedSuffixHeadPreservesNoEpisodeBoundary protocol nameEq
          keyEq registered ordinal live action original
          (plannedSystemState original
            (completePlanResult (postClosePlan boundary)))
          exactBefore tag checked rest discipline retained
        planRaw = namedFireProjectsRaw nameEq keyEq action
          (plannedSystemState original
            (completePlanResult (postClosePlan boundary)))
          (retainedBoundaryNamed exactStep) (retainedBoundaryFires exactStep)
    in case action of
      OInsert actor parent component =>
        let control = replayForeignInsertControls nameEq keyEq selected actor
              actorDistinct parent component (worldState original)
              (worldState survivor)
              (planTarget (completePlanResult (postClosePlan boundary)))
              (registry survivor) (postCloseControls boundary)
              (namedTag (retainedBoundaryNamed exactStep)) (namedAfter (retainedBoundaryNamed exactStep)) planRaw
              (postCloseSurvivorWellFormed boundary)
        in packageForeignPostCloseOrchestration protocol nameEq keyEq selected
          registered ordinal live unique action orchestration actorDistinct
          original originalAfter originalFinal survivor tag checked rest
          discipline retained noBegin (postCloseCurrentInactive boundary)
          (postCloseCurrentEmpty boundary) boundary exactStep
          (replace
            {p = \state => ForeignOrchestrationControlReplay name key world error
              value nameEq keyEq selected action (namedTag (retainedBoundaryNamed exactStep))
              (namedAfter (retainedBoundaryNamed exactStep)) state}
            (systemEtaPost survivor) control)
      ORetire actor =>
        let control = replayForeignRetireControls nameEq keyEq selected actor
              actorDistinct (worldState original) (worldState survivor)
              (planTarget (completePlanResult (postClosePlan boundary)))
              (registry survivor) (postCloseControls boundary)
              (namedTag (retainedBoundaryNamed exactStep)) (namedAfter (retainedBoundaryNamed exactStep)) planRaw
              (postCloseSurvivorWellFormed boundary)
        in packageForeignPostCloseOrchestration protocol nameEq keyEq selected
          registered ordinal live unique action orchestration actorDistinct
          original originalAfter originalFinal survivor tag checked rest
          discipline retained noBegin (postCloseCurrentInactive boundary)
          (postCloseCurrentEmpty boundary) boundary exactStep
          (replace
            {p = \state => ForeignOrchestrationControlReplay name key world error
              value nameEq keyEq selected action (namedTag (retainedBoundaryNamed exactStep))
              (namedAfter (retainedBoundaryNamed exactStep)) state}
            (systemEtaPost survivor) control)
      ORemove actor =>
        let control = replayForeignRemoveControls nameEq keyEq selected actor
              actorDistinct (worldState original) (worldState survivor)
              (planTarget (completePlanResult (postClosePlan boundary)))
              (registry survivor) (postCloseControls boundary)
              (namedTag (retainedBoundaryNamed exactStep)) (namedAfter (retainedBoundaryNamed exactStep)) planRaw
              (postCloseSurvivorWellFormed boundary)
        in packageForeignPostCloseOrchestration protocol nameEq keyEq selected
          registered ordinal live unique action orchestration actorDistinct
          original originalAfter originalFinal survivor tag checked rest
          discipline retained noBegin (postCloseCurrentInactive boundary)
          (postCloseCurrentEmpty boundary) boundary exactStep
          (replace
            {p = \state => ForeignOrchestrationControlReplay name key world error
              value nameEq keyEq selected action (namedTag (retainedBoundaryNamed exactStep))
              (namedAfter (retainedBoundaryNamed exactStep)) state}
            (systemEtaPost survivor) control)
      LBegin actor => case orchestration of Refl impossible
      LAdvance actor => case orchestration of Refl impossible
      LDivert actor => case orchestration of Refl impossible
      LLeave actor => case orchestration of Refl impossible
      LUnload actor => case orchestration of Refl impossible
