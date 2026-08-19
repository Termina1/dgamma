module DGamma.CP4DeletionSelectedDeletedCore

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionEmptyTableInvariant
import DGamma.CP4DeletionGenerationUnique
import DGamma.CP4DeletionInactiveInvariant
import DGamma.CP4DeletionPlanBuilder
import DGamma.CP4DeletionPlanComplete
import DGamma.CP4DeletionPlanEmpty
import DGamma.CP4DeletionPlanEffects
import DGamma.CP4DeletionSelectedBoundary
import DGamma.CP4DeletionSelectedDeletedPlan
import DGamma.CP4DeletionSelectedEffectCore
import DGamma.CP4RecoveryEffectRespect
import DGamma.CP4RecoveryTrace
import Decidable.Equality

%default total

0 partialRelatedRewriteDeleted :
  leftBefore = leftAfter -> rightBefore = rightAfter ->
  PartialRelated state rel leftBefore rightBefore ->
  PartialRelated state rel leftAfter rightAfter
partialRelatedRewriteDeleted Refl Refl related = related

0 partialJustNothingDeleted :
  PartialRelated state rel (Just left) Nothing -> Void
partialJustNothingDeleted relation impossible

record RelatedAccumulatorOutput
  (name, key, world : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (selected : name)
  (handle : AccumulatorHandle key value world)
  (left, right, leftOutput : EffectState name key value world) where
  constructor MkRelatedAccumulatorOutput
  rightOutput : EffectState name key value world
  0 rightAccumulatorRuns : accumulatorEffectMap nameEq keyEq selected handle right =
    Just rightOutput
  0 accumulatorOutputsRelated : EffectStateRelated keyEq leftOutput rightOutput

0 accumulatorRunsOnRelatedInput :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (handle : AccumulatorHandle key value world) ->
  (left, right, leftOutput : EffectState name key value world) ->
  EffectStateRelated keyEq left right ->
  accumulatorEffectMap nameEq keyEq selected handle left = Just leftOutput ->
  RelatedAccumulatorOutput name key world value nameEq keyEq selected handle left
    right leftOutput
accumulatorRunsOnRelatedInput nameEq keyEq selected handle left right leftOutput
  related leftRuns
  with (accumulatorEffectMap nameEq keyEq selected handle right) proof rightRuns
  accumulatorRunsOnRelatedInput nameEq keyEq selected handle left right leftOutput
    related leftRuns | Nothing = void (partialJustNothingDeleted
      (partialRelatedRewriteDeleted leftRuns rightRuns
        (accumulatorEffectMapRespects nameEq keyEq selected handle left right
          related)))
  accumulatorRunsOnRelatedInput nameEq keyEq selected handle left right leftOutput
    related leftRuns | Just output = MkRelatedAccumulatorOutput output rightRuns
      (case partialRelatedRewriteDeleted leftRuns rightRuns
        (accumulatorEffectMapRespects nameEq keyEq selected handle left right
          related) of
        PartialDefined observed => observed)

0 projectEffectTableReproofDeleted :
  (nameEq : DecEq name) -> (actor : name) -> (ambient : world) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (leftUnique, rightUnique : UniqueKeys (bindingKeys entries)) ->
  bindings (effectTables (projectEffectState @{nameEq}
    (the (SystemState name key value world error)
      (MkSystemState ambient (MkCoeffectContext entries leftUnique)))) actor) =
  bindings (effectTables (projectEffectState @{nameEq}
    (the (SystemState name key value world error)
      (MkSystemState ambient (MkCoeffectContext entries rightUnique)))) actor)
projectEffectTableReproofDeleted nameEq actor ambient entries leftUnique
  rightUnique with (lookupEntries @{nameEq} actor entries)
  projectEffectTableReproofDeleted nameEq actor ambient entries leftUnique
    rightUnique | Nothing = Refl
  projectEffectTableReproofDeleted nameEq actor ambient entries leftUnique
    rightUnique | Just fiber = Refl

0 projectEffectAcrossBindings :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (leftAmbient, rightAmbient : world) ->
  (left, right : Registry name key value world error) ->
  leftAmbient = rightAmbient -> bindings left = bindings right ->
  EffectStateRelated keyEq
    (projectEffectState @{nameEq}
      (the (SystemState name key value world error)
        (MkSystemState leftAmbient left)))
    (projectEffectState @{nameEq}
      (the (SystemState name key value world error)
        (MkSystemState rightAmbient right)))
projectEffectAcrossBindings nameEq keyEq leftAmbient rightAmbient
  (MkCoeffectContext leftEntries leftUnique)
  (MkCoeffectContext rightEntries rightUnique) ambientSame entriesSame =
    case ambientSame of
      Refl => case entriesSame of
        Refl => MkEffectStateRelated Refl (\actor =>
          projectEffectTableReproofDeleted nameEq actor leftAmbient rightEntries
            leftUnique rightUnique)

||| One skipped foreign R orchestration step preserves the selected effect/control
||| boundary whenever the old and new complete plans erase only empty leaves and
||| reach the same ordered target bindings.  The selected accumulator is moved
||| across the pointwise before/after effect relation; no retained survivor action
||| is fabricated.
public export
0 deletedForeignStepPreservesSelectedBoundary :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  {wholeFirst, wholeLast : SystemState name key value world error} ->
  (whole : Transitions wholeFirst wholeLast) ->
  (survivor : SystemState name key value world error) ->
  (boundary : SelectedEpisodeReplayBoundary name key world error value nameEq
    keyEq selected registered ordinal live whole before survivor) ->
  Not (selected = actionOwner action) ->
  worldState afterState = worldState before ->
  (nextPlan : CompleteCurrentRegisteredPlanResult name key world error value
    nameEq registered
    (advanceGenerationEnvironment @{nameEq} ordinal action live)
    (registry afterState)) ->
  bindings (planTarget (completePlanResult nextPlan)) =
    bindings (planTarget (completePlanResult
      (selectedBoundaryPlan boundary))) ->
  EmptyTableInactivePlan name key world error value nameEq
    (inactiveLeafPlan (completePlanResult
      (selectedBoundaryPlan boundary))) ->
  EmptyTableInactivePlan name key world error value nameEq
    (inactiveLeafPlan (completePlanResult nextPlan)) ->
  SelectedEpisodeReplayBoundary name key world error value nameEq keyEq selected
    registered (S ordinal)
    (advanceGenerationEnvironment @{nameEq} ordinal action live)
    whole afterState survivor
deletedForeignStepPreservesSelectedBoundary
  nameEq keyEq selected registered ordinal live action tag
  (MkSystemState beforeAmbient beforeRegistry)
  (MkSystemState afterAmbient afterRegistry)
  checked whole survivor
  (MkSelectedEpisodeReplayBoundary
    (MkSelectedEffectReplayBoundary sourceModel oldRecovered oldRuns
      survivorToOld)
    oldComplete oldOrdered survivorCleanInactive beforeWellFormed
    survivorWellFormed)
  selectedDistinct sameWorld nextComplete targetBindings oldEmpty nextEmpty =
    let before : SystemState name key value world error
        before = MkSystemState beforeAmbient beforeRegistry
        afterState : SystemState name key value world error
        afterState = MkSystemState afterAmbient afterRegistry
        0 oldTarget : Registry name key value world error
        oldTarget = planTarget (completePlanResult oldComplete)
        0 nextTarget : Registry name key value world error
        nextTarget = planTarget (completePlanResult nextComplete)
        0 beforeToOldTarget : EffectStateRelated keyEq
          (projectEffectState @{nameEq} before)
          (projectEffectState @{nameEq}
            (the (SystemState name key value world error)
              (MkSystemState (worldState before) oldTarget)))
        beforeToOldTarget = emptyInactivePlanPreservesEffects nameEq keyEq
          (worldState before) (registry before) oldTarget
          (inactiveLeafPlan (completePlanResult oldComplete)) oldEmpty
        0 oldTargetToNextTarget : EffectStateRelated keyEq
          (projectEffectState @{nameEq}
            (the (SystemState name key value world error)
              (MkSystemState (worldState before) oldTarget)))
          (projectEffectState @{nameEq}
            (the (SystemState name key value world error)
              (MkSystemState (worldState afterState) nextTarget)))
        oldTargetToNextTarget = projectEffectAcrossBindings nameEq keyEq
          (worldState before) (worldState afterState) oldTarget nextTarget
          (sym sameWorld) (sym targetBindings)
        0 nextTargetToAfter : EffectStateRelated keyEq
          (projectEffectState @{nameEq}
            (the (SystemState name key value world error)
              (MkSystemState (worldState afterState) nextTarget)))
          (projectEffectState @{nameEq} afterState)
        nextTargetToAfter = symmetric (EffectStateEquivalence keyEq)
          (emptyInactivePlanPreservesEffects nameEq keyEq
            (worldState afterState) (registry afterState) nextTarget
            (inactiveLeafPlan (completePlanResult nextComplete)) nextEmpty)
        0 beforeToAfter : EffectStateRelated keyEq
          (projectEffectState @{nameEq} before)
          (projectEffectState @{nameEq} afterState)
        beforeToAfter = transitive (EffectStateEquivalence keyEq)
          beforeToOldTarget
          (transitive (EffectStateEquivalence keyEq) oldTargetToNextTarget
            nextTargetToAfter)
        0 nextModel : AccumulatorModel name key world error value nameEq keyEq
          selected whole afterState
        nextModel = foreignStepPreservesAccumulatorModel nameEq keyEq selected
          action tag before afterState whole checked selectedDistinct sourceModel
        0 nextMapAtBefore :
          (accumulatorEffectMap nameEq keyEq selected (modelHandle nextModel)
              (projectEffectState @{nameEq} before) =
            accumulatorEffectMap nameEq keyEq selected (modelHandle sourceModel)
              (projectEffectState @{nameEq} before))
        nextMapAtBefore = foreignStepPreservesAccumulatorMap nameEq keyEq
          selected action tag before afterState whole checked selectedDistinct
          sourceModel (projectEffectState @{nameEq} before)
        0 nextRunsAtBefore :
          (accumulatorEffectMap nameEq keyEq selected (modelHandle nextModel)
              (projectEffectState @{nameEq} before) = Just oldRecovered)
        nextRunsAtBefore = trans nextMapAtBefore oldRuns
        0 output : RelatedAccumulatorOutput name key world value nameEq keyEq
          selected (modelHandle nextModel) (projectEffectState @{nameEq} before)
          (projectEffectState @{nameEq} afterState) oldRecovered
        output = accumulatorRunsOnRelatedInput nameEq keyEq selected
          (modelHandle nextModel) (projectEffectState @{nameEq} before)
          (projectEffectState @{nameEq} afterState) oldRecovered beforeToAfter
          nextRunsAtBefore
    in case output of
      MkRelatedAccumulatorOutput nextRecovered nextRuns oldToNext =>
        let 0 survivorToNext : EffectStateRelated keyEq
              (projectEffectState @{nameEq} survivor) nextRecovered
            survivorToNext = transitive (EffectStateEquivalence keyEq)
              survivorToOld oldToNext
            0 nextEffects : SelectedEffectReplayBoundary name key world error
              value nameEq keyEq selected whole afterState survivor
            nextEffects = MkSelectedEffectReplayBoundary nextModel nextRecovered
              nextRuns survivorToNext
            0 nextOrdered : SelectedOrderedRegistryControlsRelated name key world
              error value selected
              (bindings (planTarget (completePlanResult nextComplete)))
              (bindings (registry survivor))
            nextOrdered = selectedOrderedTransport (sym targetBindings) Refl
              oldOrdered
            0 raw : (applyAction @{nameEq} @{keyEq} action before =
              Just (tag, afterState))
            raw = checkedActionProjects nameEq keyEq action before afterState tag
              checked
            0 afterWellFormed : (registryWellFormed @{nameEq} @{keyEq}
              afterState = True)
            afterWellFormed = preservationTheoremProof nameEq keyEq action before
              afterState tag beforeWellFormed raw
        in MkSelectedEpisodeReplayBoundary nextEffects nextComplete nextOrdered
          survivorCleanInactive afterWellFormed survivorWellFormed

||| Derive empty-table evidence for the action-updated complete plan from the old
||| empty plan and the existing one-step exact-generation invariant.  This keeps
||| emptiness as derived evidence rather than adding a field to the selected
||| boundary record.
public export
0 deletedStepGivesNextEmptyPlan :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (unique : GenerationEnvironmentNamesUnique live) ->
  (action : Action name key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (raw : applyAction @{nameEq} @{keyEq} action before = Just (tag, afterState)) ->
  (noBegin : IsBeginAction action ->
    GenerationOwnedActor nameEq registered ordinal live action -> Void) ->
  (oldPlan : CompleteCurrentRegisteredPlanResult name key world error value
    nameEq registered live (registry before)) ->
  EmptyTableInactivePlan name key world error value nameEq
    (inactiveLeafPlan (completePlanResult oldPlan)) ->
  (nextPlan : CompleteCurrentRegisteredPlanResult name key world error value
    nameEq registered
    (advanceGenerationEnvironment @{nameEq} ordinal action live)
    (registry afterState)) ->
  EmptyTableInactivePlan name key world error value nameEq
    (inactiveLeafPlan (completePlanResult nextPlan))
deletedStepGivesNextEmptyPlan nameEq keyEq registered ordinal live unique action
  before afterState tag raw noBegin oldPlan oldEmpty nextPlan =
    let 0 sourceInactive = completeEmptyPlanGivesCurrentRegisteredInactive nameEq
          registered live before oldPlan oldEmpty
        0 sourceEmpty = completeEmptyPlanGivesCurrentRegisteredEmptyTables nameEq
          registered live before oldPlan oldEmpty
        0 nextEmpty = currentRegisteredEmptyTableStep nameEq keyEq registered
          ordinal live unique action before afterState tag raw noBegin sourceInactive
          sourceEmpty
        0 nextUnique = advanceGenerationEnvironmentPreservesUnique nameEq ordinal
          action live unique
    in DGamma.CP4DeletionPlanEmpty.completeCurrentRegisteredPlanHasEmptyTables
      nameEq registered
      (advanceGenerationEnvironment @{nameEq} ordinal action live) nextUnique
      (worldState afterState) (registry afterState) nextPlan nextEmpty
