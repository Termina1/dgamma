module DGamma.CP4DeletionPostCloseDeleted

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionBoundaryDeleted
import DGamma.CP4DeletionBoundaryPlan
import DGamma.CP4DeletionEmptyTableInvariant
import DGamma.CP4DeletionGenerationBounds
import DGamma.CP4DeletionGenerationUnique
import DGamma.CP4DeletionInactiveInvariant
import DGamma.CP4DeletionNoEpisodeReplay
import DGamma.CP4DeletionPlanBuilder
import DGamma.CP4DeletionPlanComplete
import DGamma.CP4DeletionPlanEmpty
import DGamma.CP4DeletionPlanEffects
import DGamma.CP4DeletionPostCloseOrchestration
import DGamma.CP4DeletionRelationalBoundary
import DGamma.CP4DeletionRelationalSuffixFold
import DGamma.CP4DeletionSelectedBoundary
import DGamma.CP4DeletionSelectedCloseBoundary
import DGamma.CP4DeletionSelectedDeletedCore
import DGamma.CP4RuntimeBindings
import Decidable.Equality

%default total

0 lookupFiberAcrossBindingsPost :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (actor : name) ->
  (left, right : Registry name key value world error) ->
  bindings left = bindings right ->
  lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} actor left =
  lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} actor right
lookupFiberAcrossBindingsPost nameEq actor left right same =
  trans (lookupFiberAsEntries nameEq actor left)
    (trans (cong (lookupEntries @{nameEq} actor) same)
      (sym (lookupFiberAsEntries nameEq actor right)))

0 inactiveAcrossBindingsPost :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (actor : name) ->
  (ambient : world) ->
  (left, right : Registry name key value world error) ->
  bindings left = bindings right ->
  InactiveFiberAt name key world error value nameEq actor
    (MkSystemState ambient right) ->
  InactiveFiberAt name key world error value nameEq actor
    (MkSystemState ambient left)
inactiveAcrossBindingsPost nameEq actor ambient left right same
  (MkInactiveFiberAt component parent retiredFlag table outcome found) =
    MkInactiveFiberAt component parent retiredFlag table outcome
      (trans (lookupFiberAcrossBindingsPost nameEq actor left right same) found)

||| A skipped current-R head updates the exact plan scaffold but leaves the
||| selected-static survivor untouched. Only current-R O-Retire/O-Remove can
||| reach this branch; the exact boundary theorem eliminates every other rule.
public export
0 deletedPostCloseStep :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  RegisteredGenerationsBornBefore registered ordinal ->
  GenerationEnvironmentNamesUnique live ->
  (action : Action name key value world error) ->
  (original, survivor : SystemState name key value world error) ->
  (boundary : PostCloseSelectedBoundary name key world error value nameEq keyEq
    selected registered ordinal live original survivor) ->
  {originalAfter : SystemState name key value world error} ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action original =
    Just (tag, originalAfter)) ->
  (deleted : GenerationOwnedActor nameEq registered ordinal live action) ->
  (noBegin : IsBeginAction action ->
    GenerationOwnedActor nameEq registered ordinal live action -> Void) ->
  PostCloseSelectedBoundary name key world error value nameEq keyEq selected
    registered (S ordinal)
    (advanceGenerationEnvironment @{nameEq} ordinal action live)
    originalAfter survivor
deletedPostCloseStep {name} {key} {world} {error} {value}
  nameEq keyEq selected registered ordinal live bornBefore unique action original
  survivor boundary tag checked deleted noBegin =
    let exactBefore = postClosePlanExactBoundary nameEq keyEq unique boundary
        exactAfter = deletedSuffixHeadPreservesNoEpisodeBoundary nameEq keyEq
          registered ordinal live bornBefore action original
          (plannedSystemState original
            (completePlanResult (postClosePlan boundary)))
          exactBefore tag checked deleted noBegin
    in case exactAfter of
      exact@(MkNoEpisodeReplayBoundary ambient source originalShape nextComplete
        survivorAmbient survivorBindings nextUnique originalWF survivorWF) =>
          case originalShape of
            Refl =>
              let 0 targetBindings : (bindings
                      (planTarget (completePlanResult nextComplete)) =
                    bindings (planTarget (completePlanResult
                      (postClosePlan boundary))))
                  targetBindings = sym survivorBindings
                  0 snapshotsSame : runtimeSnapshot
                      (plannedSystemState originalAfter
                        (completePlanResult nextComplete)) =
                    runtimeSnapshot
                      (plannedSystemState original
                        (completePlanResult (postClosePlan boundary)))
                  snapshotsSame = cong2 MkRuntimeSnapshot
                    (sym survivorAmbient) targetBindings
                  0 planEffects : EffectStateRelated keyEq
                    (projectEffectState @{nameEq}
                      (plannedSystemState originalAfter
                        (completePlanResult nextComplete)))
                    (projectEffectState @{nameEq}
                      (plannedSystemState original
                        (completePlanResult (postClosePlan boundary))))
                  planEffects = effectsEquivalent
                    (runtimeSnapshotGivesSystemEquivalent nameEq keyEq
                      (plannedSystemState originalAfter
                        (completePlanResult nextComplete))
                      (plannedSystemState original
                        (completePlanResult (postClosePlan boundary)))
                      snapshotsSame)
                  0 nextEffects : EffectStateRelated keyEq
                    (projectEffectState @{nameEq}
                      (plannedSystemState originalAfter
                        (completePlanResult nextComplete)))
                    (projectEffectState @{nameEq} survivor)
                  nextEffects = case planEffects of
                    MkEffectStateRelated firstAmbient firstTables =>
                      case postCloseEffects boundary of
                        MkEffectStateRelated secondAmbient secondTables =>
                          MkEffectStateRelated
                            (trans firstAmbient secondAmbient)
                            (\actor => trans (firstTables actor)
                              (secondTables actor))
                  0 oldControls : SelectedOrderedRegistryControlsRelated name
                    key world error value selected
                    (bindings (planTarget (completePlanResult
                      (postClosePlan boundary))))
                    (bindings (registry survivor))
                  oldControls = postCloseControls boundary
                  0 nextControls : SelectedOrderedRegistryControlsRelated name key world
                    error value selected
                    (bindings (planTarget (completePlanResult nextComplete)))
                    (bindings (registry survivor))
                  nextControls = replace
                    {p = \observed => SelectedOrderedRegistryControlsRelated name
                      key world error value selected observed
                      (bindings (registry survivor))}
                    (sym targetBindings) oldControls
                  0 nextSelectedInactive : InactiveFiberAt name key world error value
                    nameEq selected
                    (MkSystemState (worldState originalAfter)
                      (planTarget (completePlanResult nextComplete)))
                  nextSelectedInactive = inactiveAcrossBindingsPost nameEq selected
                    (worldState originalAfter) (planTarget (completePlanResult nextComplete))
                    (planTarget (completePlanResult (postClosePlan boundary)))
                    targetBindings
                    (replace
                      {p = \observed => InactiveFiberAt name key world error value nameEq
                        selected
                        (MkSystemState observed
                          (planTarget (completePlanResult (postClosePlan boundary))))}
                      survivorAmbient
                      (postClosePlanSelectedInactive boundary))
                  0 raw : (applyAction @{nameEq} @{keyEq} action original =
                    Just (tag, originalAfter))
                  raw = checkedActionProjects nameEq keyEq action original
                    originalAfter tag checked
                  0 nextInactive : CurrentRegisteredInactiveFibers name key world error
                    value nameEq registered
                    (advanceGenerationEnvironment @{nameEq} ordinal action live)
                    originalAfter
                  nextInactive = currentRegisteredInactiveStep nameEq keyEq registered
                    ordinal live unique action original originalAfter tag raw noBegin
                    (postCloseCurrentInactive boundary)
                  0 nextEmpty : CurrentRegisteredEmptyTables name key world error value
                    nameEq registered
                    (advanceGenerationEnvironment @{nameEq} ordinal action live)
                    originalAfter
                  nextEmpty = currentRegisteredEmptyTableStep nameEq keyEq registered
                    ordinal live unique action original originalAfter tag raw noBegin
                    (postCloseCurrentInactive boundary) (postCloseCurrentEmpty boundary)
                  0 nextPlanEmpty : EmptyTableInactivePlan name key world error value nameEq
                    (inactiveLeafPlan (completePlanResult nextComplete))
                  nextPlanEmpty = deletedStepGivesNextEmptyPlan nameEq keyEq registered
                    ordinal live unique action original originalAfter tag raw noBegin
                    (postClosePlan boundary) (postClosePlanEmpty boundary) nextComplete
              in MkPostCloseSelectedBoundary nextComplete
                nextEffects nextControls nextSelectedInactive
                (postCloseCleanInactive boundary)
                originalWF
                (postCloseSurvivorWellFormed boundary) nextInactive nextEmpty
                nextPlanEmpty
