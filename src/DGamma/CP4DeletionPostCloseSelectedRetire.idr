module DGamma.CP4DeletionPostCloseSelectedRetire

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionBoundaryDeleted
import DGamma.CP4DeletionBoundaryRetained
import DGamma.CP4DeletionCommuteCore
import DGamma.CP4DeletionGenerationFilter
import DGamma.CP4DeletionGenerationUnique
import DGamma.CP4DeletionInactiveInvariant
import DGamma.CP4DeletionNoEpisodeReplay
import DGamma.CP4DeletionPlanBuilder
import DGamma.CP4DeletionPlanComplete
import DGamma.CP4DeletionPostCloseEffectReplay
import DGamma.CP4DeletionPostCloseOrchestration
import DGamma.CP4DeletionRelationalBoundary
import DGamma.CP4DeletionSelectedBoundary
import DGamma.CP4DeletionSelectedCloseBoundary
import DGamma.CP4DeletionSelectedForeignOrchestration
import DGamma.CP4DeletionSelectedRetire
import DGamma.CP4RuntimeBindings
import Decidable.Equality

%default total

||| Apply O-Retire to both selected cells. Only the static selected relation is
||| needed: retirement rewrites the same immutable Boolean field on each side.
public export
0 replaySelectedRetirePostControls :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (planAmbient, survivorAmbient : world) ->
  (plan, survivor : Registry name key value world error) ->
  SelectedOrderedRegistryControlsRelated name key world error value selected
    (bindings plan) (bindings survivor) ->
  (tag : RuleTag) -> (planAfter : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq} (ORetire selected)
    (MkSystemState planAmbient plan) = Just (tag, planAfter) ->
  registryWellFormed @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error}
    (MkSystemState survivorAmbient survivor) = True ->
  ForeignOrchestrationControlReplay name key world error value nameEq keyEq
    selected (ORetire selected) tag planAfter
    (MkSystemState survivorAmbient survivor)
replaySelectedRetirePostControls nameEq keyEq selected planAmbient survivorAmbient
  plan survivor ordered tag planAfter planRaw survivorWellFormed =
    case retireSuccessView nameEq keyEq selected planAmbient plan tag planAfter
      planRaw of
      MkRetireSuccessView planFiber planFound =>
        case selectedStaticLookupFound nameEq selected plan survivor planFiber
          planFound ordered of
          MkSelectedStaticFiberFound survivorFiber survivorFound static =>
            let survivorAfter : SystemState name key value world error
                survivorAfter = MkSystemState
                  (worldState (MkSystemState survivorAmbient survivor))
                  (replaceBinding @{nameEq} selected (retireFiber survivorFiber)
                    (registry (MkSystemState survivorAmbient survivor)))
                0 survivorRaw : (applyAction @{nameEq} @{keyEq}
                  (ORetire selected) (MkSystemState survivorAmbient survivor) =
                  Just (ORetireTag, survivorAfter))
                survivorRaw = rewrite survivorFound in Refl
                0 survivorAfterWellFormed : (registryWellFormed
                  @{nameEq} @{keyEq} survivorAfter = True)
                survivorAfterWellFormed = preservationTheoremProof nameEq keyEq
                  (ORetire selected) (MkSystemState survivorAmbient survivor)
                  survivorAfter ORetireTag survivorWellFormed survivorRaw
                0 survivorChecked : (checkedApplyAction @{nameEq} @{keyEq}
                  (ORetire selected) (MkSystemState survivorAmbient survivor) =
                  Just (ORetireTag, survivorAfter))
                survivorChecked = rewrite survivorRaw in
                  rewrite survivorAfterWellFormed in Refl
                0 nextStatic : (FiberStaticRelated name key world error value
                  (retireFiber planFiber) (retireFiber survivorFiber))
                nextStatic = retireFiberStaticRelated static
                0 canonicalOrdered : (SelectedOrderedRegistryControlsRelated
                  name key world error value selected
                  (replaceEntries @{nameEq} selected (retireFiber planFiber)
                    (bindings plan))
                  (replaceEntries @{nameEq} selected (retireFiber survivorFiber)
                    (bindings survivor)))
                canonicalOrdered = selectedOrderedReplaceSelectedBoth nameEq
                  selected (retireFiber planFiber) (retireFiber survivorFiber)
                  nextStatic (bindings plan) (bindings survivor) ordered
                0 planBindings : (bindings
                  (replaceBinding @{nameEq} selected (retireFiber planFiber)
                    plan) = replaceEntries @{nameEq} selected
                      (retireFiber planFiber) (bindings plan))
                planBindings = replaceBindingRuntimeBindings nameEq selected
                  (retireFiber planFiber) plan
                0 survivorBindings : (bindings
                  (replaceBinding @{nameEq} selected (retireFiber survivorFiber)
                    survivor) = replaceEntries @{nameEq} selected
                      (retireFiber survivorFiber) (bindings survivor))
                survivorBindings = replaceBindingRuntimeBindings nameEq
                  selected (retireFiber survivorFiber) survivor
                0 finalOrdered : (SelectedOrderedRegistryControlsRelated name
                  key world error value selected
                  (bindings (replaceBinding @{nameEq} selected
                    (retireFiber planFiber) plan))
                  (bindings (replaceBinding @{nameEq} selected
                    (retireFiber survivorFiber) survivor)))
                finalOrdered = selectedOrderedTransport (sym planBindings)
                  (sym survivorBindings) canonicalOrdered
            in MkForeignOrchestrationControlReplay survivorAfter survivorRaw
              survivorChecked finalOrdered

0 inactiveAfterSelectedRetire :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (ORetire selected) before =
    Just (tag, afterState) ->
  InactiveFiberAt name key world error value nameEq selected before ->
  InactiveFiberAt name key world error value nameEq selected afterState
inactiveAfterSelectedRetire nameEq keyEq selected
  (MkSystemState ambient source) afterState tag raw
  (MkInactiveFiberAt component parent retiredFlag table outcome inactiveFound) =
    case retireSuccessView nameEq keyEq selected ambient source tag afterState raw
      of
      MkRetireSuccessView fiber found =>
        let 0 sameFiber = justInjective (trans (sym found) inactiveFound)
        in case sameFiber of
          Refl => MkInactiveFiberAt component parent True table outcome
            (lookupReplacedFiber selected fiber (retireFiber fiber) source found)

0 cleanAfterSelectedRetire :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (ORetire selected) before =
    Just (tag, afterState) ->
  SelectedSurvivorCleanInactive name key world error value nameEq selected
    before ->
  SelectedSurvivorCleanInactive name key world error value nameEq selected
    afterState
cleanAfterSelectedRetire nameEq keyEq selected
  (MkSystemState ambient source) afterState tag raw
  (SelectedCleanInactiveWitness component parent retiredFlag table cleanFound) =
    case retireSuccessView nameEq keyEq selected ambient source tag afterState raw
      of
      MkRetireSuccessView fiber found =>
        let 0 sameFiber = justInjective (trans (sym found) cleanFound)
        in case sameFiber of
          Refl => SelectedCleanInactiveWitness component parent True table
            (lookupReplacedFiber selected fiber (retireFiber fiber) source found)

||| Replay a selected O-Retire after the deleted episode has closed, retaining
||| the selected-static quotient for subsequent foreign actions.
public export
0 retainedSelectedPostCloseRetire :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  GenerationEnvironmentNamesUnique live ->
  (original, originalAfter, originalFinal, survivor :
    SystemState name key value world error) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} (ORetire selected) original =
    Just (ORetireTag, originalAfter)) ->
  (rest : Transitions originalAfter originalFinal) ->
  RegistrationStepDiscipline protocol nameEq (ORetire selected) original rest ->
  (retained : Not (GenerationOwnedActor nameEq registered ordinal live
    (the (Action name key value world error) (ORetire selected)))) ->
  (noBegin : IsBeginAction
      (the (Action name key value world error) (ORetire selected)) ->
    GenerationOwnedActor nameEq registered ordinal live
      (the (Action name key value world error) (ORetire selected)) -> Void) ->
  (boundary : PostCloseSelectedBoundary name key world error value nameEq keyEq
    selected registered ordinal live original survivor) ->
  PostCloseOrchestrationStep name key world error value nameEq keyEq selected
    registered (S ordinal) live (ORetire selected) originalAfter survivor
retainedSelectedPostCloseRetire protocol nameEq keyEq selected registered ordinal
  live unique original originalAfter originalFinal survivor checked rest
  discipline retained noBegin boundary =
    let exactBefore = postClosePlanExactBoundary nameEq keyEq unique boundary
        exactStep = retainedSuffixHeadPreservesNoEpisodeBoundary protocol nameEq
          keyEq registered ordinal live (ORetire selected) original
          (plannedSystemState original
            (completePlanResult (postClosePlan boundary)))
          exactBefore ORetireTag checked rest discipline retained
        0 planRaw = namedFireProjectsRaw nameEq keyEq (ORetire selected)
          (plannedSystemState original
            (completePlanResult (postClosePlan boundary)))
          (retainedBoundaryNamed exactStep) (retainedBoundaryFires exactStep)
        control = replaySelectedRetirePostControls nameEq keyEq selected
          (worldState original) (worldState survivor)
          (planTarget (completePlanResult (postClosePlan boundary)))
          (registry survivor) (postCloseControls boundary)
          (namedTag (retainedBoundaryNamed exactStep))
          (namedAfter (retainedBoundaryNamed exactStep)) planRaw
          (postCloseSurvivorWellFormed boundary)
        controlExact : ForeignOrchestrationControlReplay name key world error
          value nameEq keyEq selected (ORetire selected)
          (namedTag (retainedBoundaryNamed exactStep))
          (namedAfter (retainedBoundaryNamed exactStep)) survivor
        controlExact = replace
          {p = \state => ForeignOrchestrationControlReplay name key world error
            value nameEq keyEq selected (ORetire selected)
            (namedTag (retainedBoundaryNamed exactStep))
            (namedAfter (retainedBoundaryNamed exactStep)) state}
          (systemEtaPost survivor) control
        0 planInactive : (InactiveFiberAt name key world error value nameEq
          selected (namedAfter (retainedBoundaryNamed exactStep)))
        planInactive = inactiveAfterSelectedRetire nameEq keyEq selected
          (plannedSystemState original
            (completePlanResult (postClosePlan boundary)))
          (namedAfter (retainedBoundaryNamed exactStep))
          (namedTag (retainedBoundaryNamed exactStep)) planRaw
          (postClosePlanSelectedInactive boundary)
        0 clean : (SelectedSurvivorCleanInactive name key world error value
          nameEq selected (foreignControlAfter controlExact))
        clean = cleanAfterSelectedRetire nameEq keyEq selected survivor
          (foreignControlAfter controlExact)
          (namedTag (retainedBoundaryNamed exactStep))
          (foreignControlRaw controlExact) (postCloseCleanInactive boundary)
        0 planChecked : (checkedApplyAction @{nameEq} @{keyEq}
          (ORetire selected)
          (plannedSystemState original
            (completePlanResult (postClosePlan boundary))) =
          Just (namedTag (retainedBoundaryNamed exactStep),
            namedAfter (retainedBoundaryNamed exactStep)))
        planChecked = rewrite planRaw in
          rewrite survivorBoundaryWellFormed (retainedNextBoundary exactStep) in
          Refl
        0 headEffects : (EffectStateRelated keyEq
          (projectEffectState @{nameEq}
            (namedAfter (retainedBoundaryNamed exactStep)))
          (projectEffectState @{nameEq}
            (foreignControlAfter controlExact)))
        headEffects = postCloseOrchestrationEffects nameEq keyEq
          (ORetire selected) Refl (namedTag (retainedBoundaryNamed exactStep))
          (plannedSystemState original
            (completePlanResult (postClosePlan boundary)))
          (namedAfter (retainedBoundaryNamed exactStep)) survivor
          (foreignControlAfter controlExact) planChecked
          (foreignControlChecked controlExact) (postCloseEffects boundary)
    in packagePostCloseOrchestrationWithInvariants protocol nameEq keyEq selected
      registered ordinal live unique (ORetire selected) original originalAfter
      originalFinal survivor ORetireTag checked rest discipline retained noBegin
      (postCloseCurrentInactive boundary) (postCloseCurrentEmpty boundary)
      boundary exactStep controlExact planInactive clean headEffects
