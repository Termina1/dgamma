module DGamma.CP4DeletionPostCloseRemove

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
import DGamma.CP4DeletionFrameCore
import DGamma.CP4DeletionNoEpisodeReplay
import DGamma.CP4DeletionPostCloseEffectReplay
import DGamma.CP4ParentSafety
import DGamma.CP4DeletionPostCloseOrchestration
import DGamma.CP4DeletionPlanBuilder
import DGamma.CP4DeletionPlanComplete
import DGamma.CP4DeletionPostCloseUpgrade
import DGamma.CP4DeletionRelationalActionCore
import DGamma.CP4DeletionRelationalBoundary
import DGamma.CP4DeletionRelationalSuffixFold
import DGamma.CP4DeletionSelectedBoundary
import DGamma.CP4DeletionSelectedCloseBoundary
import DGamma.CP4DeletionSelectedForeignControlCore
import DGamma.CP4DeletionSelectedOwn
import DGamma.CP4DeletionSelectedForeignOrchestration
import DGamma.CP4DeletionSelectedForeignOrchestrationStep
import DGamma.CP4DeletionSelectedRetire
import DGamma.CP4RuntimeBindings
import Decidable.Equality

%default total

0 lookupDeleteSelfPostRemove :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) ->
  (source : Registry name key value world error) ->
  lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} selected
    (deleteBinding @{nameEq} selected source) = Nothing
lookupDeleteSelfPostRemove nameEq selected
  (MkCoeffectContext entries unique) = lookupDeleteSelf @{nameEq} selected
    (MkCoeffectContext entries unique)

0 selectedOrderedDeleteSelectedPost :
  (nameEq : DecEq name) -> (selected : name) ->
  (left, right : List (Binding name (FiberAt name key value world error))) ->
  SelectedOrderedRegistryControlsRelated name key world error value selected
    left right ->
  SelectedOrderedRegistryControlsRelated name key world error value selected
    (deleteEntries @{nameEq} selected left)
    (deleteEntries @{nameEq} selected right)
selectedOrderedDeleteSelectedPost nameEq selected [] []
  SelectedOrderedControlsNil = SelectedOrderedControlsNil
selectedOrderedDeleteSelectedPost nameEq selected
  (Bind actor leftFiber :: leftRest) (Bind actor rightFiber :: rightRest)
  (SelectedOrderedControlsCons actor relation tail)
  with (decEq @{nameEq} selected actor)
  selectedOrderedDeleteSelectedPost nameEq actor
    (Bind actor leftFiber :: leftRest) (Bind actor rightFiber :: rightRest)
    (SelectedOrderedControlsCons actor relation tail) | Yes Refl = tail
  selectedOrderedDeleteSelectedPost nameEq selected
    (Bind actor leftFiber :: leftRest) (Bind actor rightFiber :: rightRest)
    (SelectedOrderedControlsCons actor relation tail) | No distinct =
      SelectedOrderedControlsCons actor relation
        (selectedOrderedDeleteSelectedPost nameEq selected leftRest rightRest tail)

0 andLeftTruePostRemove : (left, right : Bool) -> left && right = True ->
  left = True
andLeftTruePostRemove False right Refl impossible
andLeftTruePostRemove True right equation = Refl

0 fiberStaticRetiredPost :
  FiberStaticRelated name key world error value left right ->
  retired left = retired right
fiberStaticRetiredPost
  (FibersStaticRelated leftParent rightParent leftRetired rightRetired leftTable
    rightTable leftLifecycle rightLifecycle parentSame retiredSame) = retiredSame

0 selectedRemovePostControls :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (planAmbient, survivorAmbient : world) ->
  (plan, survivor : Registry name key value world error) ->
  SelectedOrderedRegistryControlsRelated name key world error value selected
    (bindings plan) (bindings survivor) ->
  SelectedSurvivorCleanInactive name key world error value nameEq selected
    (MkSystemState survivorAmbient survivor) ->
  (tag : RuleTag) -> (planAfter : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} (ORemove selected)
    (MkSystemState planAmbient plan) = Just (tag, planAfter) ->
  registryWellFormed @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error}
    (MkSystemState survivorAmbient survivor) = True ->
  ForeignOrchestrationControlReplay name key world error value nameEq keyEq
    selected (ORemove selected) tag planAfter
    (MkSystemState survivorAmbient survivor)
selectedRemovePostControls nameEq keyEq selected planAmbient survivorAmbient plan
  survivor ordered clean tag planAfter planRaw survivorWF =
    case removeSuccessView nameEq keyEq selected planAmbient plan tag planAfter
      planRaw of
      MkRemoveSuccessView planFiber planFound planGuard planNoChild =>
        case selectedStaticLookupFound nameEq selected plan survivor planFiber
          planFound ordered of
          MkSelectedStaticFiberFound survivorFiber survivorFound static =>
            case clean of
              SelectedCleanInactiveWitness cleanComponent cleanParent
                cleanRetired cleanTable cleanFound =>
                  let sameFiber = justInjective (trans (sym survivorFound)
                        cleanFound)
                  in case sameFiber of
                    Refl =>
                      let retiredSame = fiberStaticRetiredPost static
                          childSame = selectedOrderedHasChildSame nameEq selected
                            plan survivor ordered
                          survivorNoChild = trans (sym childSame) planNoChild
                          planRetiredTrue = andLeftTruePostRemove
                            (retired planFiber)
                            (isInactive (fiberLifecycle planFiber) &&
                              not (hasChild @{nameEq} selected plan)) planGuard
                          survivorRetiredTrue = trans (sym retiredSame)
                            planRetiredTrue
                          survivorGuard : (retired (MkFiber cleanComponent
                              cleanParent cleanRetired cleanTable
                              (Inactive Nothing)) && True &&
                            not (hasChild @{nameEq} {name = name} {key = key}
                              {value = value} {world = world} {error = error}
                              selected survivor) = True)
                          survivorGuard = rewrite survivorNoChild in
                            rewrite survivorRetiredTrue in Refl
                          0 survivorRaw : applyAction @{nameEq} @{keyEq}
                              {name = name} {key = key} {value = value}
                              {world = world} {error = error} (ORemove selected)
                              (MkSystemState survivorAmbient survivor) =
                            Just (ORemoveTag, (MkSystemState survivorAmbient
                            (deleteBinding @{nameEq} selected survivor)))
                          survivorRaw = rewrite cleanFound in
                            rewrite survivorGuard in Refl
                          0 survivorAfterWF : registryWellFormed @{nameEq}
                            @{keyEq} {name = name} {key = key} {value = value}
                            {world = world} {error = error}
                            (MkSystemState survivorAmbient
                            (deleteBinding @{nameEq} selected survivor)) = True
                          survivorAfterWF = preservationTheoremProof nameEq keyEq
                            (ORemove selected)
                            (MkSystemState survivorAmbient survivor) (MkSystemState survivorAmbient
                            (deleteBinding @{nameEq} selected survivor))
                            ORemoveTag survivorWF survivorRaw
                          0 survivorChecked : checkedApplyAction @{nameEq}
                              @{keyEq} {name = name} {key = key} {value = value}
                              {world = world} {error = error} (ORemove selected)
                              (MkSystemState survivorAmbient survivor) =
                            Just (ORemoveTag, (MkSystemState survivorAmbient
                            (deleteBinding @{nameEq} selected survivor)))
                          survivorChecked = rewrite survivorRaw in
                            rewrite survivorAfterWF in Refl
                          0 deleted : SelectedOrderedRegistryControlsRelated
                            name key world error value selected
                            (deleteEntries @{nameEq} selected (bindings plan))
                            (deleteEntries @{nameEq} selected
                              (bindings survivor))
                          deleted = selectedOrderedDeleteSelectedPost nameEq
                            selected (bindings plan) (bindings survivor) ordered
                          0 planBindings : bindings
                              (deleteBinding @{nameEq} selected plan) =
                            deleteEntries @{nameEq} selected (bindings plan)
                          planBindings = deleteBindingRuntimeBindings nameEq
                            selected plan
                          0 survivorBindings : bindings
                              (deleteBinding @{nameEq} selected survivor) =
                            deleteEntries @{nameEq} selected (bindings survivor)
                          survivorBindings = deleteBindingRuntimeBindings nameEq
                            selected survivor
                          0 finalOrdered : SelectedOrderedRegistryControlsRelated
                            name key world error value selected
                            (bindings (deleteBinding @{nameEq} selected plan))
                            (bindings (deleteBinding @{nameEq} selected survivor))
                          finalOrdered = selectedOrderedTransport
                            (sym planBindings) (sym survivorBindings) deleted
                      in MkForeignOrchestrationControlReplay (MkSystemState survivorAmbient
                            (deleteBinding @{nameEq} selected survivor))
                        survivorRaw survivorChecked finalOrdered

0 orderedTransitivePostRemove :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {left, middle, right : List
    (Binding name (FiberAt name key value world error))} ->
  OrderedRegistryControlsRelated name key world error value left middle ->
  OrderedRegistryControlsRelated name key world error value middle right ->
  OrderedRegistryControlsRelated name key world error value left right
orderedTransitivePostRemove OrderedControlsNil OrderedControlsNil =
  OrderedControlsNil
orderedTransitivePostRemove
  (OrderedControlsCons actor first firstRest)
  (OrderedControlsCons actor second secondRest) =
    OrderedControlsCons actor (fiberControlTransitive first second)
      (orderedTransitivePostRemove firstRest secondRest)

0 effectsTransitivePostRemove :
  {name, key, world : Type} -> {value : key -> Type} ->
  {left, middle, right : EffectState name key value world} ->
  (keyEq : DecEq key) -> EffectStateRelated keyEq left middle -> EffectStateRelated keyEq middle right ->
  EffectStateRelated keyEq left right
effectsTransitivePostRemove keyEq
  (MkEffectStateRelated firstAmbient firstTables)
  (MkEffectStateRelated secondAmbient secondTables) =
    MkEffectStateRelated (trans firstAmbient secondAmbient)
      (\actor => trans (firstTables actor) (secondTables actor))

||| Selected O-Remove is the first point where the static quotient can disappear.
||| Replay it on the survivor, upgrade the now-absent selected cell, and return
||| the ordinary relational boundary consumed by the generic suffix fold.
public export
0 retainedSelectedPostCloseRemove :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  GenerationEnvironmentNamesUnique live ->
  (original, originalAfter, originalFinal, survivor :
    SystemState name key value world error) ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} (ORemove selected) original =
    Just (tag, originalAfter)) ->
  (rest : Transitions originalAfter originalFinal) ->
  RegistrationStepDiscipline protocol nameEq (ORemove selected) original rest ->
  (retained : Not (GenerationOwnedActor nameEq registered ordinal live
    (the (Action name key value world error) (ORemove selected)))) ->
  (boundary : PostCloseSelectedBoundary name key world error value nameEq keyEq
    selected registered ordinal live original survivor) ->
  RelationalRetainedNoEpisodeBoundaryStep name key world error value nameEq keyEq
    registered (advanceGenerationEnvironment @{nameEq} ordinal
      (the (Action name key value world error) (ORemove selected)) live)
    (ORemove selected) originalAfter survivor
retainedSelectedPostCloseRemove protocol nameEq keyEq selected registered ordinal
  live unique original originalAfter originalFinal survivor tag checked rest
  discipline retained boundary =
    let 0 exactBefore = postClosePlanExactBoundary nameEq keyEq unique boundary
        0 exactStep = retainedSuffixHeadPreservesNoEpisodeBoundary protocol nameEq
          keyEq registered ordinal live (ORemove selected) original
          (plannedSystemState original
            (completePlanResult (postClosePlan boundary))) exactBefore tag checked
          rest discipline retained
        0 planRaw : (applyAction @{nameEq} @{keyEq}
          (ORemove selected)
          (plannedSystemState original
            (completePlanResult (postClosePlan boundary))) =
        Just (namedTag (retainedBoundaryNamed exactStep), namedAfter (retainedBoundaryNamed exactStep)))
        planRaw = namedFireProjectsRaw nameEq keyEq (ORemove selected)
          (plannedSystemState original
            (completePlanResult (postClosePlan boundary)))
          (retainedBoundaryNamed exactStep) (retainedBoundaryFires exactStep)
        0 cleanEta : SelectedSurvivorCleanInactive name key world error value
          nameEq selected
          (MkSystemState (worldState survivor) (registry survivor))
        cleanEta = replace
          {p = \observed => SelectedSurvivorCleanInactive name key world error
            value nameEq selected observed}
          (sym (systemEtaPost survivor)) (postCloseCleanInactive boundary)
        0 controlEta : ForeignOrchestrationControlReplay name key world error
          value nameEq keyEq selected (ORemove selected)
          (namedTag (retainedBoundaryNamed exactStep))
          (namedAfter (retainedBoundaryNamed exactStep))
          (MkSystemState (worldState survivor) (registry survivor))
        controlEta = selectedRemovePostControls nameEq keyEq selected
          (worldState original) (worldState survivor)
          (planTarget (completePlanResult (postClosePlan boundary)))
          (registry survivor) (postCloseControls boundary) cleanEta
          (namedTag (retainedBoundaryNamed exactStep))
          (namedAfter (retainedBoundaryNamed exactStep)) planRaw
          (postCloseSurvivorWellFormed boundary)
        0 control : ForeignOrchestrationControlReplay name key world error value
          nameEq keyEq selected (ORemove selected)
          (namedTag (retainedBoundaryNamed exactStep))
          (namedAfter (retainedBoundaryNamed exactStep)) survivor
        control = replace
          {p = \observed => ForeignOrchestrationControlReplay name key world error
            value nameEq keyEq selected (ORemove selected)
            (namedTag (retainedBoundaryNamed exactStep))
            (namedAfter (retainedBoundaryNamed exactStep)) observed}
          (systemEtaPost survivor) controlEta
        0 planChecked : checkedApplyAction @{nameEq} @{keyEq}
            (ORemove selected)
            (plannedSystemState original
              (completePlanResult (postClosePlan boundary))) =
          Just (namedTag (retainedBoundaryNamed exactStep),
            namedAfter (retainedBoundaryNamed exactStep))
        planChecked = rewrite planRaw in
          rewrite survivorBoundaryWellFormed (retainedNextBoundary exactStep) in
          Refl
        0 headEffects : EffectStateRelated keyEq
          (projectEffectState @{nameEq}
            (namedAfter (retainedBoundaryNamed exactStep)))
          (projectEffectState @{nameEq} (foreignControlAfter control))
        headEffects = postCloseOrchestrationEffects nameEq keyEq
          (ORemove selected) Refl (namedTag (retainedBoundaryNamed exactStep))
          (plannedSystemState original
            (completePlanResult (postClosePlan boundary)))
          (namedAfter (retainedBoundaryNamed exactStep)) survivor
          (foreignControlAfter control) planChecked
          (foreignControlChecked control) (postCloseEffects boundary)
        0 afterAbsent : lookupFiber @{nameEq} {name = name} {key = key}
            {value = value} {world = world} {error = error} selected
            (registry (namedAfter (retainedBoundaryNamed exactStep))) = Nothing
        afterAbsent = removeTargetIsAbsent nameEq keyEq selected
          (plannedSystemState original
            (completePlanResult (postClosePlan boundary)))
          (namedAfter (retainedBoundaryNamed exactStep))
          (namedTag (retainedBoundaryNamed exactStep)) planRaw
        0 afterEntriesAbsent : lookupEntries @{nameEq} selected
            (bindings (registry
              (namedAfter (retainedBoundaryNamed exactStep)))) = Nothing
        afterEntriesAbsent = trans
          (sym (lookupFiberAsEntries nameEq selected
            (registry (namedAfter (retainedBoundaryNamed exactStep)))))
          afterAbsent
        0 afterOrdered : OrderedRegistryControlsRelated name key world error
          value (bindings (registry
            (namedAfter (retainedBoundaryNamed exactStep))))
            (bindings (registry (foreignControlAfter control)))
        afterOrdered = selectedOrderedAbsentGivesOrdered nameEq selected
          (bindings (registry (namedAfter (retainedBoundaryNamed exactStep))))
          (bindings (registry (foreignControlAfter control)))
          afterEntriesAbsent
          (foreignControlOrdered control)
    in packagePostCloseDischarged nameEq keyEq selected registered ordinal
      live (ORemove selected) originalAfter survivor
      exactStep
      control
      headEffects afterOrdered (postCloseSurvivorWellFormed boundary)
