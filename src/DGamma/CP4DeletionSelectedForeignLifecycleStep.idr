module DGamma.CP4DeletionSelectedForeignLifecycleStep

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionBoundaryRetained
import DGamma.CP4DeletionFrameCore
import DGamma.CP4DeletionFrames
import DGamma.CP4DeletionGenerationFilter
import DGamma.CP4DeletionNoEpisodeReplay
import DGamma.CP4DeletionPlanBuilder
import DGamma.CP4DeletionPlanComplete
import DGamma.CP4DeletionRelatedLifecycleEffectMap
import DGamma.CP4DeletionSelectedBoundary
import DGamma.CP4DeletionSelectedEffectCore
import DGamma.CP4DeletionSelectedEffectForeign
import DGamma.CP4DeletionSelectedForeignLifecycleReplayCore
import DGamma.CP4DeletionSelectedForeignOrchestrationStep
import DGamma.CP4DeletionSelectedRetire
import DGamma.Unified
import Decidable.Equality

%default total

0 partialRelatedAtLeftRun :
  (leftRun : leftResult = Just leftOutput) ->
  PartialRelated state relation leftResult rightResult ->
  PartialRelated state relation (Just leftOutput) rightResult
partialRelatedAtLeftRun leftRun related =
  replace {p = \observed => PartialRelated state relation observed rightResult}
    leftRun related

0 partialRelatedTransitive :
  (eq : Equivalence state) ->
  PartialRelated state (relation eq) first middle ->
  PartialRelated state (relation eq) middle last ->
  PartialRelated state (relation eq) first last
partialRelatedTransitive eq PartialUndefined PartialUndefined = PartialUndefined
partialRelatedTransitive eq (PartialDefined first) (PartialDefined second) =
  PartialDefined (transitive eq first second)

0 partialDefinedRelation :
  PartialRelated state relation (Just left) (Just right) -> relation left right
partialDefinedRelation (PartialDefined related) = related

0 transitionMapIsTableMap :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  (state : EffectState name key value world) ->
  partialEffectMap
    (Fired {before = before} {afterState = afterState}
      nameEq keyEq action tag checked) state =
    partialEffectMapFor nameEq keyEq action tag before state
transitionMapIsTableMap nameEq keyEq action tag before afterState checked state =
  Refl

record NamedForeignLifecycleReplay
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (action : Action name key value world error)
  (before, target : SystemState name key value world error) where
  constructor MkNamedForeignLifecycleReplay
  lifecycleNamed : NamedTransition name key world error value action before
  0 lifecycleFires : fireNamed nameEq keyEq action before = Just lifecycleNamed
  0 lifecycleNamedAfter : namedAfter lifecycleNamed = target

foreignLifecycleReplayNamed :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  (before : SystemState name key value world error) ->
  (0 replay : ForeignLifecycleControlReplay name key world error value nameEq keyEq
    selected action tag planAfter before) ->
  NamedForeignLifecycleReplay name key world error value nameEq keyEq action
    before (foreignLifecycleAfter replay)
foreignLifecycleReplayNamed nameEq keyEq action before replay
  with (fireNamed nameEq keyEq action before) proof fired
  foreignLifecycleReplayNamed nameEq keyEq action before replay | Nothing =
    let 0 checkedNothing : (checkedApplyAction @{nameEq} @{keyEq} action
          before = Nothing)
        checkedNothing = fireNamedNothingImpliesCheckedNothing nameEq keyEq
          action before fired
    in void (nothingIsNotJust
      (trans (sym checkedNothing) (foreignLifecycleChecked replay)))
  foreignLifecycleReplayNamed nameEq keyEq action before replay | Just named =
    let 0 namedRaw = namedFireProjectsRaw nameEq keyEq action before named fired
        0 pairSame : ((namedTag named, namedAfter named) =
          (tag, foreignLifecycleAfter replay))
        pairSame = justInjective
          (trans (sym namedRaw) (foreignLifecycleRaw replay))
    in MkNamedForeignLifecycleReplay named fired (cong snd pairSame)

||| Join a concrete retained lifecycle replay with the already-transposed
||| selected effect step.  Related owner controls compare the original Table-1
||| map with the survivor's map at the same recovered input; the actual frame
||| then connects that map output to the checked survivor target.
public export
packageForeignLifecycleEpisodeStep :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (action : Action name key value world error) ->
  (lifecycle : isLifecycleAction action = True) ->
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
  (originalOwner, survivorOwner : Fiber name key value world error) ->
  lookupFiber @{nameEq} (actionOwner action) (registry before) =
    Just originalOwner ->
  lookupFiber @{nameEq} (actionOwner action) (registry survivor) =
    Just survivorOwner ->
  FiberControlRelated originalOwner survivorOwner ->
  (0 control : ForeignLifecycleControlReplay name key world error value nameEq
    keyEq selected action (namedTag (retainedBoundaryNamed exactStep))
    (namedAfter (retainedBoundaryNamed exactStep)) survivor) ->
  ForeignRetainedEpisodeStep name key world error value nameEq keyEq selected
    registered ordinal live whole action afterState survivor
packageForeignLifecycleEpisodeStep nameEq keyEq selected registered ordinal live
  action lifecycle distinct whole before afterState
  survivor@(MkSystemState survivorWorld survivorRegistry) tag checked occurs
  independent boundary exactStep originalOwner survivorOwner originalFound
  survivorFound ownersRelated control =
    let 0 planTagSame : (namedTag (retainedBoundaryNamed exactStep) = tag)
        planTagSame = retainedBoundaryTagSame exactStep
        0 controlAtTag : ForeignLifecycleControlReplay name key world error value
          nameEq keyEq selected action tag
          (namedAfter (retainedBoundaryNamed exactStep)) survivor
        controlAtTag = replace
          {p = \observed => ForeignLifecycleControlReplay name key world error
            value nameEq keyEq selected action observed
            (namedAfter (retainedBoundaryNamed exactStep)) survivor}
          planTagSame control
        transition : Transition before afterState
        transition = Fired nameEq keyEq action tag checked
        0 effectStep : ForeignSelectedEffectStep name key world error value
          nameEq keyEq selected before afterState survivor transition whole
        effectStep = foreignStepTransposesSelectedEffectBoundary nameEq keyEq
          selected action tag before afterState checked whole occurs independent
          survivor (selectedBoundaryEffects boundary)
          (\same => distinct (sym same))
        survivorEffects : EffectState name key value world
        survivorEffects = projectEffectState @{nameEq} survivor
        0 mapsRelated : PartialRelated (EffectState name key value world)
          (EffectStateRelated keyEq)
          (partialEffectMapFor nameEq keyEq action tag before survivorEffects)
          (partialEffectMapFor nameEq keyEq action tag survivor survivorEffects)
        mapsRelated = relatedLifecyclePartialMapOutputsAtStates nameEq keyEq
          action lifecycle tag before survivor originalOwner survivorOwner
          originalFound survivorFound ownersRelated survivorEffects
        0 originalMapRuns : partialEffectMapFor nameEq keyEq action tag before
          survivorEffects = Just (foreignSurvivorOutput effectStep)
        originalMapRuns = trans
          (sym (transitionMapIsTableMap nameEq keyEq action tag before afterState
            checked survivorEffects))
          (foreignMapRunsOnSurvivor effectStep)
        0 expectedToActualMap : PartialRelated
          (EffectState name key value world) (EffectStateRelated keyEq)
          (Just (foreignSurvivorOutput effectStep))
          (partialEffectMapFor nameEq keyEq action tag survivor survivorEffects)
        expectedToActualMap = partialRelatedAtLeftRun originalMapRuns mapsRelated
        0 actualFrame : PartialRelated (EffectState name key value world)
          (EffectStateRelated keyEq)
          (partialEffectMapFor nameEq keyEq action tag survivor survivorEffects)
          (Just (projectEffectState @{nameEq}
            (foreignLifecycleAfter controlAtTag)))
        actualFrame = case actualTransitionEffectFrame nameEq keyEq action tag
          survivor (foreignLifecycleAfter controlAtTag)
          (foreignLifecycleChecked controlAtTag) of
          MkActualEffectFrame frame => frame
        0 expectedToActual : EffectStateRelated keyEq
          (foreignSurvivorOutput effectStep)
          (projectEffectState @{nameEq} (foreignLifecycleAfter controlAtTag))
        expectedToActual = partialDefinedRelation
          (partialRelatedTransitive (EffectStateEquivalence keyEq)
            expectedToActualMap actualFrame)
        0 actualToExpected : EffectStateRelated keyEq
          (projectEffectState @{nameEq} (foreignLifecycleAfter controlAtTag))
          (foreignSurvivorOutput effectStep)
        actualToExpected = symmetric (EffectStateEquivalence keyEq)
          expectedToActual
        0 nextEffects : SelectedEffectReplayBoundary name key world error value
          nameEq keyEq selected whole afterState
          (foreignLifecycleAfter controlAtTag)
        nextEffects = foreignEffectStepGivesNextBoundary nameEq keyEq selected
          transition whole effectStep actualToExpected
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
          (bindings (registry (foreignLifecycleAfter controlAtTag)))
        nextOrdered = selectedOrderedTransport (sym nextPlanBindings) Refl
          (foreignLifecycleOrdered controlAtTag)
        0 nextClean : SelectedSurvivorCleanInactive name key world error value
          nameEq selected (foreignLifecycleAfter controlAtTag)
        nextClean = foreignActionPreservesCleanInactive nameEq keyEq selected
          action distinct survivor (foreignLifecycleAfter controlAtTag) tag
          (foreignLifecycleRaw controlAtTag)
          (selectedBoundarySurvivorCleanInactive boundary)
        0 originalAfterWellFormed : registryWellFormed @{nameEq} @{keyEq}
          afterState = True
        originalAfterWellFormed = preservationTheoremProof nameEq keyEq action
          before afterState tag (selectedOriginalWellFormed boundary)
          (checkedActionProjects nameEq keyEq action before afterState tag checked)
        0 survivorAfterWellFormed : registryWellFormed @{nameEq} @{keyEq}
          (foreignLifecycleAfter controlAtTag) = True
        survivorAfterWellFormed = preservationTheoremProof nameEq keyEq action
          survivor (foreignLifecycleAfter controlAtTag) tag
          (selectedSurvivorWellFormed boundary)
          (foreignLifecycleRaw controlAtTag)
        nextBoundary = MkSelectedEpisodeReplayBoundary nextEffects nextComplete
          nextOrdered nextClean originalAfterWellFormed survivorAfterWellFormed
        namedReplay = foreignLifecycleReplayNamed nameEq keyEq action survivor
          controlAtTag
    in case namedReplay of
      MkNamedForeignLifecycleReplay named fires namedAfterSame =>
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
