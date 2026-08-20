module DGamma.CP4DeletionSelectedRetire

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionBoundaryDeleted
import DGamma.CP4DeletionBoundaryRetained
import DGamma.CP4DeletionCommuteCore
import DGamma.CP4DeletionFrameCore
import DGamma.CP4DeletionFrameRetire
import DGamma.CP4DeletionGenerationFilter
import DGamma.CP4DeletionNoEpisodeReplay
import DGamma.CP4DeletionPlanBuilder
import DGamma.CP4DeletionPlanComplete
import DGamma.CP4DeletionSelectedBoundary
import DGamma.CP4DeletionSelectedEffectCore
import DGamma.CP4RecoverySelectedReplayStep
import DGamma.Unified
import Decidable.Equality

%default total

0 selectedRetireViewTag :
  RetireSuccessView name key world error value nameEq actor ambient source tag
    afterState -> tag = ORetireTag
selectedRetireViewTag (MkRetireSuccessView fiber found) = Refl

selectedRetireViewFiber :
  RetireSuccessView name key world error value nameEq actor ambient source tag
    afterState -> Fiber name key value world error
selectedRetireViewFiber (MkRetireSuccessView fiber found) = fiber

0 selectedRetireViewFound :
  (view : RetireSuccessView name key world error value nameEq actor ambient
    source tag afterState) ->
  lookupFiber @{nameEq} actor source = Just (selectedRetireViewFiber view)
selectedRetireViewFound (MkRetireSuccessView fiber found) = found

0 selectedRetireViewAfter :
  (view : RetireSuccessView name key world error value nameEq actor ambient
    source tag afterState) ->
  MkSystemState ambient
    (replaceBinding @{nameEq} actor
      (retireFiber (selectedRetireViewFiber view)) source) = afterState
selectedRetireViewAfter (MkRetireSuccessView fiber found) = Refl

public export
record SelectedStaticFiberFound
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (selected : name)
  (left, right : Registry name key value world error)
  (leftFiber : Fiber name key value world error) where
  constructor MkSelectedStaticFiberFound
  selectedStaticRightFiber : Fiber name key value world error
  0 selectedStaticRightFound : lookupFiber @{nameEq} selected right =
    Just selectedStaticRightFiber
  0 selectedStaticRelated : FiberStaticRelated name key world error value
    leftFiber selectedStaticRightFiber

0 selectedStaticLookupFoundEntries :
  (nameEq : DecEq name) -> (selected : name) ->
  (leftFiber : Fiber name key value world error) ->
  (left, right : List (Binding name (FiberAt name key value world error))) ->
  lookupEntries @{nameEq} selected left = Just leftFiber ->
  SelectedOrderedRegistryControlsRelated name key world error value selected
    left right ->
  (rightFiber : Fiber name key value world error **
    (lookupEntries @{nameEq} selected right = Just rightFiber,
     FiberStaticRelated name key world error value leftFiber rightFiber))
selectedStaticLookupFoundEntries nameEq selected leftFiber [] [] found
  SelectedOrderedControlsNil = case found of Refl impossible
selectedStaticLookupFoundEntries nameEq selected leftFiber
  (Bind actor leftHead :: leftRest) (Bind actor rightHead :: rightRest) found
  (SelectedOrderedControlsCons actor relation tail)
  with (decEq @{nameEq} selected actor)
  selectedStaticLookupFoundEntries nameEq actor leftFiber
    (Bind actor leftHead :: leftRest) (Bind actor rightHead :: rightRest) found
    (SelectedOrderedControlsCons actor
      (SelectedFiberControls actorSelected static) tail) | Yes Refl =
        let leftSame = justInjective found
        in case leftSame of Refl => (rightHead ** (Refl, static))
  selectedStaticLookupFoundEntries nameEq actor leftFiber
    (Bind actor leftHead :: leftRest) (Bind actor rightHead :: rightRest) found
    (SelectedOrderedControlsCons actor
      (ForeignFiberControls distinct controls) tail) | Yes Refl =
        void (distinct Refl)
  selectedStaticLookupFoundEntries nameEq selected leftFiber
    (Bind actor leftHead :: leftRest) (Bind actor rightHead :: rightRest) found
    (SelectedOrderedControlsCons actor relation tail) | No different =
      selectedStaticLookupFoundEntries nameEq selected leftFiber leftRest
        rightRest found tail

public export
0 selectedStaticLookupFound :
  (nameEq : DecEq name) -> (selected : name) ->
  (left, right : Registry name key value world error) ->
  (leftFiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} selected left = Just leftFiber ->
  SelectedOrderedRegistryControlsRelated name key world error value selected
    (bindings left) (bindings right) ->
  SelectedStaticFiberFound name key world error value nameEq selected left right
    leftFiber
selectedStaticLookupFound nameEq selected left right leftFiber found ordered =
  case selectedStaticLookupFoundEntries nameEq selected leftFiber
    (bindings left) (bindings right)
    (trans (sym (lookupFiberAsEntries nameEq selected left)) found) ordered of
    (rightFiber ** (rightFound, static)) =>
      MkSelectedStaticFiberFound rightFiber
        (trans (lookupFiberAsEntries nameEq selected right) rightFound) static

public export
0 retireFiberStaticRelated :
  FiberStaticRelated name key world error value left right ->
  FiberStaticRelated name key world error value (retireFiber left)
    (retireFiber right)
retireFiberStaticRelated
  (FibersStaticRelated leftParent rightParent leftRetired rightRetired
    leftTable rightTable leftLifecycle rightLifecycle parentSame retiredSame) =
      FibersStaticRelated leftParent rightParent True True leftTable rightTable
        leftLifecycle rightLifecycle parentSame Refl

public export
0 selectedOrderedReplaceSelectedBoth :
  (nameEq : DecEq name) -> (selected : name) ->
  (nextLeft, nextRight : Fiber name key value world error) ->
  FiberStaticRelated name key world error value nextLeft nextRight ->
  (left, right : List (Binding name (FiberAt name key value world error))) ->
  SelectedOrderedRegistryControlsRelated name key world error value selected
    left right ->
  SelectedOrderedRegistryControlsRelated name key world error value selected
    (replaceEntries @{nameEq} selected nextLeft left)
    (replaceEntries @{nameEq} selected nextRight right)
selectedOrderedReplaceSelectedBoth nameEq selected nextLeft nextRight nextStatic
  [] [] SelectedOrderedControlsNil = SelectedOrderedControlsNil
selectedOrderedReplaceSelectedBoth nameEq selected nextLeft nextRight nextStatic
  (Bind actor leftFiber :: leftRest) (Bind actor rightFiber :: rightRest)
  (SelectedOrderedControlsCons actor relation tail)
  with (decEq @{nameEq} selected actor)
  selectedOrderedReplaceSelectedBoth nameEq actor nextLeft nextRight nextStatic
    (Bind actor leftFiber :: leftRest) (Bind actor rightFiber :: rightRest)
    (SelectedOrderedControlsCons actor
      (SelectedFiberControls actorSelected oldStatic) tail) | Yes Refl =
        SelectedOrderedControlsCons actor
          (SelectedFiberControls Refl nextStatic) tail
  selectedOrderedReplaceSelectedBoth nameEq actor nextLeft nextRight nextStatic
    (Bind actor leftFiber :: leftRest) (Bind actor rightFiber :: rightRest)
    (SelectedOrderedControlsCons actor
      (ForeignFiberControls distinct controls) tail) | Yes Refl =
        void (distinct Refl)
  selectedOrderedReplaceSelectedBoth nameEq selected nextLeft nextRight nextStatic
    (Bind actor leftFiber :: leftRest) (Bind actor rightFiber :: rightRest)
    (SelectedOrderedControlsCons actor relation tail) | No different =
      SelectedOrderedControlsCons actor relation
        (selectedOrderedReplaceSelectedBoth nameEq selected nextLeft nextRight
          nextStatic leftRest rightRest tail)

public export
record SelectedRetainedEpisodeStep
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (selected : name)
  (registered : List (RegistrationGeneration name))
  (ordinal : Nat) (live : GenerationEnvironment name)
  {wholeFirst, wholeLast : SystemState name key value world error}
  (whole : Transitions wholeFirst wholeLast)
  (originalAfter, survivorBefore : SystemState name key value world error) where
  constructor MkSelectedRetainedEpisodeStep
  selectedRetainedNamed : NamedTransition name key world error value
    (ORetire selected) survivorBefore
  0 selectedRetainedFires : fireNamed nameEq keyEq (ORetire selected)
    survivorBefore = Just selectedRetainedNamed
  0 selectedRetainedBoundary : SelectedEpisodeReplayBoundary name key world error
    value nameEq keyEq selected registered (S ordinal) live whole originalAfter
    (namedAfter selectedRetainedNamed)

public export
record RetainedNextPlanPackage
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (registered : List (RegistrationGeneration name))
  (live : GenerationEnvironment name)
  (originalAfter, namedAfter : SystemState name key value world error) where
  constructor MkRetainedNextPlanPackage
  retainedPackagePlan : CompleteCurrentRegisteredPlanResult name key world error
    value nameEq registered live (registry originalAfter)
  0 retainedPackageBindings : bindings
    (planTarget (completePlanResult retainedPackagePlan)) =
    bindings (registry namedAfter)

public export
retainedStepNextPlanPackage :
  (step : RetainedNoEpisodeBoundaryStep name key world error value nameEq keyEq
    registered live action originalTag originalAfter survivorBefore) ->
  RetainedNextPlanPackage name key world error value nameEq registered live
    originalAfter (namedAfter (retainedBoundaryNamed step))
retainedStepNextPlanPackage step = case retainedNextBoundary step of
  MkNoEpisodeReplayBoundary ambient source originalShape complete
    survivorWorld survivorBindings unique originalWellFormed survivorWellFormed =>
      let 0 sourceSame : (registry originalAfter = source)
          sourceSame = cong registry originalShape
          transported = replace
            {p = \observed => CompleteCurrentRegisteredPlanResult name key world
              error value nameEq registered live observed}
            (sym sourceSame) complete
      in MkRetainedNextPlanPackage transported (sym survivorBindings)

||| Replay retained selected O-Retire while the episode's lifecycle actions stay
||| quotiented.  Both selected cells receive the same static retirement edit;
||| the original accumulator model advances, whereas the survivor executes the
||| real checked orchestration step.
public export
0 retainedSelectedRetirePreservesEpisodeBoundary :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (whole : Transitions wholeFirst wholeLast) ->
  (before, afterState, survivor : SystemState name key value world error) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} (ORetire selected) before =
    Just (ORetireTag, afterState)) ->
  (boundary : SelectedEpisodeReplayBoundary name key world error value nameEq
    keyEq selected registered ordinal live whole before survivor) ->
  (planStep : RetainedNoEpisodeBoundaryStep name key world error value nameEq
    keyEq registered live (ORetire selected) ORetireTag afterState
    (MkSystemState (worldState before)
      (planTarget
        (completePlanResult (selectedBoundaryPlan boundary))))) ->
  SelectedRetainedEpisodeStep name key world error value nameEq keyEq selected
    registered ordinal live whole afterState survivor
retainedSelectedRetirePreservesEpisodeBoundary
  {name} {key} {world} {error} {value}
  nameEq keyEq selected registered ordinal live whole before afterState survivor
  checked
  boundary@(MkSelectedEpisodeReplayBoundary
    oldEffects oldComplete oldOrdered oldClean beforeWellFormed survivorWellFormed)
  planStep =
    case survivor of
      MkSystemState survivorWorld survivorRegistry =>
        retireAtPlan (worldState before)
          (planTarget (completePlanResult oldComplete)) survivorWorld
          survivorRegistry oldEffects oldOrdered oldClean survivorWellFormed
          planStep
  where
  0 retireAtPlan :
    (planWorld : world) -> (planRegistry : Registry name key value world error) ->
    (survivorWorld : world) ->
    (survivorRegistry : Registry name key value world error) ->
    SelectedEffectReplayBoundary name key world error value nameEq keyEq selected
      whole before (MkSystemState survivorWorld survivorRegistry) ->
    SelectedOrderedRegistryControlsRelated name key world error value selected
      (bindings planRegistry) (bindings survivorRegistry) ->
    SelectedSurvivorCleanInactive name key world error value nameEq selected
      (MkSystemState survivorWorld survivorRegistry) ->
    registryWellFormed @{nameEq} @{keyEq}
      (the (SystemState name key value world error)
        (MkSystemState survivorWorld survivorRegistry)) = True ->
    RetainedNoEpisodeBoundaryStep name key world error value nameEq keyEq
      registered live (ORetire selected) ORetireTag afterState
      (MkSystemState planWorld planRegistry) ->
    SelectedRetainedEpisodeStep name key world error value nameEq keyEq selected
      registered ordinal live whole afterState
      (MkSystemState survivorWorld survivorRegistry)
  retireAtPlan planWorld planRegistry survivorWorld survivorRegistry
    effectsAt orderedAt cleanAt rightWellFormed exactStep =
      let planRaw = namedFireProjectsRaw nameEq keyEq (ORetire selected)
            (MkSystemState planWorld planRegistry) (retainedBoundaryNamed exactStep)
            (retainedBoundaryFires exactStep)
      in let view = retireSuccessView nameEq keyEq selected planWorld planRegistry
               (namedTag (retainedBoundaryNamed exactStep))
               (namedAfter (retainedBoundaryNamed exactStep)) planRaw
         in case selectedStaticLookupFound nameEq selected planRegistry
           survivorRegistry (selectedRetireViewFiber view) (selectedRetireViewFound view) orderedAt of
            MkSelectedStaticFiberFound survivorFiber survivorFound static =>
              let planAfterConcrete : SystemState name key value world error
                  planAfterConcrete = MkSystemState planWorld
                    (replaceBinding @{nameEq} selected (retireFiber (selectedRetireViewFiber view))
                      planRegistry)
                  survivorAfter : SystemState name key value world error
                  survivorAfter = MkSystemState survivorWorld
                    (replaceBinding @{nameEq} selected (retireFiber survivorFiber)
                      survivorRegistry)
                  0 tagSame : namedTag (retainedBoundaryNamed exactStep) = ORetireTag
                  tagSame = selectedRetireViewTag view
                  0 planAfterShape : planAfterConcrete = namedAfter (retainedBoundaryNamed exactStep)
                  planAfterShape = selectedRetireViewAfter view
                  survivorRawTag : applyAction @{nameEq} @{keyEq}
                    (ORetire selected)
                    (MkSystemState survivorWorld survivorRegistry) =
                    Just (ORetireTag, survivorAfter)
                  survivorRawTag = rewrite survivorFound in Refl
                  survivorRaw : applyAction @{nameEq} @{keyEq}
                    (ORetire selected)
                    (MkSystemState survivorWorld survivorRegistry) =
                    Just (namedTag (retainedBoundaryNamed exactStep), survivorAfter)
                  survivorRaw = rewrite tagSame in survivorRawTag
                  0 survivorAfterWellFormed : registryWellFormed @{nameEq}
                    @{keyEq} survivorAfter = True
                  survivorAfterWellFormed = preservationTheoremProof nameEq keyEq
                    (ORetire selected)
                    (MkSystemState survivorWorld survivorRegistry) survivorAfter
                    (namedTag (retainedBoundaryNamed exactStep)) rightWellFormed survivorRaw
                  0 survivorChecked : checkedApplyAction @{nameEq} @{keyEq}
                    (ORetire selected)
                    (MkSystemState survivorWorld survivorRegistry) =
                    Just (namedTag (retainedBoundaryNamed exactStep), survivorAfter)
                  survivorChecked = rewrite survivorRaw in
                    rewrite survivorAfterWellFormed in Refl
                  survivorNamed : NamedTransition name key world error value
                    (ORetire selected)
                    (MkSystemState survivorWorld survivorRegistry)
                  survivorNamed = MkNamedTransition survivorAfter
                    (namedTag (retainedBoundaryNamed exactStep))
                    (Fired nameEq keyEq (ORetire selected) (namedTag (retainedBoundaryNamed exactStep))
                      survivorChecked) Refl
                  0 survivorFires : fireNamed nameEq keyEq (ORetire selected)
                    (MkSystemState survivorWorld survivorRegistry) =
                    Just survivorNamed
                  survivorFires = rewrite survivorChecked in Refl
                  0 staticNext : FiberStaticRelated name key world error value
                    (retireFiber (selectedRetireViewFiber view)) (retireFiber survivorFiber)
                  staticNext = retireFiberStaticRelated static
                  0 replacedOrdered : SelectedOrderedRegistryControlsRelated
                    name key world error value selected
                    (replaceEntries @{nameEq} selected (retireFiber (selectedRetireViewFiber view))
                      (bindings planRegistry))
                    (replaceEntries @{nameEq} selected (retireFiber survivorFiber)
                      (bindings survivorRegistry))
                  replacedOrdered = selectedOrderedReplaceSelectedBoth nameEq
                    selected (retireFiber (selectedRetireViewFiber view)) (retireFiber survivorFiber)
                    staticNext (bindings planRegistry)
                    (bindings survivorRegistry) orderedAt
                  0 planBindings : bindings
                    (replaceBinding @{nameEq} selected (retireFiber (selectedRetireViewFiber view))
                      planRegistry) =
                    replaceEntries @{nameEq} selected (retireFiber (selectedRetireViewFiber view))
                      (bindings planRegistry)
                  planBindings = replaceBindingRuntimeBindings nameEq selected
                    (retireFiber (selectedRetireViewFiber view)) planRegistry
                  0 survivorBindings : bindings
                    (replaceBinding @{nameEq} selected (retireFiber survivorFiber)
                      survivorRegistry) =
                    replaceEntries @{nameEq} selected (retireFiber survivorFiber)
                      (bindings survivorRegistry)
                  survivorBindings = replaceBindingRuntimeBindings nameEq selected
                    (retireFiber survivorFiber) survivorRegistry
                  0 concreteOrdered : SelectedOrderedRegistryControlsRelated
                    name key world error value selected
                    (bindings (replaceBinding @{nameEq} selected
                      (retireFiber (selectedRetireViewFiber view)) planRegistry))
                    (bindings (replaceBinding @{nameEq} selected
                      (retireFiber survivorFiber) survivorRegistry))
                  concreteOrdered = selectedOrderedTransport (sym planBindings)
                    (sym survivorBindings) replacedOrdered
                  0 observedOrdered : SelectedOrderedRegistryControlsRelated
                    name key world error value selected
                    (bindings (registry (namedAfter (retainedBoundaryNamed exactStep))))
                    (bindings (registry survivorAfter))
                  observedOrdered = selectedOrderedTransport
                    (cong (\state => bindings (registry state)) planAfterShape)
                    Refl concreteOrdered
                  0 originalStep : SelectedAccumulatorStep name key world error
                    value nameEq keyEq selected
                    (Fired nameEq keyEq (ORetire selected) ORetireTag checked)
                    whole (selectedBoundaryModel effectsAt)
                  originalStep = selectedRetireAccumulatorStep nameEq keyEq
                    selected before afterState whole checked
                    (selectedBoundaryModel effectsAt)
                  0 skippedEffects : SelectedEffectReplayBoundary name key world
                    error value nameEq keyEq selected whole afterState
                    (MkSystemState survivorWorld survivorRegistry)
                  skippedEffects = selectedStepPreservesEffectReplayBoundary
                    nameEq keyEq selected
                    (Fired nameEq keyEq (ORetire selected) ORetireTag checked)
                    whole effectsAt originalStep
                  0 survivorFrame : EffectStateRelated keyEq
                    (projectEffectState @{nameEq}
                      (the (SystemState name key value world error)
                        (MkSystemState survivorWorld survivorRegistry)))
                    (projectEffectState @{nameEq} survivorAfter)
                  survivorFrame = case retireActualEffectFrame nameEq keyEq selected
                    (MkSystemState survivorWorld survivorRegistry) survivorAfter
                    ORetireTag survivorRawTag of
                    MkActualEffectFrame (PartialDefined related) => related
                  0 nextEffects : SelectedEffectReplayBoundary name key world
                    error value nameEq keyEq selected whole afterState
                    survivorAfter
                  nextEffects = case skippedEffects of
                    MkSelectedEffectReplayBoundary model recovered runs
                      oldSurvivorToRecovered =>
                        MkSelectedEffectReplayBoundary model recovered runs
                          (transitive (EffectStateEquivalence keyEq)
                            (symmetric (EffectStateEquivalence keyEq) survivorFrame)
                            oldSurvivorToRecovered)
                  nextPackage : RetainedNextPlanPackage name key world error
                    value nameEq registered live afterState
                    (namedAfter (retainedBoundaryNamed exactStep))
                  nextPackage = retainedStepNextPlanPackage exactStep
                  nextComplete : CompleteCurrentRegisteredPlanResult name key
                    world error value nameEq registered live
                    (registry afterState)
                  nextComplete = retainedPackagePlan nextPackage
                  0 nextPlanBindings : bindings
                    (planTarget (completePlanResult nextComplete)) =
                    bindings (registry
                      (namedAfter (retainedBoundaryNamed exactStep)))
                  nextPlanBindings = retainedPackageBindings nextPackage
                  0 nextOrdered : SelectedOrderedRegistryControlsRelated name
                    key world error value selected
                    (bindings (planTarget (completePlanResult nextComplete)))
                    (bindings (registry survivorAfter))
                  nextOrdered = selectedOrderedTransport (sym nextPlanBindings)
                    Refl observedOrdered
                  0 nextClean : SelectedSurvivorCleanInactive name key world
                    error value nameEq selected survivorAfter
                  nextClean = case cleanAt of
                    SelectedCleanInactiveWitness cleanComponent cleanParent
                      cleanRetired cleanTable cleanFound =>
                        let 0 cleanSame : (survivorFiber =
                              MkFiber cleanComponent cleanParent cleanRetired
                                cleanTable (Inactive Nothing))
                            cleanSame = justInjective
                              (trans (sym survivorFound) cleanFound)
                            0 retiredFound : lookupFiber @{nameEq} selected
                              (replaceBinding @{nameEq} selected
                                (retireFiber survivorFiber) survivorRegistry) =
                              Just (retireFiber survivorFiber)
                            retiredFound = lookupReplacedFiber selected
                              survivorFiber (retireFiber survivorFiber)
                              survivorRegistry survivorFound
                        in case cleanSame of
                          Refl => SelectedCleanInactiveWitness cleanComponent
                            cleanParent True cleanTable retiredFound
                  nextBoundary : SelectedEpisodeReplayBoundary name key world
                    error value nameEq keyEq selected registered (S ordinal) live
                    whole afterState survivorAfter
                  nextBoundary = MkSelectedEpisodeReplayBoundary nextEffects
                    nextComplete nextOrdered nextClean
                    (preservationTheoremProof nameEq keyEq (ORetire selected)
                      before afterState ORetireTag beforeWellFormed
                      (checkedActionProjects nameEq keyEq (ORetire selected)
                        before afterState ORetireTag checked))
                    survivorAfterWellFormed
              in MkSelectedRetainedEpisodeStep survivorNamed survivorFires
                nextBoundary
