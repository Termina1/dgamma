module DGamma.CP4DeletionSelectedForeignLifecycleUnload

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionCommuteCore
import DGamma.CP4DeletionSelectedBoundary
import DGamma.CP4DeletionSelectedForeignLifecycleCore
import DGamma.CP4DeletionSelectedForeignLifecycleReplayCore
import Decidable.Equality

%default total

0 nothingNotJustForeignUnload : Nothing = Just item -> Void
nothingNotJustForeignUnload Refl impossible

public export
record ForeignUnloadPlanView
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (actor : name) (ambient : world)
  (plan : Registry name key value world error)
  (owner : Fiber name key value world error)
  (tag : RuleTag) (afterState : SystemState name key value world error) where
  constructor MkForeignUnloadPlanView
  unloadComponent : Component key value world error
  unloadParent : Parent name
  unloadRetired : Bool
  unloadTable : OwnedTable key value
    (componentProvisions unloadComponent)
  unloadAccumulator : LocalState key value world
    (componentProvisions unloadComponent) ->
    LocalState key value world (componentProvisions unloadComponent)
  unloadView : View name
    (dependencies (componentDependencies unloadComponent))
  unloadOutcome : Maybe error
  0 unloadOwnerShape : owner = MkFiber unloadComponent unloadParent unloadRetired
    unloadTable (Unloading unloadAccumulator unloadView unloadOutcome)
  0 unloadPlanUnrelied : relied @{nameEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} actor plan = False

public export
record LocatedForeignUnloadPlanView
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (actor : name) (ambient : world)
  (plan : Registry name key value world error)
  (tag : RuleTag) (afterState : SystemState name key value world error) where
  constructor MkLocatedForeignUnloadPlanView
  unloadPlanOwner : Fiber name key value world error
  0 unloadPlanOwnerFound : lookupFiber @{nameEq} actor plan =
    Just unloadPlanOwner
  0 unloadPlanView : ForeignUnloadPlanView name key world error value nameEq
    keyEq actor ambient plan unloadPlanOwner tag afterState

public export
0 foreignUnloadPlanView :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (plan : Registry name key value world error) ->
  (tag : RuleTag) -> (afterState : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq} (LUnload actor)
    (MkSystemState ambient plan) = Just (tag, afterState) ->
  LocatedForeignUnloadPlanView name key world error value nameEq keyEq actor
    ambient plan tag afterState
foreignUnloadPlanView nameEq keyEq actor ambient plan tag afterState raw
  with (lookupFiber @{nameEq} actor plan) proof found
  foreignUnloadPlanView nameEq keyEq actor ambient plan tag afterState raw |
    Nothing = void (nothingNotJustForeignUnload raw)
  foreignUnloadPlanView nameEq keyEq actor ambient plan tag afterState raw |
    Just (MkFiber component parent retiredFlag table (Inactive outcome)) =
      void (nothingNotJustForeignUnload raw)
  foreignUnloadPlanView nameEq keyEq actor ambient plan tag afterState raw |
    Just (MkFiber component parent retiredFlag table
      (Reloading remaining accumulator view)) =
        void (nothingNotJustForeignUnload raw)
  foreignUnloadPlanView nameEq keyEq actor ambient plan tag afterState raw |
    Just (MkFiber component parent retiredFlag table
      (Active accumulator view)) = void (nothingNotJustForeignUnload raw)
  foreignUnloadPlanView nameEq keyEq actor ambient plan tag afterState raw |
    Just (MkFiber component parent retiredFlag table
      (Unloading accumulator view outcome))
    with (relied @{nameEq} actor plan) proof reliance
    foreignUnloadPlanView nameEq keyEq actor ambient plan tag afterState raw |
      Just (MkFiber component parent retiredFlag table
        (Unloading accumulator view outcome)) | True =
          void (nothingNotJustForeignUnload raw)
    foreignUnloadPlanView nameEq keyEq actor ambient plan tag afterState raw |
      Just (MkFiber component parent retiredFlag table
        (Unloading accumulator view outcome)) | False =
          case justInjective raw of
            Refl => MkLocatedForeignUnloadPlanView
              (MkFiber component parent retiredFlag table
                (Unloading accumulator view outcome)) found
              (MkForeignUnloadPlanView component parent retiredFlag table
                accumulator view outcome Refl reliance)

public export
record UnloadingRightControls
  {key, world, error, name : Type} {value : key -> Type}
  {deps : List key} {provision : CoeffectSpec key}
  (leftAccumulator : LocalState key value world provision ->
    LocalState key value world provision)
  (leftView : View name deps) (leftOutcome : Maybe error)
  (rightLifecycle : Lifecycle key value world error name deps provision) where
  constructor MkUnloadingRightControls
  rightControlAccumulator : LocalState key value world provision ->
    LocalState key value world provision
  rightControlView : View name deps
  rightControlOutcome : Maybe error
  0 rightControlLifecycle : rightLifecycle = Unloading rightControlAccumulator
    rightControlView rightControlOutcome
  0 rightControlAccumulatorsEqual : AccumulatorRelated leftAccumulator
    rightControlAccumulator
  0 rightControlViewsEqual : leftView = rightControlView
  0 rightControlOutcomesEqual : leftOutcome = rightControlOutcome

public export
0 unloadingRightControls :
  {key, world, error, name : Type} -> {value : key -> Type} ->
  {deps : List key} -> {provision : CoeffectSpec key} ->
  {leftAccumulator : LocalState key value world provision ->
    LocalState key value world provision} ->
  {leftView : View name deps} -> {leftOutcome : Maybe error} ->
  {rightLifecycle : Lifecycle key value world error name deps provision} ->
  LifecycleControlRelated
    (Unloading leftAccumulator leftView leftOutcome) rightLifecycle ->
  UnloadingRightControls leftAccumulator leftView leftOutcome rightLifecycle
unloadingRightControls {rightLifecycle = Unloading rightAccumulator rightView
  rightOutcome}
  (UnloadingControls accumulatorsSame viewsSame outcomesSame) =
    MkUnloadingRightControls rightAccumulator rightView rightOutcome Refl
      accumulatorsSame viewsSame outcomesSame

||| Reconstruct retained foreign L-Unload on the survivor. The saturated frame
||| transfers the false reliance guard. Related accumulators need not produce
||| equal proof-bearing tables or equal outputs across different ambient inputs;
||| control reconstruction observes only the common Inactive outcome, while the
||| already-transposed effect layer owns ambient/table agreement.
public export
0 replayForeignUnloadControls :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected, actor : name) -> Not (actor = selected) ->
  (planAmbient, survivorAmbient : world) ->
  (plan, survivor : Registry name key value world error) ->
  (leftOwner, rightOwner : Fiber name key value world error) ->
  lookupFiber @{nameEq} actor plan = Just leftOwner ->
  lookupFiber @{nameEq} actor survivor = Just rightOwner ->
  (frame : ForeignLifecycleGuardFrame name key world error value nameEq keyEq
    selected actor (dependencies
      (componentDependencies (fiberComponent leftOwner)))
    leftOwner rightOwner plan survivor) ->
  (tag : RuleTag) -> (planAfter : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq} (LUnload actor)
    (MkSystemState planAmbient plan) = Just (tag, planAfter) ->
  registryWellFormed @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error}
    (MkSystemState survivorAmbient survivor) = True ->
  ForeignLifecycleControlReplay name key world error value nameEq keyEq
    selected (LUnload actor) tag planAfter
    (MkSystemState survivorAmbient survivor)
replayForeignUnloadControls nameEq keyEq selected actor actorDistinct planAmbient
  survivorAmbient plan survivor leftOwner rightOwner leftFound rightFound frame
  tag planAfter planRaw survivorWellFormed =
    case fst (lUnloadBoundary nameEq keyEq actor
      (MkSystemState planAmbient plan) planAfter tag planRaw) of
      Refl => case foreignUnloadPlanView nameEq keyEq actor planAmbient plan tag
        planAfter planRaw of
        MkLocatedForeignUnloadPlanView observedOwner observedFound planView =>
          let 0 ownerSame : (observedOwner = leftOwner)
              ownerSame = justInjective (trans (sym observedFound) leftFound)
          in case ownerSame of
            Refl => case planView of
              MkForeignUnloadPlanView component leftParent leftRetired leftTable
                leftAccumulator leftView leftOutcome ownerShape leftUnrelied =>
                  case ownerShape of
                    Refl => case frame of
                      MkForeignLifecycleGuardFrame sources
                        (FibersControlRelated leftParent rightParent leftRetired
                          rightRetired leftTable rightTable
                          (Unloading leftAccumulator leftView leftOutcome)
                          rightLifecycle parentSame retiredSame lifecycleSame)
                        relianceFrame =>
                        case unloadingRightControls lifecycleSame of
                          MkUnloadingRightControls rightAccumulator rightView
                            rightOutcome rightLifecycleShape accumulatorsSame
                            viewsSame outcomesSame =>
                              case rightLifecycleShape of
                                Refl => case viewsSame of
                                  Refl =>
                                    let 0 rightUnrelied : (relied @{nameEq}
                                          {name = name} {key = key} {value = value}
                                          {world = world} {error = error} actor
                                          survivor = False)
                                        rightUnrelied = relianceFrame leftUnrelied
                                        leftRestored : LocalState key value world
                                          (componentProvisions component)
                                        leftRestored = leftAccumulator
                                          (MkLocalState planAmbient
                                            (restrictOwnedPreservingOrder @{keyEq}
                                              (componentProvisions component)
                                              (ownedValues leftTable)))
                                        rightRestored : LocalState key value world
                                          (componentProvisions component)
                                        rightRestored = rightAccumulator
                                          (MkLocalState survivorAmbient
                                            (restrictOwnedPreservingOrder @{keyEq}
                                              (componentProvisions component)
                                              (ownedValues rightTable)))
                                        leftNext : Fiber name key value world error
                                        leftNext = MkFiber component leftParent
                                          leftRetired (localTable leftRestored)
                                          (Inactive leftOutcome)
                                        0 planConcreteRaw : applyAction @{nameEq}
                                          @{keyEq} (LUnload actor)
                                          (MkSystemState planAmbient plan) =
                                          Just (LUnloadTag,
                                            the (SystemState name key value
                                              world error)
                                              (MkSystemState
                                                (localWorld leftRestored)
                                                (replaceBinding @{nameEq} actor
                                                  leftNext plan)))
                                        planConcreteRaw = rewrite leftFound in
                                          rewrite leftUnrelied in Refl
                                        0 planReduced :
                                          Just (LUnloadTag,
                                            the (SystemState name key value
                                              world error)
                                              (MkSystemState
                                                (localWorld leftRestored)
                                                (replaceBinding @{nameEq} actor
                                                  leftNext plan))) =
                                          Just (LUnloadTag, planAfter)
                                        planReduced = trans
                                          (sym planConcreteRaw) planRaw
                                        0 planAfterShape :
                                          MkSystemState (localWorld leftRestored)
                                            (replaceBinding @{nameEq} actor
                                              leftNext plan) = planAfter
                                        planAfterShape = cong snd
                                          (justInjective planReduced)
                                        rightNext : Fiber name key value world error
                                        rightNext = MkFiber component rightParent
                                          rightRetired (localTable rightRestored)
                                          (Inactive rightOutcome)
                                        survivorAfter : SystemState name key value
                                          world error
                                        survivorAfter = MkSystemState
                                          (localWorld rightRestored)
                                          (replaceBinding @{nameEq} actor rightNext
                                            survivor)
                                        0 survivorRaw : applyAction @{nameEq}
                                          @{keyEq} (LUnload actor)
                                          (MkSystemState survivorAmbient survivor) =
                                            Just (LUnloadTag, survivorAfter)
                                        survivorRaw = rewrite rightFound in
                                          rewrite rightUnrelied in Refl
                                        0 survivorAfterWellFormed :
                                          registryWellFormed @{nameEq} @{keyEq}
                                            survivorAfter = True
                                        survivorAfterWellFormed =
                                          preservationTheoremProof nameEq keyEq
                                            (LUnload actor)
                                            (MkSystemState survivorAmbient survivor)
                                            survivorAfter LUnloadTag
                                            survivorWellFormed survivorRaw
                                        0 survivorChecked : checkedApplyAction
                                          @{nameEq} @{keyEq} (LUnload actor)
                                          (MkSystemState survivorAmbient survivor) =
                                            Just (LUnloadTag, survivorAfter)
                                        survivorChecked = rewrite survivorRaw in
                                          rewrite survivorAfterWellFormed in Refl
                                        0 nextLifecycle : LifecycleControlRelated
                                          (Inactive leftOutcome)
                                          (Inactive rightOutcome)
                                        nextLifecycle = InactiveControls outcomesSame
                                        0 nextOwnerControls : FiberControlRelated
                                          leftNext rightNext
                                        nextOwnerControls = FibersControlRelated
                                          leftParent rightParent leftRetired
                                          rightRetired (localTable leftRestored)
                                          (localTable rightRestored)
                                          (Inactive leftOutcome)
                                          (Inactive rightOutcome) parentSame
                                          retiredSame nextLifecycle
                                        0 sourceOrdered :
                                          SelectedOrderedRegistryControlsRelated
                                            name key world error value selected
                                            (bindings plan) (bindings survivor)
                                        sourceOrdered =
                                          foreignLifecycleSourcesGiveSelectedOrdered
                                            sources
                                        0 replacedOrdered :
                                          SelectedOrderedRegistryControlsRelated
                                            name key world error value selected
                                            (replaceEntries @{nameEq} actor leftNext
                                              (bindings plan))
                                            (replaceEntries @{nameEq} actor rightNext
                                              (bindings survivor))
                                        replacedOrdered =
                                          selectedOrderedReplaceForeign nameEq
                                            selected actor actorDistinct leftNext
                                            rightNext nextOwnerControls
                                            (bindings plan) (bindings survivor)
                                            sourceOrdered
                                        0 planBindings : bindings
                                          (replaceBinding @{nameEq} actor leftNext
                                            plan) = replaceEntries @{nameEq} actor
                                              leftNext (bindings plan)
                                        planBindings =
                                          replaceBindingRuntimeBindings nameEq actor
                                            leftNext plan
                                        0 survivorBindings : bindings
                                          (replaceBinding @{nameEq} actor rightNext
                                            survivor) = replaceEntries @{nameEq}
                                              actor rightNext (bindings survivor)
                                        survivorBindings =
                                          replaceBindingRuntimeBindings nameEq actor
                                            rightNext survivor
                                        0 finalOrderedConcrete :
                                          SelectedOrderedRegistryControlsRelated
                                            name key world error value selected
                                            (bindings (replaceBinding @{nameEq}
                                              actor leftNext plan))
                                            (bindings (replaceBinding @{nameEq}
                                              actor rightNext survivor))
                                        finalOrderedConcrete =
                                          selectedOrderedTransport
                                            (sym planBindings)
                                            (sym survivorBindings)
                                            replacedOrdered
                                        0 finalOrdered :
                                          SelectedOrderedRegistryControlsRelated
                                            name key world error value selected
                                            (bindings (registry planAfter))
                                            (bindings (replaceBinding @{nameEq}
                                              actor rightNext survivor))
                                        finalOrdered = selectedOrderedTransport
                                          (cong (\state => bindings
                                            (registry state)) planAfterShape)
                                          Refl finalOrderedConcrete
                                    in MkForeignLifecycleControlReplay survivorAfter
                                      survivorRaw survivorChecked finalOrdered
