module DGamma.CP4DeletionSelectedForeignLifecycleLeave

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionCommuteCore
import DGamma.CP4DeletionSelectedBoundary
import DGamma.CP4DeletionSelectedForeignLifecycleCore
import DGamma.CP4DeletionSelectedForeignLifecycleGuards
import DGamma.CP4DeletionSelectedForeignLifecycleReplayCore
import Decidable.Equality

%default total

0 nothingNotJustForeignLeave : Nothing = Just item -> Void
nothingNotJustForeignLeave Refl impossible

public export
data ForeignLeavePlanView :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor : name) -> (ambient : world) ->
  (plan : Registry name key value world error) ->
  (owner : Fiber name key value world error) ->
  RuleTag -> SystemState name key value world error -> Type where
  MkForeignLeavePlanView :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {keyEq : DecEq key} ->
    {actor : name} -> {ambient : world} ->
    {plan : Registry name key value world error} ->
    {component : Component key value world error} ->
    {parent : Parent name} -> {retiredFlag : Bool} ->
    {table : OwnedTable key value (componentProvisions component)} ->
    (accumulator : LocalState key value world (componentProvisions component) ->
      LocalState key value world (componentProvisions component)) ->
    (view : View name (dependencies (componentDependencies component))) ->
    targetMatches @{nameEq}
      (targetFiber @{nameEq} @{keyEq}
        (MkFiber component parent retiredFlag table
          (Active accumulator view)) plan) view = False ->
    ForeignLeavePlanView name key world error value nameEq keyEq actor ambient
      plan
      (MkFiber component parent retiredFlag table (Active accumulator view))
      LLeaveTag
      (MkSystemState ambient
        (replaceBinding @{nameEq} actor
          (MkFiber component parent retiredFlag table
            (Unloading accumulator view Nothing)) plan))

record LocatedForeignLeavePlanView
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (actor : name) (ambient : world)
  (plan : Registry name key value world error)
  (tag : RuleTag) (afterState : SystemState name key value world error) where
  constructor MkLocatedForeignLeavePlanView
  leavePlanOwner : Fiber name key value world error
  0 leavePlanOwnerFound : lookupFiber @{nameEq} actor plan =
    Just leavePlanOwner
  0 leavePlanView : ForeignLeavePlanView name key world error value nameEq
    keyEq actor ambient plan leavePlanOwner tag afterState

0 foreignLeavePlanView :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (plan : Registry name key value world error) ->
  (tag : RuleTag) -> (afterState : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq} (LLeave actor)
    (MkSystemState ambient plan) = Just (tag, afterState) ->
  LocatedForeignLeavePlanView name key world error value nameEq keyEq actor
    ambient plan tag afterState
foreignLeavePlanView nameEq keyEq actor ambient plan tag afterState raw
  with (lookupFiber @{nameEq} actor plan) proof found
  foreignLeavePlanView nameEq keyEq actor ambient plan tag afterState raw |
    Nothing = void (nothingNotJustForeignLeave raw)
  foreignLeavePlanView nameEq keyEq actor ambient plan tag afterState raw |
    Just (MkFiber component parent retiredFlag table (Inactive outcome)) =
      void (nothingNotJustForeignLeave raw)
  foreignLeavePlanView nameEq keyEq actor ambient plan tag afterState raw |
    Just (MkFiber component parent retiredFlag table
      (Reloading remaining accumulator view)) =
        void (nothingNotJustForeignLeave raw)
  foreignLeavePlanView nameEq keyEq actor ambient plan tag afterState raw |
    Just (MkFiber component parent retiredFlag table
      (Active accumulator view))
    with (targetMatches @{nameEq}
      (targetFiber @{nameEq} @{keyEq}
        (MkFiber component parent retiredFlag table
          (Active accumulator view)) plan) view) proof matches
    foreignLeavePlanView nameEq keyEq actor ambient plan tag afterState raw |
      Just (MkFiber component parent retiredFlag table
        (Active accumulator view)) | True =
          void (nothingNotJustForeignLeave raw)
    foreignLeavePlanView nameEq keyEq actor ambient plan tag afterState raw |
      Just (MkFiber component parent retiredFlag table
        (Active accumulator view)) | False =
          case justInjective raw of
            Refl => MkLocatedForeignLeavePlanView
              (MkFiber component parent retiredFlag table
                (Active accumulator view)) found
              (MkForeignLeavePlanView accumulator view matches)
  foreignLeavePlanView nameEq keyEq actor ambient plan tag afterState raw |
    Just (MkFiber component parent retiredFlag table
      (Unloading accumulator view outcome)) =
        void (nothingNotJustForeignLeave raw)

0 targetFiberFromResolveSameForeignLeave :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (component : Component key value world error) ->
  (leftParent, rightParent : Parent name) ->
  (leftRetired, rightRetired : Bool) ->
  leftRetired = rightRetired ->
  (leftTable, rightTable : OwnedTable key value
    (componentProvisions component)) ->
  (leftLifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies component))
    (componentProvisions component)) ->
  (rightLifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies component))
    (componentProvisions component)) ->
  (left, right : Registry name key value world error) ->
  resolveView @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error}
    (dependencies (componentDependencies component)) left =
  resolveView @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error}
    (dependencies (componentDependencies component)) right ->
  targetFiber @{nameEq} @{keyEq}
    (MkFiber component leftParent leftRetired leftTable leftLifecycle) left =
  targetFiber @{nameEq} @{keyEq}
    (MkFiber component rightParent rightRetired rightTable rightLifecycle) right
targetFiberFromResolveSameForeignLeave nameEq keyEq component leftParent
  rightParent False False Refl leftTable rightTable leftLifecycle
  rightLifecycle left right same =
    trans (targetFiberExplicit nameEq keyEq component leftParent False
      leftTable leftLifecycle left)
      (trans same
        (sym (targetFiberExplicit nameEq keyEq component rightParent False
          rightTable rightLifecycle right)))
targetFiberFromResolveSameForeignLeave nameEq keyEq component leftParent
  rightParent True True Refl leftTable rightTable leftLifecycle rightLifecycle
  left right same =
    trans (targetFiberExplicit nameEq keyEq component leftParent True leftTable
      leftLifecycle left)
      (sym (targetFiberExplicit nameEq keyEq component rightParent True
        rightTable rightLifecycle right))

record ActiveRightControls
  {key, world, error, name : Type} {value : key -> Type}
  {deps : List key} {provision : CoeffectSpec key}
  (leftAccumulator : LocalState key value world provision ->
    LocalState key value world provision)
  (leftView : View name deps)
  (rightLifecycle : Lifecycle key value world error name deps provision) where
  constructor MkActiveRightControls
  rightControlAccumulator : LocalState key value world provision ->
    LocalState key value world provision
  rightControlView : View name deps
  0 rightControlLifecycle : rightLifecycle = Active rightControlAccumulator
    rightControlView
  0 rightControlAccumulatorsEqual : AccumulatorRelated leftAccumulator
    rightControlAccumulator
  0 rightControlViewsEqual : leftView = rightControlView

0 activeRightControls :
  {key, world, error, name : Type} -> {value : key -> Type} ->
  {deps : List key} -> {provision : CoeffectSpec key} ->
  {leftAccumulator : LocalState key value world provision ->
    LocalState key value world provision} ->
  {leftView : View name deps} ->
  {rightLifecycle : Lifecycle key value world error name deps provision} ->
  LifecycleControlRelated
    (Active leftAccumulator leftView) rightLifecycle ->
  ActiveRightControls leftAccumulator leftView rightLifecycle
activeRightControls {rightLifecycle = Active rightAccumulator rightView}
  (ActiveControls accumulatorsSame viewsSame) =
    MkActiveRightControls rightAccumulator rightView Refl accumulatorsSame
      viewsSame

||| Reconstruct retained foreign L-Leave on the survivor. The saturated source
||| relation preserves the owner's exact committed target scan, so the stale
||| target remains stale after the selected episode is erased.
public export
0 replayForeignLeaveControls :
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
  applyAction @{nameEq} @{keyEq} (LLeave actor)
    (MkSystemState planAmbient plan) = Just (tag, planAfter) ->
  registryWellFormed @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error}
    (MkSystemState survivorAmbient survivor) = True ->
  ForeignLifecycleControlReplay name key world error value nameEq keyEq
    selected (LLeave actor) tag planAfter
    (MkSystemState survivorAmbient survivor)
replayForeignLeaveControls nameEq keyEq selected actor actorDistinct planAmbient
  survivorAmbient plan survivor leftOwner rightOwner leftFound rightFound frame
  tag planAfter planRaw survivorWellFormed =
    case foreignLeavePlanView nameEq keyEq actor planAmbient plan tag planAfter
      planRaw of
      MkLocatedForeignLeavePlanView observedOwner observedFound planView =>
        let 0 ownerSame : (observedOwner = leftOwner)
            ownerSame = justInjective (trans (sym observedFound) leftFound)
        in case ownerSame of
          Refl => case planView of
            MkForeignLeavePlanView {component} {parent = leftParent}
              {retiredFlag = leftRetired} {table = leftTable}
              leftAccumulator leftView leftMismatch =>
                case frame of
                  MkForeignLifecycleGuardFrame sources
                    (FibersControlRelated leftParent rightParent leftRetired
                      rightRetired leftTable rightTable
                      (Active leftAccumulator leftView)
                      rightLifecycle parentSame retiredSame lifecycleSame)
                    relianceFrame =>
                      case activeRightControls lifecycleSame of
                        MkActiveRightControls rightAccumulator rightView
                          rightLifecycleShape accumulatorsSame viewsSame =>
                            case rightLifecycleShape of
                              Refl => case viewsSame of
                                Refl =>
                                    let 0 targetScanSame =
                                          foreignLifecycleResolveViewSame nameEq keyEq
                                            (dependencies
                                              (componentDependencies component))
                                            plan survivor sources
                                        0 targetsSame :
                                          (targetFiber @{nameEq} @{keyEq}
                                            (MkFiber component leftParent leftRetired
                                              leftTable
                                              (Active leftAccumulator leftView))
                                            plan =
                                           targetFiber @{nameEq} @{keyEq}
                                            (MkFiber component rightParent rightRetired
                                              rightTable
                                              (Active rightAccumulator leftView))
                                            survivor)
                                        targetsSame = targetFiberFromResolveSameForeignLeave
                                          nameEq keyEq component leftParent rightParent
                                          leftRetired rightRetired retiredSame leftTable
                                          rightTable
                                          (Active leftAccumulator leftView)
                                          (Active rightAccumulator leftView)
                                          plan survivor targetScanSame
                                        0 rightMismatch :
                                          (targetMatches @{nameEq}
                                            (targetFiber @{nameEq} @{keyEq}
                                              (MkFiber component rightParent rightRetired
                                                rightTable
                                                (Active rightAccumulator leftView))
                                              survivor) leftView = False)
                                        rightMismatch = trans
                                          (cong (\target => targetMatches @{nameEq} target
                                            leftView) (sym targetsSame)) leftMismatch
                                        leftNext : Fiber name key value world error
                                        leftNext = MkFiber component leftParent leftRetired
                                          leftTable
                                          (Unloading leftAccumulator leftView Nothing)
                                        rightNext : Fiber name key value world error
                                        rightNext = MkFiber component rightParent
                                          rightRetired rightTable
                                          (Unloading rightAccumulator leftView Nothing)
                                        survivorAfter : SystemState name key value world error
                                        survivorAfter = MkSystemState survivorAmbient
                                          (replaceBinding @{nameEq} actor rightNext survivor)
                                        0 survivorRaw : applyAction @{nameEq} @{keyEq}
                                          (LLeave actor)
                                          (MkSystemState survivorAmbient survivor) =
                                            Just (LLeaveTag, survivorAfter)
                                        survivorRaw = rewrite rightFound in
                                          rewrite rightMismatch in Refl
                                        0 survivorAfterWellFormed :
                                          registryWellFormed @{nameEq} @{keyEq}
                                            survivorAfter = True
                                        survivorAfterWellFormed = preservationTheoremProof
                                          nameEq keyEq (LLeave actor)
                                          (MkSystemState survivorAmbient survivor)
                                          survivorAfter LLeaveTag survivorWellFormed
                                          survivorRaw
                                        0 survivorChecked : checkedApplyAction @{nameEq}
                                          @{keyEq} (LLeave actor)
                                          (MkSystemState survivorAmbient survivor) =
                                            Just (LLeaveTag, survivorAfter)
                                        survivorChecked = rewrite survivorRaw in
                                          rewrite survivorAfterWellFormed in Refl
                                        0 nextLifecycle : LifecycleControlRelated
                                          (Unloading leftAccumulator leftView
                                            (the (Maybe error) Nothing))
                                          (Unloading rightAccumulator leftView
                                            (the (Maybe error) Nothing))
                                        nextLifecycle = UnloadingControls
                                          {error = error} accumulatorsSame Refl Refl
                                        0 nextOwnerControls : FiberControlRelated leftNext
                                          rightNext
                                        nextOwnerControls = FibersControlRelated leftParent
                                          rightParent leftRetired rightRetired leftTable
                                          rightTable
                                          (Unloading leftAccumulator leftView Nothing)
                                          (Unloading rightAccumulator leftView Nothing)
                                          parentSame retiredSame nextLifecycle
                                        0 sourceOrdered :
                                          SelectedOrderedRegistryControlsRelated name key
                                            world error value selected (bindings plan)
                                            (bindings survivor)
                                        sourceOrdered =
                                          foreignLifecycleSourcesGiveSelectedOrdered sources
                                        0 replacedOrdered :
                                          SelectedOrderedRegistryControlsRelated name key
                                            world error value selected
                                            (replaceEntries @{nameEq} actor leftNext
                                              (bindings plan))
                                            (replaceEntries @{nameEq} actor rightNext
                                              (bindings survivor))
                                        replacedOrdered = selectedOrderedReplaceForeign
                                          nameEq selected actor actorDistinct leftNext
                                          rightNext nextOwnerControls (bindings plan)
                                          (bindings survivor) sourceOrdered
                                        0 planBindings : bindings
                                          (replaceBinding @{nameEq} actor leftNext plan) =
                                          replaceEntries @{nameEq} actor leftNext
                                            (bindings plan)
                                        planBindings = replaceBindingRuntimeBindings nameEq
                                          actor leftNext plan
                                        0 survivorBindings : bindings
                                          (replaceBinding @{nameEq} actor rightNext
                                            survivor) =
                                          replaceEntries @{nameEq} actor rightNext
                                            (bindings survivor)
                                        survivorBindings = replaceBindingRuntimeBindings
                                          nameEq actor rightNext survivor
                                        0 finalOrdered :
                                          SelectedOrderedRegistryControlsRelated name key
                                            world error value selected
                                            (bindings (replaceBinding @{nameEq} actor
                                              leftNext plan))
                                            (bindings (replaceBinding @{nameEq} actor
                                              rightNext survivor))
                                        finalOrdered = selectedOrderedTransport
                                          (sym planBindings) (sym survivorBindings)
                                          replacedOrdered
                                    in MkForeignLifecycleControlReplay survivorAfter
                                      survivorRaw survivorChecked finalOrdered
