module DGamma.CP4DeletionSelectedForeignLifecycleDivert

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

0 nothingNotJustForeignDivert : Nothing = Just item -> Void
nothingNotJustForeignDivert Refl impossible

public export
data ForeignDivertPlanView :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor : name) -> (ambient : world) ->
  (plan : Registry name key value world error) ->
  (owner : Fiber name key value world error) ->
  RuleTag -> SystemState name key value world error -> Type where
  MkForeignDivertPlanView :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {keyEq : DecEq key} ->
    {actor : name} -> {ambient : world} ->
    {plan : Registry name key value world error} ->
    {component : Component key value world error} ->
    {parent : Parent name} -> {retiredFlag : Bool} ->
    {table : OwnedTable key value (componentProvisions component)} ->
    (remaining : List (StepEffect key value world error
      (dependencies (componentDependencies component))
      (componentProvisions component))) ->
    (accumulator : LocalState key value world (componentProvisions component) ->
      LocalState key value world (componentProvisions component)) ->
    (view : View name (dependencies (componentDependencies component))) ->
    targetMatches @{nameEq}
      (targetFiber @{nameEq} @{keyEq}
        (MkFiber component parent retiredFlag table
          (Reloading remaining accumulator view)) plan) view = False ->
    ForeignDivertPlanView name key world error value nameEq keyEq actor ambient
      plan
      (MkFiber component parent retiredFlag table
        (Reloading remaining accumulator view))
      LDivertTag
      (MkSystemState ambient
        (replaceBinding @{nameEq} actor
          (MkFiber component parent retiredFlag table
            (Unloading accumulator view Nothing)) plan))

public export
record ForeignDivertReplayData
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (actor : name) (ambient : world)
  (plan : Registry name key value world error)
  (owner : Fiber name key value world error)
  (tag : RuleTag) (afterState : SystemState name key value world error) where
  constructor MkForeignDivertReplayData
  divertReplayComponent : Component key value world error
  divertReplayParent : Parent name
  divertReplayRetired : Bool
  divertReplayTable : OwnedTable key value
    (componentProvisions divertReplayComponent)
  divertReplayRemaining : List (StepEffect key value world error
    (dependencies (componentDependencies divertReplayComponent))
    (componentProvisions divertReplayComponent))
  divertReplayAccumulator : LocalState key value world
    (componentProvisions divertReplayComponent) ->
    LocalState key value world (componentProvisions divertReplayComponent)
  divertReplayView : View name
    (dependencies (componentDependencies divertReplayComponent))
  0 divertReplayOwnerShape : owner = MkFiber divertReplayComponent
    divertReplayParent divertReplayRetired divertReplayTable
    (Reloading divertReplayRemaining divertReplayAccumulator divertReplayView)
  0 divertReplayMismatch : targetMatches @{nameEq}
    (targetFiber @{nameEq} @{keyEq}
      (MkFiber divertReplayComponent divertReplayParent divertReplayRetired
        divertReplayTable
        (Reloading divertReplayRemaining divertReplayAccumulator
          divertReplayView)) plan) divertReplayView = False
  0 divertReplayTagShape : tag = LDivertTag
  0 divertReplayAfterShape : MkSystemState ambient
    (replaceBinding @{nameEq} actor
      (MkFiber divertReplayComponent divertReplayParent divertReplayRetired
        divertReplayTable
        (Unloading divertReplayAccumulator divertReplayView Nothing)) plan) =
    afterState

public export
0 foreignDivertReplayData :
  ForeignDivertPlanView name key world error value nameEq keyEq actor ambient
    plan owner tag afterState ->
  ForeignDivertReplayData name key world error value nameEq keyEq actor ambient
    plan owner tag afterState
foreignDivertReplayData
  (MkForeignDivertPlanView {component} {parent} {retiredFlag} {table}
    remaining accumulator view mismatch) =
      MkForeignDivertReplayData component parent retiredFlag table remaining
        accumulator view Refl mismatch Refl Refl

public export
0 foreignDivertPlanViewTag :
  ForeignDivertPlanView name key world error value nameEq keyEq actor ambient
    plan owner tag afterState -> tag = LDivertTag
foreignDivertPlanViewTag
  (MkForeignDivertPlanView remaining accumulator view mismatch) = Refl

public export
foreignDivertPlanAfter :
  ForeignDivertPlanView name key world error value nameEq keyEq actor ambient
    plan owner tag afterState -> SystemState name key value world error
foreignDivertPlanAfter
  (MkForeignDivertPlanView {component} {parent} {retiredFlag} {table}
    remaining accumulator view mismatch) =
      MkSystemState ambient (replaceBinding @{nameEq} actor
        (MkFiber component parent retiredFlag table
          (Unloading accumulator view Nothing)) plan)

public export
0 foreignDivertPlanAfterIsObserved :
  (witness : ForeignDivertPlanView name key world error value nameEq keyEq actor
    ambient plan owner tag afterState) ->
  foreignDivertPlanAfter witness = afterState
foreignDivertPlanAfterIsObserved
  (MkForeignDivertPlanView remaining accumulator view mismatch) = Refl

public export
record LocatedForeignDivertPlanView
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (actor : name) (ambient : world)
  (plan : Registry name key value world error)
  (tag : RuleTag) (afterState : SystemState name key value world error) where
  constructor MkLocatedForeignDivertPlanView
  divertPlanOwner : Fiber name key value world error
  0 divertPlanOwnerFound : lookupFiber @{nameEq} actor plan =
    Just divertPlanOwner
  0 divertPlanView : ForeignDivertPlanView name key world error value nameEq
    keyEq actor ambient plan divertPlanOwner tag afterState

public export
0 foreignDivertPlanView :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (plan : Registry name key value world error) ->
  (tag : RuleTag) -> (afterState : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq} (LDivert actor)
    (MkSystemState ambient plan) = Just (tag, afterState) ->
  LocatedForeignDivertPlanView name key world error value nameEq keyEq actor
    ambient plan tag afterState
foreignDivertPlanView nameEq keyEq actor ambient plan tag afterState raw
  with (lookupFiber @{nameEq} actor plan) proof found
  foreignDivertPlanView nameEq keyEq actor ambient plan tag afterState raw |
    Nothing = void (nothingNotJustForeignDivert raw)
  foreignDivertPlanView nameEq keyEq actor ambient plan tag afterState raw |
    Just (MkFiber component parent retiredFlag table (Inactive outcome)) =
      void (nothingNotJustForeignDivert raw)
  foreignDivertPlanView nameEq keyEq actor ambient plan tag afterState raw |
    Just (MkFiber component parent retiredFlag table
      (Reloading remaining accumulator view))
    with (targetMatches @{nameEq}
      (targetFiber @{nameEq} @{keyEq}
        (MkFiber component parent retiredFlag table
          (Reloading remaining accumulator view)) plan) view) proof matches
    foreignDivertPlanView nameEq keyEq actor ambient plan tag afterState raw |
      Just (MkFiber component parent retiredFlag table
        (Reloading remaining accumulator view)) | True =
          void (nothingNotJustForeignDivert raw)
    foreignDivertPlanView nameEq keyEq actor ambient plan tag afterState raw |
      Just (MkFiber component parent retiredFlag table
        (Reloading remaining accumulator view)) | False =
          case justInjective raw of
            Refl => MkLocatedForeignDivertPlanView
              (MkFiber component parent retiredFlag table
                (Reloading remaining accumulator view)) found
              (MkForeignDivertPlanView remaining accumulator view matches)
  foreignDivertPlanView nameEq keyEq actor ambient plan tag afterState raw |
    Just (MkFiber component parent retiredFlag table
      (Active accumulator view)) = void (nothingNotJustForeignDivert raw)
  foreignDivertPlanView nameEq keyEq actor ambient plan tag afterState raw |
    Just (MkFiber component parent retiredFlag table
      (Unloading accumulator view outcome)) =
        void (nothingNotJustForeignDivert raw)

public export
0 targetFiberFromResolveSameForeignDivert :
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
targetFiberFromResolveSameForeignDivert nameEq keyEq component leftParent
  rightParent False False Refl leftTable rightTable leftLifecycle
  rightLifecycle left right same =
    trans (targetFiberExplicit nameEq keyEq component leftParent False
      leftTable leftLifecycle left)
      (trans same
        (sym (targetFiberExplicit nameEq keyEq component rightParent False
          rightTable rightLifecycle right)))
targetFiberFromResolveSameForeignDivert nameEq keyEq component leftParent
  rightParent True True Refl leftTable rightTable leftLifecycle rightLifecycle
  left right same =
    trans (targetFiberExplicit nameEq keyEq component leftParent True leftTable
      leftLifecycle left)
      (sym (targetFiberExplicit nameEq keyEq component rightParent True
        rightTable rightLifecycle right))

public export
record ReloadingRightControls
  {key, world, error, name : Type} {value : key -> Type}
  {deps : List key} {provision : CoeffectSpec key}
  (leftRemaining : List (StepEffect key value world error deps provision))
  (leftAccumulator : LocalState key value world provision ->
    LocalState key value world provision)
  (leftView : View name deps)
  (rightLifecycle : Lifecycle key value world error name deps provision) where
  constructor MkReloadingRightControls
  rightControlRemaining : List
    (StepEffect key value world error deps provision)
  rightControlAccumulator : LocalState key value world provision ->
    LocalState key value world provision
  rightControlView : View name deps
  0 rightControlLifecycle : rightLifecycle = Reloading rightControlRemaining
    rightControlAccumulator rightControlView
  0 rightControlRemainingEqual : leftRemaining = rightControlRemaining
  0 rightControlAccumulatorsEqual : AccumulatorRelated leftAccumulator
    rightControlAccumulator
  0 rightControlViewsEqual : leftView = rightControlView

public export
0 reloadingRightControls :
  {key, world, error, name : Type} -> {value : key -> Type} ->
  {deps : List key} -> {provision : CoeffectSpec key} ->
  {leftRemaining : List (StepEffect key value world error deps provision)} ->
  {leftAccumulator : LocalState key value world provision ->
    LocalState key value world provision} ->
  {leftView : View name deps} ->
  {rightLifecycle : Lifecycle key value world error name deps provision} ->
  LifecycleControlRelated
    (Reloading leftRemaining leftAccumulator leftView) rightLifecycle ->
  ReloadingRightControls leftRemaining leftAccumulator leftView rightLifecycle
reloadingRightControls {rightLifecycle = Reloading rightRemaining
  rightAccumulator rightView}
  (ReloadingControls remainingSame accumulatorsSame viewsSame) =
    MkReloadingRightControls rightRemaining rightAccumulator rightView Refl
      remainingSame accumulatorsSame viewsSame

||| Reconstruct retained foreign L-Divert on the survivor. The saturated source
||| relation preserves the owner's exact committed target scan, so the stale
||| target remains stale after the selected episode is erased.
public export
0 replayForeignDivertControls :
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
  applyAction @{nameEq} @{keyEq} (LDivert actor)
    (MkSystemState planAmbient plan) = Just (tag, planAfter) ->
  registryWellFormed @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error}
    (MkSystemState survivorAmbient survivor) = True ->
  ForeignLifecycleControlReplay name key world error value nameEq keyEq
    selected (LDivert actor) tag planAfter
    (MkSystemState survivorAmbient survivor)
replayForeignDivertControls nameEq keyEq selected actor actorDistinct planAmbient
  survivorAmbient plan survivor leftOwner rightOwner leftFound rightFound frame
  tag planAfter planRaw survivorWellFormed =
    case foreignDivertPlanView nameEq keyEq actor planAmbient plan tag planAfter
      planRaw of
      MkLocatedForeignDivertPlanView observedOwner observedFound planView =>
        let 0 ownerSame : (observedOwner = leftOwner)
            ownerSame = justInjective (trans (sym observedFound) leftFound)
        in case ownerSame of
          Refl => case planView of
            MkForeignDivertPlanView {component} {parent = leftParent}
              {retiredFlag = leftRetired} {table = leftTable} remaining
              leftAccumulator leftView leftMismatch =>
                case frame of
                  MkForeignLifecycleGuardFrame sources
                    (FibersControlRelated leftParent rightParent leftRetired
                      rightRetired leftTable rightTable
                      (Reloading remaining leftAccumulator leftView)
                      rightLifecycle parentSame retiredSame lifecycleSame)
                    relianceFrame =>
                      case reloadingRightControls lifecycleSame of
                        MkReloadingRightControls rightRemaining rightAccumulator
                          rightView rightLifecycleShape remainingSame
                          accumulatorsSame viewsSame =>
                            case rightLifecycleShape of
                              Refl => case remainingSame of
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
                                              (Reloading remaining leftAccumulator
                                                leftView)) plan =
                                           targetFiber @{nameEq} @{keyEq}
                                            (MkFiber component rightParent rightRetired
                                              rightTable
                                              (Reloading remaining rightAccumulator
                                                leftView)) survivor)
                                        targetsSame = targetFiberFromResolveSameForeignDivert
                                          nameEq keyEq component leftParent rightParent
                                          leftRetired rightRetired retiredSame leftTable
                                          rightTable
                                          (Reloading remaining leftAccumulator leftView)
                                          (Reloading remaining rightAccumulator leftView)
                                          plan survivor targetScanSame
                                        0 rightMismatch :
                                          (targetMatches @{nameEq}
                                            (targetFiber @{nameEq} @{keyEq}
                                              (MkFiber component rightParent rightRetired
                                                rightTable
                                                (Reloading remaining rightAccumulator
                                                  leftView)) survivor) leftView = False)
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
                                          (LDivert actor)
                                          (MkSystemState survivorAmbient survivor) =
                                            Just (LDivertTag, survivorAfter)
                                        survivorRaw = rewrite rightFound in
                                          rewrite rightMismatch in Refl
                                        0 survivorAfterWellFormed :
                                          registryWellFormed @{nameEq} @{keyEq}
                                            survivorAfter = True
                                        survivorAfterWellFormed = preservationTheoremProof
                                          nameEq keyEq (LDivert actor)
                                          (MkSystemState survivorAmbient survivor)
                                          survivorAfter LDivertTag survivorWellFormed
                                          survivorRaw
                                        0 survivorChecked : checkedApplyAction @{nameEq}
                                          @{keyEq} (LDivert actor)
                                          (MkSystemState survivorAmbient survivor) =
                                            Just (LDivertTag, survivorAfter)
                                        survivorChecked = rewrite survivorRaw in
                                          rewrite survivorAfterWellFormed in Refl
                                        0 nextLifecycle : LifecycleControlRelated
                                          (Unloading leftAccumulator leftView Nothing)
                                          (Unloading rightAccumulator leftView Nothing)
                                        nextLifecycle = divertLifecycleControlRelated
                                          {leftRemaining = remaining}
                                          {rightRemaining = remaining}
                                          (ReloadingControls Refl accumulatorsSame Refl)
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
