module DGamma.CP4DeletionSelectedForeignLifecycleBegin

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

0 nothingNotJustForeignBegin : Nothing = Just item -> Void
nothingNotJustForeignBegin Refl impossible

public export
data ForeignBeginPlanView :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor : name) -> (ambient : world) ->
  (plan : Registry name key value world error) ->
  (owner : Fiber name key value world error) ->
  RuleTag -> SystemState name key value world error -> Type where
  MkForeignBeginPlanView :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {keyEq : DecEq key} ->
    {actor : name} -> {ambient : world} ->
    {plan : Registry name key value world error} ->
    {component : Component key value world error} ->
    {parent : Parent name} ->
    {table : OwnedTable key value (componentProvisions component)} ->
    (view : View name
      (dependencies (componentDependencies component))) ->
    (targetFound : targetFiber @{nameEq} @{keyEq}
      (MkFiber component parent False table (Inactive Nothing)) plan =
        Just view) ->
    ForeignBeginPlanView name key world error value nameEq keyEq actor ambient
      plan (MkFiber component parent False table (Inactive Nothing))
      LBeginTag
      (MkSystemState ambient
        (replaceBinding @{nameEq} actor
          (MkFiber component parent False table
            (Reloading (componentProgram component) (\local => local) view))
          plan))

0 applyBeginAtFound :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (plan : Registry name key value world error) ->
  (owner : Fiber name key value world error) ->
  lookupFiber @{nameEq} actor plan = Just owner ->
  applyAction @{nameEq} @{keyEq} (LBegin actor)
    (MkSystemState ambient plan) =
  beginFiberAction @{nameEq} @{keyEq} actor owner
    (MkSystemState ambient plan)
applyBeginAtFound nameEq keyEq actor ambient plan owner found =
  rewrite found in Refl

0 foreignBeginUnretiredPlanView :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (plan : Registry name key value world error) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (tag : RuleTag) -> (afterState : SystemState name key value world error) ->
  beginFiberAction @{nameEq} @{keyEq} actor
    (MkFiber component parent False table (Inactive Nothing))
    (MkSystemState ambient plan) = Just (tag, afterState) ->
  ForeignBeginPlanView name key world error value nameEq keyEq actor ambient
    plan (MkFiber component parent False table (Inactive Nothing)) tag afterState
foreignBeginUnretiredPlanView nameEq keyEq actor ambient plan component parent
  table tag afterState raw
  with (targetFiber @{nameEq} @{keyEq}
    (MkFiber component parent False table (Inactive Nothing)) plan) proof target
  foreignBeginUnretiredPlanView nameEq keyEq actor ambient plan component parent
    table tag afterState raw | Nothing =
      void (nothingNotJustForeignBegin raw)
  foreignBeginUnretiredPlanView nameEq keyEq actor ambient plan component parent
    table tag afterState raw | Just view =
      case justInjective raw of
        Refl => MkForeignBeginPlanView view target

0 foreignBeginInactivePlanView :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (plan : Registry name key value world error) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (tag : RuleTag) -> (afterState : SystemState name key value world error) ->
  beginFiberAction @{nameEq} @{keyEq} actor
    (MkFiber component parent retiredFlag table (Inactive Nothing))
    (MkSystemState ambient plan) = Just (tag, afterState) ->
  ForeignBeginPlanView name key world error value nameEq keyEq actor ambient
    plan (MkFiber component parent retiredFlag table (Inactive Nothing)) tag
    afterState
foreignBeginInactivePlanView nameEq keyEq actor ambient plan component parent
  False table tag afterState raw = foreignBeginUnretiredPlanView nameEq keyEq
    actor ambient plan component parent table tag afterState raw
foreignBeginInactivePlanView nameEq keyEq actor ambient plan component parent
  True table tag afterState raw = void (nothingNotJustForeignBegin raw)

0 foreignBeginPlanViewAtOwner :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (plan : Registry name key value world error) ->
  (owner : Fiber name key value world error) ->
  (tag : RuleTag) -> (afterState : SystemState name key value world error) ->
  beginFiberAction @{nameEq} @{keyEq} actor owner
    (MkSystemState ambient plan) = Just (tag, afterState) ->
  ForeignBeginPlanView name key world error value nameEq keyEq actor ambient
    plan owner tag afterState
foreignBeginPlanViewAtOwner nameEq keyEq actor ambient plan
  (MkFiber component parent retiredFlag table (Inactive Nothing)) tag afterState
  raw = foreignBeginInactivePlanView nameEq keyEq actor ambient plan component
    parent retiredFlag table tag afterState raw
foreignBeginPlanViewAtOwner nameEq keyEq actor ambient plan
  (MkFiber component parent retiredFlag table (Inactive (Just failure))) tag
  afterState raw = void (nothingNotJustForeignBegin raw)
foreignBeginPlanViewAtOwner nameEq keyEq actor ambient plan
  (MkFiber component parent retiredFlag table
    (Reloading remaining accumulator view)) tag afterState raw =
      void (nothingNotJustForeignBegin raw)
foreignBeginPlanViewAtOwner nameEq keyEq actor ambient plan
  (MkFiber component parent retiredFlag table (Active accumulator view)) tag
  afterState raw = void (nothingNotJustForeignBegin raw)
foreignBeginPlanViewAtOwner nameEq keyEq actor ambient plan
  (MkFiber component parent retiredFlag table
    (Unloading accumulator view outcome)) tag afterState raw =
      void (nothingNotJustForeignBegin raw)

0 foreignBeginPlanView :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (plan : Registry name key value world error) ->
  (owner : Fiber name key value world error) ->
  lookupFiber @{nameEq} actor plan = Just owner ->
  (tag : RuleTag) -> (afterState : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq} (LBegin actor)
    (MkSystemState ambient plan) = Just (tag, afterState) ->
  ForeignBeginPlanView name key world error value nameEq keyEq actor ambient
    plan owner tag afterState
foreignBeginPlanView nameEq keyEq actor ambient plan owner found tag afterState
  raw = foreignBeginPlanViewAtOwner nameEq keyEq actor ambient plan owner tag
    afterState (trans (sym (applyBeginAtFound nameEq keyEq actor ambient plan
      owner found)) raw)

||| Reconstruct a retained foreign L-Begin on the recovered survivor.  The
||| saturated provider scan gives the exact dependent target view; the source
||| control relation fixes the same component/program and clean Inactive state.
public export
0 replayForeignBeginControls :
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
  applyAction @{nameEq} @{keyEq} (LBegin actor)
    (MkSystemState planAmbient plan) = Just (tag, planAfter) ->
  registryWellFormed @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error}
    (MkSystemState survivorAmbient survivor) = True ->
  ForeignLifecycleControlReplay name key world error value nameEq keyEq
    selected (LBegin actor) tag planAfter
    (MkSystemState survivorAmbient survivor)
replayForeignBeginControls nameEq keyEq selected actor actorDistinct planAmbient
  survivorAmbient plan survivor leftOwner rightOwner leftFound rightFound
  frame tag planAfter planRaw survivorWellFormed =
    case foreignBeginPlanView nameEq keyEq actor planAmbient plan leftOwner
      leftFound tag planAfter planRaw of
      MkForeignBeginPlanView {component} {parent = leftParent}
        {table = leftTable} view leftTarget =>
        case frame of
          MkForeignLifecycleGuardFrame sources
            (FibersControlRelated leftParent rightParent False rightRetired
              leftTable rightTable (Inactive Nothing) rightLifecycle parentSame
              retiredSame lifecycleSame)
            relianceFrame =>
              case lifecycleSame of
                InactiveControls outcomeSame =>
                  case outcomeSame of
                    Refl => case retiredSame of
                      Refl =>
                          let 0 targetScanSame :
                                (resolveView @{nameEq} @{keyEq} {name = name}
                                  {key = key} {value = value} {world = world}
                                  {error = error} (dependencies
                                    (componentDependencies component)) plan =
                                 resolveView @{nameEq} @{keyEq} {name = name}
                                  {key = key} {value = value} {world = world}
                                  {error = error} (dependencies
                                    (componentDependencies component)) survivor)
                              targetScanSame =
                                foreignLifecycleResolveViewSame nameEq keyEq
                                  (dependencies
                                    (componentDependencies component))
                                  plan survivor sources
                              0 leftExplicit :
                                (targetFiber @{nameEq} @{keyEq}
                                  (MkFiber component leftParent False leftTable
                                    (Inactive Nothing)) plan =
                                 resolveView @{nameEq} @{keyEq} {name = name}
                                  {key = key} {value = value} {world = world}
                                  {error = error} (dependencies
                                    (componentDependencies component)) plan)
                              leftExplicit = targetFiberExplicit nameEq keyEq
                                component leftParent False leftTable
                                (Inactive Nothing) plan
                              0 leftResolve :
                                (resolveView @{nameEq} @{keyEq} {name = name}
                                  {key = key} {value = value} {world = world}
                                  {error = error} (dependencies
                                    (componentDependencies component)) plan =
                                  Just view)
                              leftResolve = trans (sym leftExplicit) leftTarget
                              0 rightExplicit :
                                (targetFiber @{nameEq} @{keyEq}
                                  (MkFiber component rightParent False rightTable
                                    (Inactive Nothing)) survivor =
                                 resolveView @{nameEq} @{keyEq} {name = name}
                                  {key = key} {value = value} {world = world}
                                  {error = error} (dependencies
                                    (componentDependencies component)) survivor)
                              rightExplicit = targetFiberExplicit nameEq keyEq
                                component rightParent False rightTable
                                (Inactive Nothing) survivor
                              0 rightTarget : (targetFiber @{nameEq} @{keyEq}
                                (MkFiber component rightParent False rightTable
                                  (Inactive Nothing)) survivor = Just view)
                              rightTarget = trans rightExplicit
                                (trans (sym targetScanSame) leftResolve)
                              leftNext : Fiber name key value world error
                              leftNext = MkFiber component leftParent False
                                leftTable
                                (Reloading (componentProgram component)
                                  (\local => local) view)
                              rightNext : Fiber name key value world error
                              rightNext = MkFiber component rightParent False
                                rightTable
                                (Reloading (componentProgram component)
                                  (\local => local) view)
                              survivorAfter : SystemState name key value world error
                              survivorAfter = MkSystemState survivorAmbient
                                (replaceBinding @{nameEq} actor rightNext survivor)
                              0 survivorRaw : applyAction @{nameEq} @{keyEq}
                                (LBegin actor)
                                (MkSystemState survivorAmbient survivor) =
                                  Just (LBeginTag, survivorAfter)
                              survivorRaw = rewrite rightFound in
                                rewrite rightTarget in Refl
                              0 survivorAfterWellFormed :
                                registryWellFormed @{nameEq} @{keyEq}
                                  survivorAfter = True
                              survivorAfterWellFormed = preservationTheoremProof
                                nameEq keyEq (LBegin actor)
                                (MkSystemState survivorAmbient survivor)
                                survivorAfter LBeginTag survivorWellFormed
                                survivorRaw
                              0 survivorChecked :
                                checkedApplyAction @{nameEq} @{keyEq}
                                  (LBegin actor)
                                  (MkSystemState survivorAmbient survivor) =
                                    Just (LBeginTag, survivorAfter)
                              survivorChecked = rewrite survivorRaw in
                                rewrite survivorAfterWellFormed in Refl
                              0 nextOwnerControls :
                                FiberControlRelated leftNext rightNext
                              nextOwnerControls = FibersControlRelated leftParent
                                rightParent False False leftTable rightTable
                                (Reloading (componentProgram component)
                                  (\local => local) view)
                                (Reloading (componentProgram component)
                                  (\local => local) view)
                                parentSame Refl
                                (beginLifecycleControlRelated
                                  (componentProgram component) view)
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
