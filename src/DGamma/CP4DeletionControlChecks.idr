module DGamma.CP4DeletionControlChecks

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.Metatheory
import DGamma.CP4DeletionControlPlan
import DGamma.CalculusChecks
import DGamma.Section3Example
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total

controlActorComponent : Component ToyKey ToyValue ToyRuntime String
controlActorComponent = MkComponent DGamma.CalculusChecks.toyEmptySpec
  DGamma.Section3Example.toySpecA [DGamma.CalculusChecks.providerFinish]

controlInertComponent : Component ToyKey ToyValue ToyRuntime String
controlInertComponent = MkComponent DGamma.CalculusChecks.toyEmptySpec
  DGamma.CalculusChecks.toyEmptySpec []

controlActorFiber : Fiber Nat ToyKey ToyValue ToyRuntime String
controlActorFiber = MkFiber controlActorComponent Root False emptyOwned
  (Reloading [DGamma.CalculusChecks.providerFinish] id EmptyView)

controlInertFiber : Fiber Nat ToyKey ToyValue ToyRuntime String
controlInertFiber = MkFiber controlInertComponent Root True emptyOwned
  (Inactive Nothing)

0 zeroNotOne : Not ((the Nat 0) = (the Nat 1))
zeroNotOne Refl impossible

0 zeroNotElemOne : Not (Elem (the Nat 0) [(the Nat 1)])
zeroNotElemOne Here impossible
zeroNotElemOne (There later) = absurd later

controlRegistry : Registry Nat ToyKey ToyValue ToyRuntime String
controlRegistry = MkCoeffectContext
  [Bind (the Nat 0) controlActorFiber, Bind (the Nat 1) controlInertFiber]
  (UniqueCons zeroNotElemOne (UniqueCons notInEmpty UniqueNil))

controlSource : SystemState Nat ToyKey ToyValue ToyRuntime String
controlSource = MkSystemState (MkToyRuntime False False) controlRegistry

controlAfter : SystemState Nat ToyKey ToyValue ToyRuntime String
controlAfter = MkSystemState (MkToyRuntime False False)
  (replaceBinding 0
    (setFiberRuntime controlActorFiber
      (restrictOwnedPreservingOrder DGamma.Section3Example.toySpecA
        (ownedValues (fiberTable controlActorFiber)))
      (Active (pushLocalUndo DGamma.Section3Example.toySpecA id id) EmptyView))
    controlRegistry)

0 controlEmptyViewValid :
  (fibers : Registry Nat ToyKey ToyValue ToyRuntime String) ->
  viewBindingsInvariant @{the (DecEq Nat) %search}
    @{the (DecEq ToyKey) %search} {name = Nat} {key = ToyKey}
    {value = ToyValue} {world = ToyRuntime} {error = String}
    [] EmptyView fibers = True
controlEmptyViewValid fibers = Refl

0 controlSourceWellFormed :
  registryWellFormed @{the (DecEq Nat) %search}
    @{the (DecEq ToyKey) %search}
    DGamma.CP4DeletionControlChecks.controlSource = True
controlSourceWellFormed =
  rewrite controlEmptyViewValid controlRegistry in Refl

0 controlAdvanceRaw :
  applyAction @{the (DecEq Nat) %search} @{the (DecEq ToyKey) %search}
    (LAdvance (the Nat 0)) DGamma.CP4DeletionControlChecks.controlSource =
      Just (LFinishTag, DGamma.CP4DeletionControlChecks.controlAfter)
controlAdvanceRaw = Refl

0 controlAdvanceChecked :
  checkedApplyAction @{the (DecEq Nat) %search}
    @{the (DecEq ToyKey) %search} (LAdvance (the Nat 0))
    DGamma.CP4DeletionControlChecks.controlSource =
      Just (LFinishTag, DGamma.CP4DeletionControlChecks.controlAfter)
controlAdvanceChecked =
  let targetWellFormed = preservationTheoremProof
        (the (DecEq Nat) %search) (the (DecEq ToyKey) %search)
        (LAdvance (the Nat 0)) controlSource controlAfter LFinishTag
        controlSourceWellFormed controlAdvanceRaw
  in rewrite controlAdvanceRaw in rewrite targetWellFormed in Refl

0 controlDeletionPlan :
  InactiveLeafDeletionPlan {name = Nat} {key = ToyKey} {value = ToyValue}
    {world = ToyRuntime} {error = String} (the (DecEq Nat) %search)
    DGamma.CP4DeletionControlChecks.controlRegistry
    (deleteBinding (the Nat 1) DGamma.CP4DeletionControlChecks.controlRegistry)
controlDeletionPlan = DeleteInactiveLeaf {name = Nat} {key = ToyKey}
  {value = ToyValue} {world = ToyRuntime} {error = String}
  (the Nat 1) controlInertComponent Root True emptyOwned Nothing Refl Refl
  NoInactiveLeafDeletion

0 controlActorOutside : ActorOutsideDeletionPlan (the Nat 0)
  DGamma.CP4DeletionControlChecks.controlDeletionPlan
controlActorOutside = ActorOutsideDeletionStep NoInactiveLeafDeletion zeroNotOne
  ActorOutsideDeletionEnd

||| Nonempty regression: a checked L-Finish landing remains checked after one
||| concrete inert R-entry is erased.
public export
0 nonemptyInactivePlanControlWitness :
  TransitionResult {name = Nat} {key = ToyKey} {value = ToyValue}
    {world = ToyRuntime} {error = String}
    (MkSystemState (MkToyRuntime False False)
      (deleteBinding (the Nat 1)
        DGamma.CP4DeletionControlChecks.controlRegistry))
nonemptyInactivePlanControlWitness =
  DGamma.CP4DeletionControlPlan.checkedLifecycleAfterInactivePlan
  (the (DecEq Nat) %search) (the (DecEq ToyKey) %search)
  (LAdvance (the Nat 0)) Refl (MkToyRuntime False False)
  DGamma.CP4DeletionControlChecks.controlRegistry
  (deleteBinding (the Nat 1) DGamma.CP4DeletionControlChecks.controlRegistry)
  DGamma.CP4DeletionControlChecks.controlDeletionPlan controlActorOutside
  controlSourceWellFormed controlAdvanceChecked
