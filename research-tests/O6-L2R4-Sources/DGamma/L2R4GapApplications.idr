module DGamma.L2R4GapApplications

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4ProgressNoDeadlock
import DGamma.L2R2ConditionalGap
import DGamma.L2R2SmallStates
import DGamma.L2R2SmallExecution
import DGamma.L2R3Attached
import DGamma.L2R3AttachedGap
import DGamma.L2R3SmallAttached
import DGamma.L2R3BarrierStates
import DGamma.L2R3BarrierExecution
import DGamma.L2R3BarrierBlocks
import DGamma.L2R3FixtureCoverage
import DGamma.L2R3Separation
import DGamma.L2R4FixtureSeparation
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Typed observation of existing SAME-origin fixture data: literal residual
||| gaps and whole-body offsets. No separation or theorem conclusion is a
||| field; no second SystemState producer is equated to the original one.
public export
record AttachedFixtureObservations where
  constructor MkAttachedFixtureObservations
  0 smallGapObserved :
    attachedBetweenBlocks (DGamma.L2R3SmallAttached.SmallAttachedBlocks.physicalOrder smallAttachedBlocks) =
    NoTransitions {state = smallState 5}
  0 barrierGapObserved :
    attachedBetweenBlocks (DGamma.L2R3BarrierBlocks.BarrierAttachedBlocks.physicalOrder barrierAttachedBlocks) =
    NoTransitions {state = barrierState 6}
  0 smallOffsetObserved : 5 =
    transitionCount (attachedBefore (DGamma.L2R3SmallAttached.SmallAttachedBlocks.freeingBlock smallAttachedBlocks)) +
    S (transitionCount (attachedBody (DGamma.L2R3SmallAttached.SmallAttachedBlocks.freeingBlock smallAttachedBlocks)))
  0 barrierOffsetObserved : 6 =
    transitionCount (attachedBefore (DGamma.L2R3BarrierBlocks.BarrierAttachedBlocks.freeingBlock barrierAttachedBlocks)) +
    S (transitionCount (attachedBody (DGamma.L2R3BarrierBlocks.BarrierAttachedBlocks.freeingBlock barrierAttachedBlocks)))

||| Simultaneous single-constructor observation of the existing native block
||| producers. These literal gap/offset data instantiate physical premises;
||| universal separation comes separately from the localization theorem.
public export
0 attachedFixtureObservations : AttachedFixtureObservations
attachedFixtureObservations = MkAttachedFixtureObservations Refl Refl Refl Refl
