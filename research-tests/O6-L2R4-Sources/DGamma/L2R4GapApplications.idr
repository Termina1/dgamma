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

||| First non-conditional application of the UNCHANGED zero-gap theorem on
||| C12. Physical empty-gap/offset are observed fixture data, residual NF is
||| honestly vacuous; separation is PRODUCED for ALL bundles by localization.
||| Nonvacuous pre-attachment coverage is separately fixtureRootRegions.
export
0 smallGapViaNormalForm :
  transitionCount (attachedBetweenBlocks
    (DGamma.L2R3SmallAttached.SmallAttachedBlocks.physicalOrder smallAttachedBlocks)) = 0
smallGapViaNormalForm = attachedZeroGapInNormalForm
  (DGamma.L2R3SmallAttached.SmallAttachedBlocks.freeingBlock smallAttachedBlocks)
  (DGamma.L2R3SmallAttached.SmallAttachedBlocks.followingBlock smallAttachedBlocks)
  (DGamma.L2R3SmallAttached.SmallAttachedBlocks.physicalOrder smallAttachedBlocks)
  (NoTransitions {state = smallState 5}) 5
  (cong transitionCount (sym (smallGapObserved attachedFixtureObservations)))
  (smallOffsetObserved attachedFixtureObservations)
  (replace {p = RemainingGapHeadIsRoot %search} (smallGapObserved attachedFixtureObservations)
    (c12ResidualCovered fixtureCoverage))
  (replace {p = \gap => AttachedNormalForm Nat Bool Unit String (\key => Unit) %search %search smallTrace gap 5}
    (smallGapObserved attachedFixtureObservations) (c12ResidualNF fixtureCoverage))
  (\action, ordinal, member => separateBundleObserved 5 action ordinal member smallNoBundleStraddles
    (isLTE (bundleOffset member + transitionCount (memberBundle member)) 5))

||| Same non-conditional unchanged-theorem application for barrier R/S.
||| Native residual gap/offset and residual coverage/NF are fixture data;
||| the universal separated callback is derived from barrierNoBundleStraddles.
||| This does not claim that the nonempty root region has count zero.
export
0 barrierGapViaNormalForm :
  transitionCount (attachedBetweenBlocks
    (DGamma.L2R3BarrierBlocks.BarrierAttachedBlocks.physicalOrder barrierAttachedBlocks)) = 0
barrierGapViaNormalForm = attachedZeroGapInNormalForm
  (DGamma.L2R3BarrierBlocks.BarrierAttachedBlocks.freeingBlock barrierAttachedBlocks)
  (DGamma.L2R3BarrierBlocks.BarrierAttachedBlocks.followingBlock barrierAttachedBlocks)
  (DGamma.L2R3BarrierBlocks.BarrierAttachedBlocks.physicalOrder barrierAttachedBlocks)
  (NoTransitions {state = barrierState 6}) 6
  (cong transitionCount (sym (barrierGapObserved attachedFixtureObservations)))
  (barrierOffsetObserved attachedFixtureObservations)
  (replace {p = RemainingGapHeadIsRoot %search} (barrierGapObserved attachedFixtureObservations)
    (barrierResidualCovered fixtureCoverage))
  (replace {p = \gap => AttachedNormalForm Nat Bool Unit String (\key => Unit) %search %search barrierTrace gap 6}
    (barrierGapObserved attachedFixtureObservations) (barrierResidualNF fixtureCoverage))
  (\action, ordinal, member => separateBundleObserved 6 action ordinal member barrierNoBundleStraddles
    (isLTE (bundleOffset member + transitionCount (memberBundle member)) 6))
