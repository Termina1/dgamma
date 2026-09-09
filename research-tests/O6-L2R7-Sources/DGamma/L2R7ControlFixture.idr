module DGamma.L2R7ControlFixture

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.CP5ActorLifecycleOnlyExtended
import DGamma.L2R2SmallStates
import DGamma.L2R2SmallExecution
import DGamma.L2R3BarrierStates
import DGamma.L2R3BarrierExecution
import DGamma.L2R3Attached
import DGamma.L2R3SmallAttached
import DGamma.L2R7AttachedC
import DGamma.L2R7ControlStates
import DGamma.L2R7ControlExecution
import DGamma.L2R7ControlTrace
import DGamma.L2R7ControlDisposition
import Data.List
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Full native located blocks and SAME-BUNDLE control dispositions, built
||| simultaneously. The gap starts after R,S,Retire3,Remove3, not after core.
public export
record ControlFixture where
  constructor MkControlFixture
  parentBlockC : LocatedOpenEpisodeBlockAttachedC Nat Bool Unit String (\key => Unit) %search %search 0 controlTrace
  followingBlockC : LocatedOpenEpisodeBlockAttachedC Nat Bool Unit String (\key => Unit) %search %search 2 controlTrace
  controlPhysicalOrder : BlockBeforeAttachedC Nat Bool Unit String (\key => Unit) %search %search controlTrace 0 2 parentBlockC followingBlockC
  0 parentRangeC : (transitionCount (attachedCBefore parentBlockC), transitionCount (attachedCBefore parentBlockC) + S (transitionCount (attachedCBody parentBlockC))) = (0,8)
  0 followingRangeC : (transitionCount (attachedCBefore followingBlockC), transitionCount (attachedCBefore followingBlockC) + S (transitionCount (attachedCBody followingBlockC))) = (8,10)
  0 controlsGapZero : transitionCount (attachedCBetweenBlocks controlPhysicalOrder) = 0
  0 retireInBundle : ForcedRootControlInBundle Nat Bool Unit String (\key => Unit) %search %search controlTrace 0 parentBlockC 3 (ORetire 3)
  0 removeInBundle : ForcedRootControlInBundle Nat Bool Unit String (\key => Unit) %search %search controlTrace 0 parentBlockC 3 (ORemove 3)
