module DGamma.L2R3BarrierBlocks

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ActorLifecycleOnlyExtended
import DGamma.L2R2SmallStates
import DGamma.L2R2SmallExecution
import DGamma.L2R3Attached
import DGamma.L2R3SmallAttached
import DGamma.L2R3BarrierStates
import DGamma.L2R3BarrierExecution
import Data.Nat
import Data.List.Elem
import Decidable.Equality

%default total
%unbound_implicits off

||| R/S counterpart of the same-trace C12 attached-block fixture. The whole
||| ordered bundle belongs to parent0; S is barrier-forced, not key-forced.
public export
record BarrierAttachedBlocks where
  constructor MkBarrierAttachedBlocks
  freeingBlock : LocatedOpenEpisodeBlockAttached Nat Bool Unit String (\key => Unit) %search %search 0 barrierTrace
  followingBlock : LocatedOpenEpisodeBlockAttached Nat Bool Unit String (\key => Unit) %search %search 2 barrierTrace
  physicalOrder : BlockBeforeAttached Nat Bool Unit String (\key => Unit) %search %search barrierTrace 0 2 freeingBlock followingBlock
  0 freeingRange : (transitionCount (attachedBefore freeingBlock),
    transitionCount (attachedBefore freeingBlock) + S (transitionCount (attachedBody freeingBlock))) = (0, 6)
  0 followingRange : (transitionCount (attachedBefore followingBlock),
    transitionCount (attachedBefore followingBlock) + S (transitionCount (attachedBody followingBlock))) = (6, 8)
  0 forcedRootGapCount : transitionCount (attachedBetweenBlocks physicalOrder) = 0
  0 rInBody : LocatedActionOccurrence (OInsert 3 Root (smallComponent True)) (attachedBody freeingBlock)

  0 sInBody : LocatedActionOccurrence (OInsert 4 Root (smallComponent False)) (attachedBody freeingBlock)
  0 rsOrdered : LT (locatedActionOrdinal rInBody) (locatedActionOrdinal sInBody)
