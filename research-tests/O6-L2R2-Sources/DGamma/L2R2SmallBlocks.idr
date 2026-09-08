module DGamma.L2R2SmallBlocks

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ActorLifecycleOnlyExtended
import DGamma.CP5L2R1ExtendedZeroGap
import DGamma.L2R2SmallStates
import DGamma.L2R2SmallExecution
import DGamma.L2R2SmallPlacement
import Data.List.Elem
import Decidable.Equality

%default total
%unbound_implicits off

||| A12 witness over UNCHANGED extended grammar (CP3:1786/1824 counterparts)
||| and physical block order (CP3:1873 counterpart). Parent0's block contains
||| its own child's Retire1 AND Remove1. Root3 is the one actual gap edge
||| before actor2's block; the authentic earliest-birth proof lives in C9.
public export
record SmallExtendedBlocks where
  constructor MkSmallExtendedBlocks
  freeingBlock : LocatedOpenEpisodeBlockExtended Nat Bool Unit String (\key => Unit) %search %search 0 smallTrace
  followingBlock : LocatedOpenEpisodeBlockExtended Nat Bool Unit String (\key => Unit) %search %search 2 smallTrace
  physicalOrder : BlockBeforeExtended Nat Bool Unit String (\key => Unit) %search %search smallTrace 0 2 freeingBlock followingBlock
  0 freeingRange : (transitionCount (extendedBefore freeingBlock),
    transitionCount (extendedBefore freeingBlock) + S (transitionCount (extendedBody freeingBlock))) = (0, 4)
  0 followingRange : (transitionCount (extendedBefore followingBlock),
    transitionCount (extendedBefore followingBlock) + S (transitionCount (extendedBody followingBlock))) = (5, 7)
  0 forcedRootGapCount : transitionCount (extendedBetweenBlocks physicalOrder) = 1
  0 forcedRootInGap : LocatedActionOccurrence (OInsert 3 Root (smallComponent True)) (extendedBetweenBlocks physicalOrder)
