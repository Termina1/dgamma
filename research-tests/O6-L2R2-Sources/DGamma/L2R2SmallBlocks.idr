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

||| Simultaneously construct the two real extended blocks and their physical
||| ordering. Own-child Retire1/Remove1 are INSIDE the parent range [0,4),
||| actor2 has range [5,7), and the authentic native root birth occupies the
||| single transition in between. No zero-gap or block normalization is assumed.
public export
0 smallExtendedBlocks : SmallExtendedBlocks
smallExtendedBlocks = MkSmallExtendedBlocks
  (MkLocatedOpenEpisodeBlockExtended (smallState 0) (smallState 1) (smallState 4)
    NoTransitions (MkBeginStep (smallBegin0 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 1} {afterState = smallState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) NoTransitions)))
    (InstalledStep {first = smallState 1} {middle = smallState 2} {finalState = smallState 4} (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution) (MoreTransitions (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) NoTransitions)) Refl
      (InstalledStep {first = smallState 2} {middle = smallState 3} {finalState = smallState 4} (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution) (MoreTransitions (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) NoTransitions) Refl
      (InstalledStep {first = smallState 3} {middle = smallState 4} {finalState = smallState 4} (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution) NoTransitions Refl
      (InstalledEnd Refl))))
    (ExtendedLifecycleStep (Fired {before = smallState 1} {afterState = smallState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) NoTransitions)) Refl Refl
      (ExtendedChildRetireStep (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) NoTransitions) 1 (freshFiber (smallComponent True) (ChildOf 0)) Refl Refl Refl
        (ExtendedChildRemoveStep (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) NoTransitions 1 (retireFiber (freshFiber (smallComponent True) (ChildOf 0))) Refl Refl Refl ExtendedLifecycleEnd)))
    (MoreTransitions (Fired {before = smallState 4} {afterState = smallState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 5} {afterState = smallState 6} %search %search (LBegin 2) LBeginTag (smallBegin2 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 6} {afterState = smallState 7} %search %search (LAdvance 2) LFinishTag (smallFinish2 smallNativeExecution)) NoTransitions)))
    NoLifecycleByEnd
    (NoLifecycleByStep (Fired {before = smallState 4} {afterState = smallState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 5} {afterState = smallState 6} %search %search (LBegin 2) LBeginTag (smallBegin2 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 6} {afterState = smallState 7} %search %search (LAdvance 2) LFinishTag (smallFinish2 smallNativeExecution)) NoTransitions)) (\life, same => case same of Refl impossible)
      (NoLifecycleByStep (Fired {before = smallState 5} {afterState = smallState 6} %search %search (LBegin 2) LBeginTag (smallBegin2 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 6} {afterState = smallState 7} %search %search (LAdvance 2) LFinishTag (smallFinish2 smallNativeExecution)) NoTransitions) (\life, same => case same of Refl impossible)
      (NoLifecycleByStep (Fired {before = smallState 6} {afterState = smallState 7} %search %search (LAdvance 2) LFinishTag (smallFinish2 smallNativeExecution)) NoTransitions (\life, same => case same of Refl impossible)
      NoLifecycleByEnd))) Refl Refl)
  (MkLocatedOpenEpisodeBlockExtended (smallState 5) (smallState 6) (smallState 7)
    (MoreTransitions (Fired {before = smallState 0} {afterState = smallState 1} %search %search (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 1} {afterState = smallState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 4} {afterState = smallState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) NoTransitions))))) (MkBeginStep (smallBegin2 smallNativeExecution))
    (MoreTransitions (Fired {before = smallState 6} {afterState = smallState 7} %search %search (LAdvance 2) LFinishTag (smallFinish2 smallNativeExecution)) NoTransitions)
    (InstalledStep {first = smallState 6} {middle = smallState 7} {finalState = smallState 7} (LAdvance 2) LFinishTag (smallFinish2 smallNativeExecution) NoTransitions Refl
      (InstalledEnd Refl))
    (ExtendedLifecycleStep (Fired {before = smallState 6} {afterState = smallState 7} %search %search (LAdvance 2) LFinishTag (smallFinish2 smallNativeExecution)) NoTransitions Refl Refl ExtendedLifecycleEnd)
    NoTransitions
    (NoLifecycleByStep (Fired {before = smallState 0} {afterState = smallState 1} %search %search (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 1} {afterState = smallState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 4} {afterState = smallState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) NoTransitions)))) (\life, same => case same of Refl impossible)
      (NoLifecycleByStep (Fired {before = smallState 1} {afterState = smallState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 4} {afterState = smallState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) NoTransitions))) (\life, same => case same of Refl impossible)
      (NoLifecycleByStep (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 4} {afterState = smallState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) NoTransitions)) (\life, same => case same of Refl impossible)
      (NoLifecycleByStep (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 4} {afterState = smallState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) NoTransitions) (\life, same => case same of Refl impossible)
      (NoLifecycleByStep (Fired {before = smallState 4} {afterState = smallState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) NoTransitions (\life, same => case same of Refl impossible)
      NoLifecycleByEnd))))) NoLifecycleByEnd Refl Refl)
  (MkBlockBeforeExtended (MoreTransitions (Fired {before = smallState 4} {afterState = smallState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) NoTransitions) Refl)
  Refl Refl Refl
  (MkLocatedActionOccurrence (smallState 4) (smallState 5) NoTransitions (Fired {before = smallState 4} {afterState = smallState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) NoTransitions Refl Refl)
