module DGamma.L2R3SmallAttached

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ActorLifecycleOnlyExtended
import DGamma.L2R2SmallStates
import DGamma.L2R2SmallExecution
import DGamma.L2R3Attached
import Data.List.Elem
import Decidable.Equality

%default total
%unbound_implicits off

||| Native Remove1 at body ordinal2 releases True for Root3. The occurrence
||| is in the SAME Finish0/Retire1/Remove1 core used by the attached fixture.
public export
0 smallRelease : AttachedRelease Nat Bool Unit String (\key => Unit) %search 0
  (MoreTransitions (Fired {before = smallState 1} {afterState = smallState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) NoTransitions))) (smallComponent True)
smallRelease = MkAttachedRelease 1 (retireFiber (freshFiber (smallComponent True) (ChildOf 0)))
  (MkLocatedActionOccurrence (smallState 3) (smallState 4) (MoreTransitions (Fired {before = smallState 1} {afterState = smallState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) (MoreTransitions (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) NoTransitions)) (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) NoTransitions Refl Refl) Refl Refl True Here Here

||| C12 counterpart of L2R2SmallBlocks:23 on the unchanged smallTrace.
||| Parent range includes Root3, actor2 starts immediately after its bundle.
public export
record SmallAttachedBlocks where
  constructor MkSmallAttachedBlocks
  freeingBlock : LocatedOpenEpisodeBlockAttached Nat Bool Unit String (\key => Unit) %search %search 0 smallTrace
  followingBlock : LocatedOpenEpisodeBlockAttached Nat Bool Unit String (\key => Unit) %search %search 2 smallTrace
  physicalOrder : BlockBeforeAttached Nat Bool Unit String (\key => Unit) %search %search smallTrace 0 2 freeingBlock followingBlock
  0 freeingRange : (transitionCount (attachedBefore freeingBlock),
    transitionCount (attachedBefore freeingBlock) + S (transitionCount (attachedBody freeingBlock))) = (0, 5)
  0 followingRange : (transitionCount (attachedBefore followingBlock),
    transitionCount (attachedBefore followingBlock) + S (transitionCount (attachedBody followingBlock))) = (5, 7)
  0 forcedRootGapCount : transitionCount (attachedBetweenBlocks physicalOrder) = 0
  0 forcedRootInBody : LocatedActionOccurrence (OInsert 3 Root (smallComponent True)) (attachedBody freeingBlock)
