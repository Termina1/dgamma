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
