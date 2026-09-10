module DGamma.L2R16AnchorSegments

import Builtin
import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import Prelude.EqOrd
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R2SmallStates
import DGamma.L2R3ForcedClosure
import DGamma.L2R5Extensional
import DGamma.L2R5RootCatalog
import DGamma.L2R6Iteration
import DGamma.L2R8NativeWords
import DGamma.L2R11ClassifierSquare
import DGamma.L2R13NativeSuffixFrames
import DGamma.L2R6ForcedScan
import DGamma.L2R6Anchors
import DGamma.L2R10OrdinalData
import DGamma.L2R16AnchorStates
import DGamma.L2R16AnchorNative
import DGamma.L2R16AnchorTrace
import DGamma.L2R16AnchorTrail
import DGamma.L2R16ProductionBridge
import DGamma.L2R16AnchorSquare
import Data.Bool
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Exact reified native pieces: 0 = common six-edge prefix, 1 = original
||| root5 suffix, >=2 = crossed root5 suffix. The total index selector makes
||| no further execution claim. They are the authentic input pieces of the
||| existing GlobalDistanceFramesFromNativeSuffix research TYPE.
public export
anchorSegment : (part : Nat) -> case part of
  0 => DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace Nat Bool Unit String (\key => Unit)
    (MoreTransitions (Fired {before = anchorState 0} {afterState = anchorState 1} (fst fixtureDictionaries) (snd fixtureDictionaries) (LBegin 0) LBeginTag (aBegin anchorNative)) (MoreTransitions (Fired {before = anchorState 1} {afterState = anchorState 2} (fst fixtureDictionaries) (snd fixtureDictionaries) (LAdvance 0) LFinishTag (aFinish anchorNative)) (MoreTransitions (Fired {before = anchorState 2} {afterState = anchorState 3} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORetire 1) ORetireTag (aRetire1 anchorNative)) (MoreTransitions (Fired {before = anchorState 3} {afterState = anchorState 4} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORemove 1) ORemoveTag (aRemove1 anchorNative)) (MoreTransitions (Fired {before = anchorState 4} {afterState = anchorState 5} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORetire 2) ORetireTag (aRetire2 anchorNative)) (MoreTransitions (Fired {before = anchorState 5} {afterState = anchorState 6} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORemove 2) ORemoveTag (aRemove2 anchorNative)) (NoTransitions)))))))
  1 => DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace Nat Bool Unit String (\key => Unit)
    (MoreTransitions (Fired {before = anchorState 8} {afterState = anchorState 9} (fst fixtureDictionaries) (snd fixtureDictionaries) (OInsert 5 Root (anchorComponent False)) OInsertTag (aRoot5 anchorNative)) (NoTransitions))
  _ => DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace Nat Bool Unit String (\key => Unit)
    (MoreTransitions (Fired {before = anchorState 11} {afterState = anchorState 12} (fst fixtureDictionaries) (snd fixtureDictionaries) (OInsert 5 Root (anchorComponent False)) OInsertTag (aLateRoot5 anchorNative)) (NoTransitions))
anchorSegment 0 =
  DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (anchorState 0) (Fired {before = anchorState 0} {afterState = anchorState 1} (fst fixtureDictionaries) (snd fixtureDictionaries) (LBegin 0) LBeginTag (aBegin anchorNative)) (MoreTransitions (Fired {before = anchorState 1} {afterState = anchorState 2} (fst fixtureDictionaries) (snd fixtureDictionaries) (LAdvance 0) LFinishTag (aFinish anchorNative)) (MoreTransitions (Fired {before = anchorState 2} {afterState = anchorState 3} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORetire 1) ORetireTag (aRetire1 anchorNative)) (MoreTransitions (Fired {before = anchorState 3} {afterState = anchorState 4} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORemove 1) ORemoveTag (aRemove1 anchorNative)) (MoreTransitions (Fired {before = anchorState 4} {afterState = anchorState 5} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORetire 2) ORetireTag (aRetire2 anchorNative)) (MoreTransitions (Fired {before = anchorState 5} {afterState = anchorState 6} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORemove 2) ORemoveTag (aRemove2 anchorNative)) (NoTransitions)))))) (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (anchorState 1) (Fired {before = anchorState 1} {afterState = anchorState 2} (fst fixtureDictionaries) (snd fixtureDictionaries) (LAdvance 0) LFinishTag (aFinish anchorNative)) (MoreTransitions (Fired {before = anchorState 2} {afterState = anchorState 3} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORetire 1) ORetireTag (aRetire1 anchorNative)) (MoreTransitions (Fired {before = anchorState 3} {afterState = anchorState 4} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORemove 1) ORemoveTag (aRemove1 anchorNative)) (MoreTransitions (Fired {before = anchorState 4} {afterState = anchorState 5} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORetire 2) ORetireTag (aRetire2 anchorNative)) (MoreTransitions (Fired {before = anchorState 5} {afterState = anchorState 6} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORemove 2) ORemoveTag (aRemove2 anchorNative)) (NoTransitions))))) (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (anchorState 2) (Fired {before = anchorState 2} {afterState = anchorState 3} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORetire 1) ORetireTag (aRetire1 anchorNative)) (MoreTransitions (Fired {before = anchorState 3} {afterState = anchorState 4} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORemove 1) ORemoveTag (aRemove1 anchorNative)) (MoreTransitions (Fired {before = anchorState 4} {afterState = anchorState 5} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORetire 2) ORetireTag (aRetire2 anchorNative)) (MoreTransitions (Fired {before = anchorState 5} {afterState = anchorState 6} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORemove 2) ORemoveTag (aRemove2 anchorNative)) (NoTransitions)))) (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (anchorState 3) (Fired {before = anchorState 3} {afterState = anchorState 4} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORemove 1) ORemoveTag (aRemove1 anchorNative)) (MoreTransitions (Fired {before = anchorState 4} {afterState = anchorState 5} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORetire 2) ORetireTag (aRetire2 anchorNative)) (MoreTransitions (Fired {before = anchorState 5} {afterState = anchorState 6} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORemove 2) ORemoveTag (aRemove2 anchorNative)) (NoTransitions))) (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (anchorState 4) (Fired {before = anchorState 4} {afterState = anchorState 5} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORetire 2) ORetireTag (aRetire2 anchorNative)) (MoreTransitions (Fired {before = anchorState 5} {afterState = anchorState 6} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORemove 2) ORemoveTag (aRemove2 anchorNative)) (NoTransitions)) (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (anchorState 5) (Fired {before = anchorState 5} {afterState = anchorState 6} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORemove 2) ORemoveTag (aRemove2 anchorNative)) (NoTransitions) (DGamma.CP5AvailabilityAwarePlacement.AvailabilityEnd (anchorState 6)))))))
anchorSegment 1 =
  DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (anchorState 8) (Fired {before = anchorState 8} {afterState = anchorState 9} (fst fixtureDictionaries) (snd fixtureDictionaries) (OInsert 5 Root (anchorComponent False)) OInsertTag (aRoot5 anchorNative)) (NoTransitions) (DGamma.CP5AvailabilityAwarePlacement.AvailabilityEnd (anchorState 9))
anchorSegment (S (S later)) =
  DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep (anchorState 11) (Fired {before = anchorState 11} {afterState = anchorState 12} (fst fixtureDictionaries) (snd fixtureDictionaries) (OInsert 5 Root (anchorComponent False)) OInsertTag (aLateRoot5 anchorNative)) (NoTransitions) (DGamma.CP5AvailabilityAwarePlacement.AvailabilityEnd (anchorState 12))
