module DGamma.L2R16AnchorFrameRejection

import Builtin
import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import Prelude.EqOrd
import Prelude.Num
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.CP5UniqueRawNameInsertions
import DGamma.L2R2SmallStates
import DGamma.L2R3ForcedClosure
import DGamma.L2R5Extensional
import DGamma.L2R5RootCatalog
import DGamma.L2R6Iteration
import DGamma.L2R8NativeWords
import DGamma.L2R11ClassifierSquare
import DGamma.L2R13NativeSuffixFrames
import DGamma.L2R13TerminalMove
import DGamma.L2R12DistanceFrame
import DGamma.L2R15GlobalFrames
import DGamma.L2R6ForcedScan
import DGamma.L2R6Anchors
import DGamma.L2R10OrdinalData
import DGamma.L2R16AnchorStates
import DGamma.L2R16AnchorNative
import DGamma.L2R16AnchorTrace
import DGamma.L2R16AnchorTrail
import DGamma.L2R16ProductionBridge
import DGamma.L2R16AnchorSquare
import DGamma.L2R16AnchorSegments
import DGamma.L2R16AnchorDomain
import DGamma.L2R16AnchorDistance
import Data.Bool
import Data.List
import Data.List.Elem
import Data.List.Quantifiers
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| CONDITIONAL negative theorem, not unconditional retirement: every
||| global-frame antecedent is constructed from this actual native fixture
||| EXCEPT UniqueRawNameInsertions, which remains an explicit hypothesis.
||| T12's if-reduction consumer was fully reverted; no equivalent retry is
||| hidden here. The assumed frames would force 3 = 4, contradicting the
||| independently computed vectors (3,0)->(2,1), total3->3.
export
0 anchorGlobalFrameRejectedGivenUnique :
  (0 unique : UniqueRawNameInsertions Nat Bool Unit String (\key => Unit)
    (fst fixtureDictionaries) (snd fixtureDictionaries) (anchorTrace False)) ->
  GlobalDistanceFramesFromNativeSuffix
    (fst fixtureDictionaries) (snd fixtureDictionaries) 4 (anchorComponent True)
    (anchorState 6) (anchorState 7) (anchorState 8) (ORetire 3) ORetireTag
    (MoreTransitions (Fired {before = anchorState 0} {afterState = anchorState 1} (fst fixtureDictionaries) (snd fixtureDictionaries) (LBegin 0) LBeginTag (aBegin anchorNative)) (MoreTransitions (Fired {before = anchorState 1} {afterState = anchorState 2} (fst fixtureDictionaries) (snd fixtureDictionaries) (LAdvance 0) LFinishTag (aFinish anchorNative)) (MoreTransitions (Fired {before = anchorState 2} {afterState = anchorState 3} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORetire 1) ORetireTag (aRetire1 anchorNative)) (MoreTransitions (Fired {before = anchorState 3} {afterState = anchorState 4} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORemove 1) ORemoveTag (aRemove1 anchorNative)) (MoreTransitions (Fired {before = anchorState 4} {afterState = anchorState 5} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORetire 2) ORetireTag (aRetire2 anchorNative)) (MoreTransitions (Fired {before = anchorState 5} {afterState = anchorState 6} (fst fixtureDictionaries) (snd fixtureDictionaries) (ORemove 2) ORemoveTag (aRemove2 anchorNative)) (NoTransitions))))))) (anchorSegment 0)
    (aRetire3 anchorNative) (aRoot4 anchorNative) anchorSquare
    (MoreTransitions (Fired {before = anchorState 8} {afterState = anchorState 9} (fst fixtureDictionaries) (snd fixtureDictionaries) (OInsert 5 Root (anchorComponent False)) OInsertTag (aRoot5 anchorNative)) (NoTransitions))
    (MoreTransitions (Fired {before = anchorState 11} {afterState = anchorState 12} (fst fixtureDictionaries) (snd fixtureDictionaries) (OInsert 5 Root (anchorComponent False)) OInsertTag (aLateRoot5 anchorNative)) (NoTransitions))
    (anchorSegment 1) (anchorSegment 2) anchorSuffixFrames -> Void
anchorGlobalFrameRejectedGivenUnique unique assumed =
  case assumed (anchorInitialValid anchorNative) unique
    (fst (anchorFrontNever False)) (snd (anchorFrontNever False))
    (\entry, member, forced => fst (indexAll member anchorCatalogCoverage))
    (DGamma.L2R3ForcedClosure.KeyForces Data.List.Elem.Here Refl)
    (\entry, member, earlier, forced => void (snd (indexAll member anchorCatalogCoverage) earlier))
    4 Refl (LTESucc (LTESucc (LTESucc (LTESucc LTEZero)))) of
      (untouched ** (oldFrame, newFrame)) =>
        absurd (totalDistanceOneLeftFromFrame (fst fixtureDictionaries) (snd fixtureDictionaries)
          (researchAvailability (anchorTrail False)) (researchAvailability (anchorTrail True))
          6 4 untouched (LTESucc (LTESucc (LTESucc (LTESucc LTEZero)))) oldFrame newFrame)
