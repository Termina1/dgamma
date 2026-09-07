module DGamma.R182O19AdjacencyNegative

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP3Support
import DGamma.CP4Support
import DGamma.CP4SupportSolution
import DGamma.CP4SupportQuiescence
import DGamma.CP4RecoveryEffectRespect
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorEndpoint
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5RankedEarlyApplicabilitySpike
import DGamma.Metatheory
import DGamma.Unified
import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import DGamma.R39RelationalMapAlgebraPositive
import DGamma.R172O17OpenParentRootReuseCandidate
import DGamma.R182O19RevisedSafetyPositive
import DGamma.R182O19RevisedSafetyNegative
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| B-Adj3: exact nine-edge candidate cuts. Third root is inserted BETWEEN
||| completed block0 and block1, not inside either selected actor block.
public export
r182GapState : Nat -> SystemState Nat R45Key R45Value Unit String
r182GapState Z = r182IndependentState 0
r182GapState (S Z) = r182IndependentState 1
r182GapState (S (S Z)) = r182IndependentState 2
r182GapState (S (S (S Z))) = r182IndependentState 3
r182GapState (S (S (S (S Z)))) = r182IndependentState 4
r182GapState (S (S (S (S (S Z))))) = MkSystemState ()
  (insertBinding @{r45NameEq} 2 (freshFiber r45Child Root) (registry (r182IndependentState 4)) Refl)
r182GapState (S (S (S (S (S (S Z)))))) = MkSystemState ()
  (MkCoeffectContext [Bind 2 (freshFiber r45Child Root), Bind 1 (MkFiber r45Child Root False emptyOwned (Reloading [] id EmptyView)), Bind 0 (MkFiber r45Child Root False emptyOwned (Active id EmptyView))]
    (uniqueBindings (the (Registry Nat R45Key R45Value Unit String)
      (insertBinding @{r45NameEq} 2 (freshFiber r45Child Root) (registry (r182IndependentState 4)) Refl))))
r182GapState (S (S (S (S (S (S (S Z))))))) = MkSystemState ()
  (MkCoeffectContext [Bind 2 (freshFiber r45Child Root), Bind 1 (MkFiber r45Child Root False emptyOwned (Active id EmptyView)), Bind 0 (MkFiber r45Child Root False emptyOwned (Active id EmptyView))]
    (uniqueBindings (the (Registry Nat R45Key R45Value Unit String)
      (insertBinding @{r45NameEq} 2 (freshFiber r45Child Root) (registry (r182IndependentState 4)) Refl))))
r182GapState (S (S (S (S (S (S (S (S Z)))))))) = MkSystemState ()
  (MkCoeffectContext [Bind 2 (MkFiber r45Child Root False emptyOwned (Reloading [] id EmptyView)), Bind 1 (MkFiber r45Child Root False emptyOwned (Active id EmptyView)), Bind 0 (MkFiber r45Child Root False emptyOwned (Active id EmptyView))]
    (uniqueBindings (the (Registry Nat R45Key R45Value Unit String)
      (insertBinding @{r45NameEq} 2 (freshFiber r45Child Root) (registry (r182IndependentState 4)) Refl))))
r182GapState (S (S (S (S (S (S (S (S (S later))))))))) = MkSystemState ()
  (MkCoeffectContext [Bind 2 (MkFiber r45Child Root False emptyOwned (Active id EmptyView)), Bind 1 (MkFiber r45Child Root False emptyOwned (Active id EmptyView)), Bind 0 (MkFiber r45Child Root False emptyOwned (Active id EmptyView))]
    (uniqueBindings (the (Registry Nat R45Key R45Value Unit String)
      (insertBinding @{r45NameEq} 2 (freshFiber r45Child Root) (registry (r182IndependentState 4)) Refl))))

||| B-Adj4: nine ACTUAL checked edges, together with the exact intervening
||| Insert2 edge, its simultaneous nonzero count, and successful right-first
||| opening at the genuine pre-left cut2. No nested execution builder.
public export
0 r182GapTrace :
  (Transitions (r182GapState 0) (r182GapState 9),
   (segment : Transitions (r182GapState 4) (r182GapState 5) **
     ((transitionCount segment = 1),
      CheckedEarlyApplication Nat R45Key Unit String R45Value r45NameEq r45KeyEq
        (r182GapState 2) (LBegin 1) LBeginTag)))
r182GapTrace =
  ((MoreTransitions (Fired {before = r182GapState 0} {afterState = r182GapState 1} r45NameEq r45KeyEq (OInsert 0 Root r45Child) OInsertTag Refl) (MoreTransitions (Fired {before = r182GapState 1} {afterState = r182GapState 2} r45NameEq r45KeyEq (OInsert 1 Root r45Child) OInsertTag Refl) (MoreTransitions (Fired {before = r182GapState 2} {afterState = r182GapState 3} r45NameEq r45KeyEq (LBegin 0) LBeginTag Refl) (MoreTransitions (Fired {before = r182GapState 3} {afterState = r182GapState 4} r45NameEq r45KeyEq (LAdvance 0) LFinishTag Refl) (MoreTransitions (Fired {before = r182GapState 4} {afterState = r182GapState 5} r45NameEq r45KeyEq (OInsert 2 Root r45Child) OInsertTag Refl) (MoreTransitions (Fired {before = r182GapState 5} {afterState = r182GapState 6} r45NameEq r45KeyEq (LBegin 1) LBeginTag Refl) (MoreTransitions (Fired {before = r182GapState 6} {afterState = r182GapState 7} r45NameEq r45KeyEq (LAdvance 1) LFinishTag Refl) (MoreTransitions (Fired {before = r182GapState 7} {afterState = r182GapState 8} r45NameEq r45KeyEq (LBegin 2) LBeginTag Refl) (MoreTransitions (Fired {before = r182GapState 8} {afterState = r182GapState 9} r45NameEq r45KeyEq (LAdvance 2) LFinishTag Refl) NoTransitions))))))))),
   ((MoreTransitions (Fired {before = r182GapState 4} {afterState = r182GapState 5} r45NameEq r45KeyEq (OInsert 2 Root r45Child) OInsertTag Refl) NoTransitions) **
     (Refl, MkCheckedEarlyApplication (r182IndependentState 7) Refl)))

||| B-Adj5: all fifteen ReplayInvariantBundle fields REALLY inhabited for the
||| nine-edge candidate. Existing empty-key relational algebra applies to this
||| arbitrary actual trace, not an assumed TraceIndependent or endpoint oracle.
public export
0 r182GapBundle : ReplayInvariantBundle Nat R45Key Unit String R45Value
  r45Protocol r45NameEq r45KeyEq (Builtin.fst r182GapTrace)
r182GapBundle = MkReplayInvariantBundle
  (AlignedStep (OInsert 0 Root r45Child) OInsertTag Refl _ (AlignedStep (OInsert 1 Root r45Child) OInsertTag Refl _ (AlignedStep (LBegin 0) LBeginTag Refl _ (AlignedStep (LAdvance 0) LFinishTag Refl _ (AlignedStep (OInsert 2 Root r45Child) OInsertTag Refl _ (AlignedStep (LBegin 1) LBeginTag Refl _ (AlignedStep (LAdvance 1) LFinishTag Refl _ (AlignedStep (LBegin 2) LBeginTag Refl _ (AlignedStep (LAdvance 2) LFinishTag Refl _ AlignedEnd)))))))))
  (RegistrationDisciplineStep _ _ (1 ** Refl) (RegistrationDisciplineStep _ _ (1 ** Refl) (RegistrationDisciplineStep _ _ () (RegistrationDisciplineStep _ _ () (RegistrationDisciplineStep _ _ (1 ** Refl) (RegistrationDisciplineStep _ _ () (RegistrationDisciplineStep _ _ () (RegistrationDisciplineStep _ _ () (RegistrationDisciplineStep _ _ () RegistrationDisciplineEnd))))))))) Refl Refl Refl Refl Refl
  (TraceComponentsTotalStep _ _ (r172ReuseAnyTransitionTotal (Fired {before = r182GapState 0} {afterState = r182GapState 1} r45NameEq r45KeyEq (OInsert 0 Root r45Child) OInsertTag Refl)) (TraceComponentsTotalStep _ _ (r172ReuseAnyTransitionTotal (Fired {before = r182GapState 1} {afterState = r182GapState 2} r45NameEq r45KeyEq (OInsert 1 Root r45Child) OInsertTag Refl)) (TraceComponentsTotalStep _ _ (r172ReuseAnyTransitionTotal (Fired {before = r182GapState 2} {afterState = r182GapState 3} r45NameEq r45KeyEq (LBegin 0) LBeginTag Refl)) (TraceComponentsTotalStep _ _ (r172ReuseAnyTransitionTotal (Fired {before = r182GapState 3} {afterState = r182GapState 4} r45NameEq r45KeyEq (LAdvance 0) LFinishTag Refl)) (TraceComponentsTotalStep _ _ (r172ReuseAnyTransitionTotal (Fired {before = r182GapState 4} {afterState = r182GapState 5} r45NameEq r45KeyEq (OInsert 2 Root r45Child) OInsertTag Refl)) (TraceComponentsTotalStep _ _ (r172ReuseAnyTransitionTotal (Fired {before = r182GapState 5} {afterState = r182GapState 6} r45NameEq r45KeyEq (LBegin 1) LBeginTag Refl)) (TraceComponentsTotalStep _ _ (r172ReuseAnyTransitionTotal (Fired {before = r182GapState 6} {afterState = r182GapState 7} r45NameEq r45KeyEq (LAdvance 1) LFinishTag Refl)) (TraceComponentsTotalStep _ _ (r172ReuseAnyTransitionTotal (Fired {before = r182GapState 7} {afterState = r182GapState 8} r45NameEq r45KeyEq (LBegin 2) LBeginTag Refl)) (TraceComponentsTotalStep _ _ (r172ReuseAnyTransitionTotal (Fired {before = r182GapState 8} {afterState = r182GapState 9} r45NameEq r45KeyEq (LAdvance 2) LFinishTag Refl)) TraceComponentsTotalEnd)))))))))
  (MkTraceIndependent
    (\left, right, distinct, leftT, rightT => r172ReuseMapsCommute
      (runTraceEffectTransformation leftT) (runTraceEffectTransformation rightT)
      (r182IndependentTransformationRespects left leftT)
      (r182IndependentTransformationRespects right rightT))
    (\left, right, distinct, stage, foreign, origin =>
      r182IndependentIteratorObserved left stage (runTraceEffectTransformation foreign)
        origin (runTraceEffectTransformation foreign origin) Refl))
  (registrationDisciplineProvenance r45Protocol r45NameEq (Builtin.fst r182GapTrace) (RegistrationDisciplineStep _ _ (1 ** Refl) (RegistrationDisciplineStep _ _ (1 ** Refl) (RegistrationDisciplineStep _ _ () (RegistrationDisciplineStep _ _ () (RegistrationDisciplineStep _ _ (1 ** Refl) (RegistrationDisciplineStep _ _ () (RegistrationDisciplineStep _ _ () (RegistrationDisciplineStep _ _ () (RegistrationDisciplineStep _ _ () RegistrationDisciplineEnd))))))))))
  (reachedRegistryProtocolRanked r45Protocol r45NameEq r45KeyEq (MkReachedFromEmpty (r182GapState 0) (Builtin.fst r182GapTrace) (AlignedStep (OInsert 0 Root r45Child) OInsertTag Refl _ (AlignedStep (OInsert 1 Root r45Child) OInsertTag Refl _ (AlignedStep (LBegin 0) LBeginTag Refl _ (AlignedStep (LAdvance 0) LFinishTag Refl _ (AlignedStep (OInsert 2 Root r45Child) OInsertTag Refl _ (AlignedStep (LBegin 1) LBeginTag Refl _ (AlignedStep (LAdvance 1) LFinishTag Refl _ (AlignedStep (LBegin 2) LBeginTag Refl _ (AlignedStep (LAdvance 2) LFinishTag Refl _ AlignedEnd))))))))) Refl Refl) (registrationDisciplineProvenance r45Protocol r45NameEq (Builtin.fst r182GapTrace) (RegistrationDisciplineStep _ _ (1 ** Refl) (RegistrationDisciplineStep _ _ (1 ** Refl) (RegistrationDisciplineStep _ _ () (RegistrationDisciplineStep _ _ () (RegistrationDisciplineStep _ _ (1 ** Refl) (RegistrationDisciplineStep _ _ () (RegistrationDisciplineStep _ _ () (RegistrationDisciplineStep _ _ () (RegistrationDisciplineStep _ _ () RegistrationDisciplineEnd)))))))))))
  (reachedRegistryParentRanksIncrease r45Protocol r45NameEq r45KeyEq (MkReachedFromEmpty (r182GapState 0) (Builtin.fst r182GapTrace) (AlignedStep (OInsert 0 Root r45Child) OInsertTag Refl _ (AlignedStep (OInsert 1 Root r45Child) OInsertTag Refl _ (AlignedStep (LBegin 0) LBeginTag Refl _ (AlignedStep (LAdvance 0) LFinishTag Refl _ (AlignedStep (OInsert 2 Root r45Child) OInsertTag Refl _ (AlignedStep (LBegin 1) LBeginTag Refl _ (AlignedStep (LAdvance 1) LFinishTag Refl _ (AlignedStep (LBegin 2) LBeginTag Refl _ (AlignedStep (LAdvance 2) LFinishTag Refl _ AlignedEnd))))))))) Refl Refl) (registrationDisciplineProvenance r45Protocol r45NameEq (Builtin.fst r182GapTrace) (RegistrationDisciplineStep _ _ (1 ** Refl) (RegistrationDisciplineStep _ _ (1 ** Refl) (RegistrationDisciplineStep _ _ () (RegistrationDisciplineStep _ _ () (RegistrationDisciplineStep _ _ (1 ** Refl) (RegistrationDisciplineStep _ _ () (RegistrationDisciplineStep _ _ () (RegistrationDisciplineStep _ _ () (RegistrationDisciplineStep _ _ () RegistrationDisciplineEnd)))))))))))
  (disciplinedEndpointPrecedenceAcyclic r45Protocol r45NameEq r45KeyEq
    (r182GapState 9) (MkReachedFromEmpty (r182GapState 0) (Builtin.fst r182GapTrace) (AlignedStep (OInsert 0 Root r45Child) OInsertTag Refl _ (AlignedStep (OInsert 1 Root r45Child) OInsertTag Refl _ (AlignedStep (LBegin 0) LBeginTag Refl _ (AlignedStep (LAdvance 0) LFinishTag Refl _ (AlignedStep (OInsert 2 Root r45Child) OInsertTag Refl _ (AlignedStep (LBegin 1) LBeginTag Refl _ (AlignedStep (LAdvance 1) LFinishTag Refl _ (AlignedStep (LBegin 2) LBeginTag Refl _ (AlignedStep (LAdvance 2) LFinishTag Refl _ AlignedEnd))))))))) Refl Refl) (RegistrationDisciplineStep _ _ (1 ** Refl) (RegistrationDisciplineStep _ _ (1 ** Refl) (RegistrationDisciplineStep _ _ () (RegistrationDisciplineStep _ _ () (RegistrationDisciplineStep _ _ (1 ** Refl) (RegistrationDisciplineStep _ _ () (RegistrationDisciplineStep _ _ () (RegistrationDisciplineStep _ _ () (RegistrationDisciplineStep _ _ () RegistrationDisciplineEnd))))))))))
  (supportCombinedWellFounded r45Protocol r45NameEq (r182GapState 9)
    (reachedRegistryProtocolRanked r45Protocol r45NameEq r45KeyEq (MkReachedFromEmpty (r182GapState 0) (Builtin.fst r182GapTrace) (AlignedStep (OInsert 0 Root r45Child) OInsertTag Refl _ (AlignedStep (OInsert 1 Root r45Child) OInsertTag Refl _ (AlignedStep (LBegin 0) LBeginTag Refl _ (AlignedStep (LAdvance 0) LFinishTag Refl _ (AlignedStep (OInsert 2 Root r45Child) OInsertTag Refl _ (AlignedStep (LBegin 1) LBeginTag Refl _ (AlignedStep (LAdvance 1) LFinishTag Refl _ (AlignedStep (LBegin 2) LBeginTag Refl _ (AlignedStep (LAdvance 2) LFinishTag Refl _ AlignedEnd))))))))) Refl Refl) (registrationDisciplineProvenance r45Protocol r45NameEq (Builtin.fst r182GapTrace) (RegistrationDisciplineStep _ _ (1 ** Refl) (RegistrationDisciplineStep _ _ (1 ** Refl) (RegistrationDisciplineStep _ _ () (RegistrationDisciplineStep _ _ () (RegistrationDisciplineStep _ _ (1 ** Refl) (RegistrationDisciplineStep _ _ () (RegistrationDisciplineStep _ _ () (RegistrationDisciplineStep _ _ () (RegistrationDisciplineStep _ _ () RegistrationDisciplineEnd)))))))))))
    (reachedRegistryParentRanksIncrease r45Protocol r45NameEq r45KeyEq (MkReachedFromEmpty (r182GapState 0) (Builtin.fst r182GapTrace) (AlignedStep (OInsert 0 Root r45Child) OInsertTag Refl _ (AlignedStep (OInsert 1 Root r45Child) OInsertTag Refl _ (AlignedStep (LBegin 0) LBeginTag Refl _ (AlignedStep (LAdvance 0) LFinishTag Refl _ (AlignedStep (OInsert 2 Root r45Child) OInsertTag Refl _ (AlignedStep (LBegin 1) LBeginTag Refl _ (AlignedStep (LAdvance 1) LFinishTag Refl _ (AlignedStep (LBegin 2) LBeginTag Refl _ (AlignedStep (LAdvance 2) LFinishTag Refl _ AlignedEnd))))))))) Refl Refl) (registrationDisciplineProvenance r45Protocol r45NameEq (Builtin.fst r182GapTrace) (RegistrationDisciplineStep _ _ (1 ** Refl) (RegistrationDisciplineStep _ _ (1 ** Refl) (RegistrationDisciplineStep _ _ () (RegistrationDisciplineStep _ _ () (RegistrationDisciplineStep _ _ (1 ** Refl) (RegistrationDisciplineStep _ _ () (RegistrationDisciplineStep _ _ () (RegistrationDisciplineStep _ _ () (RegistrationDisciplineStep _ _ () RegistrationDisciplineEnd))))))))))))
  (deletionPremisesGiveSupportMatchesActive r45Protocol r45NameEq r45KeyEq
    (r182GapState 0) (r182GapState 9) (Builtin.fst r182GapTrace)
    (AlignedStep (OInsert 0 Root r45Child) OInsertTag Refl _ (AlignedStep (OInsert 1 Root r45Child) OInsertTag Refl _ (AlignedStep (LBegin 0) LBeginTag Refl _ (AlignedStep (LAdvance 0) LFinishTag Refl _ (AlignedStep (OInsert 2 Root r45Child) OInsertTag Refl _ (AlignedStep (LBegin 1) LBeginTag Refl _ (AlignedStep (LAdvance 1) LFinishTag Refl _ (AlignedStep (LBegin 2) LBeginTag Refl _ (AlignedStep (LAdvance 2) LFinishTag Refl _ AlignedEnd)))))))))
    (RegistrationDisciplineStep _ _ (1 ** Refl) (RegistrationDisciplineStep _ _ (1 ** Refl) (RegistrationDisciplineStep _ _ () (RegistrationDisciplineStep _ _ () (RegistrationDisciplineStep _ _ (1 ** Refl) (RegistrationDisciplineStep _ _ () (RegistrationDisciplineStep _ _ () (RegistrationDisciplineStep _ _ () (RegistrationDisciplineStep _ _ () RegistrationDisciplineEnd))))))))) Refl Refl Refl Refl (TraceComponentsTotalStep _ _ (r172ReuseAnyTransitionTotal (Fired {before = r182GapState 0} {afterState = r182GapState 1} r45NameEq r45KeyEq (OInsert 0 Root r45Child) OInsertTag Refl)) (TraceComponentsTotalStep _ _ (r172ReuseAnyTransitionTotal (Fired {before = r182GapState 1} {afterState = r182GapState 2} r45NameEq r45KeyEq (OInsert 1 Root r45Child) OInsertTag Refl)) (TraceComponentsTotalStep _ _ (r172ReuseAnyTransitionTotal (Fired {before = r182GapState 2} {afterState = r182GapState 3} r45NameEq r45KeyEq (LBegin 0) LBeginTag Refl)) (TraceComponentsTotalStep _ _ (r172ReuseAnyTransitionTotal (Fired {before = r182GapState 3} {afterState = r182GapState 4} r45NameEq r45KeyEq (LAdvance 0) LFinishTag Refl)) (TraceComponentsTotalStep _ _ (r172ReuseAnyTransitionTotal (Fired {before = r182GapState 4} {afterState = r182GapState 5} r45NameEq r45KeyEq (OInsert 2 Root r45Child) OInsertTag Refl)) (TraceComponentsTotalStep _ _ (r172ReuseAnyTransitionTotal (Fired {before = r182GapState 5} {afterState = r182GapState 6} r45NameEq r45KeyEq (LBegin 1) LBeginTag Refl)) (TraceComponentsTotalStep _ _ (r172ReuseAnyTransitionTotal (Fired {before = r182GapState 6} {afterState = r182GapState 7} r45NameEq r45KeyEq (LAdvance 1) LFinishTag Refl)) (TraceComponentsTotalStep _ _ (r172ReuseAnyTransitionTotal (Fired {before = r182GapState 7} {afterState = r182GapState 8} r45NameEq r45KeyEq (LBegin 2) LBeginTag Refl)) (TraceComponentsTotalStep _ _ (r172ReuseAnyTransitionTotal (Fired {before = r182GapState 8} {afterState = r182GapState 9} r45NameEq r45KeyEq (LAdvance 2) LFinishTag Refl)) TraceComponentsTotalEnd))))))))))

||| B-Adj6: reject full current safety for EVERY decomposition selecting the
||| certified nonempty gap. gapObserved is explicitly the selected-gap witness;
||| a full inhabitant of the old safety/decomposition is NOT assumed or claimed.
||| The nine-edge trace, actual one-edge segment and full bundle are all owned.
public export
0 r182GapSafetyRejected :
  (orderSwap : AdjacentActorOrderSwap Nat [0, 1, 2] [1, 0, 2]) ->
  (blocks : ActorBlockDecomposition Nat R45Key Unit String R45Value r45NameEq r45KeyEq
    [0, 1, 2] (Builtin.fst r182GapTrace)) ->
  (premises : ReplayInvariantBundle Nat R45Key Unit String R45Value
    r45Protocol r45NameEq r45KeyEq (Builtin.fst r182GapTrace)) ->
  (applicableSafety : AdjacentActorSwapSafety Nat R45Key Unit String R45Value
    r45Protocol r45NameEq r45KeyEq orderSwap (Builtin.fst r182GapTrace) blocks premises) ->
  (0 gapObserved : (transitionCount (betweenBlocks (safetyBlocksOrdered applicableSafety)) =
    transitionCount (Builtin.DPair.DPair.fst (Builtin.snd r182GapTrace)))) -> Void
r182GapSafetyRejected orderSwap blocks premises applicableSafety gapObserved =
  uninhabited (trans (sym (safetyBlocksAdjacent applicableSafety))
    (trans gapObserved (Builtin.fst (Builtin.DPair.DPair.snd (Builtin.snd r182GapTrace)))))
