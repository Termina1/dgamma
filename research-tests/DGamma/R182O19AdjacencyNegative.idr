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
