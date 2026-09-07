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
