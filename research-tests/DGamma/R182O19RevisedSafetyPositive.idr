module DGamma.R182O19RevisedSafetyPositive

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
import DGamma.R172O17OpenParentRootReuseCandidate
import DGamma.R182O19RevisedSafetyNegative
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| A5: small explicit runtime states, NOT Maybe execution builders. Both
||| components have genuinely empty provisions/dependencies/programs. 0..6
||| describe left then right; 7..9 are the right-first intermediate states.
public export
r182IndependentState : Nat -> SystemState Nat R45Key R45Value Unit String
r182IndependentState Z = MkSystemState () emptyContext
r182IndependentState (S Z) = MkSystemState ()
  (insertBinding @{r45NameEq} 0 (freshFiber r45Child Root) emptyContext Refl)
r182IndependentState (S (S Z)) = MkSystemState ()
  (insertBinding @{r45NameEq} 1 (freshFiber r45Child Root)
    (insertBinding @{r45NameEq} 0 (freshFiber r45Child Root) emptyContext Refl) Refl)
r182IndependentState (S (S (S Z))) = MkSystemState ()
  (insertBinding @{r45NameEq} 1 (freshFiber r45Child Root)
    (insertBinding @{r45NameEq} 0 (MkFiber r45Child Root False emptyOwned
      (Reloading [] id EmptyView)) emptyContext Refl) Refl)
r182IndependentState (S (S (S (S Z)))) = MkSystemState ()
  (insertBinding @{r45NameEq} 1 (freshFiber r45Child Root)
    (insertBinding @{r45NameEq} 0 (MkFiber r45Child Root False emptyOwned
      (Active id EmptyView)) emptyContext Refl) Refl)
r182IndependentState (S (S (S (S (S Z))))) = MkSystemState ()
  (insertBinding @{r45NameEq} 1 (MkFiber r45Child Root False emptyOwned
      (Reloading [] id EmptyView))
    (insertBinding @{r45NameEq} 0 (MkFiber r45Child Root False emptyOwned
      (Active id EmptyView)) emptyContext Refl) Refl)
r182IndependentState (S (S (S (S (S (S Z)))))) = MkSystemState ()
  (insertBinding @{r45NameEq} 1 (MkFiber r45Child Root False emptyOwned
      (Active id EmptyView))
    (insertBinding @{r45NameEq} 0 (MkFiber r45Child Root False emptyOwned
      (Active id EmptyView)) emptyContext Refl) Refl)
r182IndependentState (S (S (S (S (S (S (S Z))))))) = MkSystemState ()
  (insertBinding @{r45NameEq} 1 (MkFiber r45Child Root False emptyOwned
      (Reloading [] id EmptyView))
    (insertBinding @{r45NameEq} 0 (freshFiber r45Child Root) emptyContext Refl) Refl)
r182IndependentState (S (S (S (S (S (S (S (S Z)))))))) = MkSystemState ()
  (insertBinding @{r45NameEq} 1 (MkFiber r45Child Root False emptyOwned
      (Active id EmptyView))
    (insertBinding @{r45NameEq} 0 (freshFiber r45Child Root) emptyContext Refl) Refl)
r182IndependentState (S (S (S (S (S (S (S (S (S later))))))))) = MkSystemState ()
  (insertBinding @{r45NameEq} 1 (MkFiber r45Child Root False emptyOwned
      (Active id EmptyView))
    (insertBinding @{r45NameEq} 0 (MkFiber r45Child Root False emptyOwned
      (Reloading [] id EmptyView)) emptyContext Refl) Refl)
