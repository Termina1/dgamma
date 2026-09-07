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
  (MkCoeffectContext [Bind 1 (freshFiber r45Child Root), Bind 0 (MkFiber r45Child Root False emptyOwned (Reloading [] id EmptyView))]
    (uniqueBindings (the (Registry Nat R45Key R45Value Unit String) (insertBinding @{r45NameEq} 1 (freshFiber r45Child Root)
      (insertBinding @{r45NameEq} 0 (freshFiber r45Child Root) emptyContext Refl) Refl))))
r182IndependentState (S (S (S (S Z)))) = MkSystemState ()
  (MkCoeffectContext [Bind 1 (freshFiber r45Child Root), Bind 0 (MkFiber r45Child Root False emptyOwned (Active id EmptyView))]
    (uniqueBindings (the (Registry Nat R45Key R45Value Unit String) (insertBinding @{r45NameEq} 1 (freshFiber r45Child Root)
      (insertBinding @{r45NameEq} 0 (freshFiber r45Child Root) emptyContext Refl) Refl))))
r182IndependentState (S (S (S (S (S Z))))) = MkSystemState ()
  (MkCoeffectContext [Bind 1 (MkFiber r45Child Root False emptyOwned (Reloading [] id EmptyView)), Bind 0 (MkFiber r45Child Root False emptyOwned (Active id EmptyView))]
    (uniqueBindings (the (Registry Nat R45Key R45Value Unit String) (insertBinding @{r45NameEq} 1 (freshFiber r45Child Root)
      (insertBinding @{r45NameEq} 0 (freshFiber r45Child Root) emptyContext Refl) Refl))))
r182IndependentState (S (S (S (S (S (S Z)))))) = MkSystemState ()
  (MkCoeffectContext [Bind 1 (MkFiber r45Child Root False emptyOwned (Active id EmptyView)), Bind 0 (MkFiber r45Child Root False emptyOwned (Active id EmptyView))]
    (uniqueBindings (the (Registry Nat R45Key R45Value Unit String) (insertBinding @{r45NameEq} 1 (freshFiber r45Child Root)
      (insertBinding @{r45NameEq} 0 (freshFiber r45Child Root) emptyContext Refl) Refl))))
r182IndependentState (S (S (S (S (S (S (S Z))))))) = MkSystemState ()
  (MkCoeffectContext [Bind 1 (MkFiber r45Child Root False emptyOwned (Reloading [] id EmptyView)), Bind 0 (freshFiber r45Child Root)]
    (uniqueBindings (the (Registry Nat R45Key R45Value Unit String) (insertBinding @{r45NameEq} 1 (freshFiber r45Child Root)
      (insertBinding @{r45NameEq} 0 (freshFiber r45Child Root) emptyContext Refl) Refl))))
r182IndependentState (S (S (S (S (S (S (S (S Z)))))))) = MkSystemState ()
  (MkCoeffectContext [Bind 1 (MkFiber r45Child Root False emptyOwned (Active id EmptyView)), Bind 0 (freshFiber r45Child Root)]
    (uniqueBindings (the (Registry Nat R45Key R45Value Unit String) (insertBinding @{r45NameEq} 1 (freshFiber r45Child Root)
      (insertBinding @{r45NameEq} 0 (freshFiber r45Child Root) emptyContext Refl) Refl))))
r182IndependentState (S (S (S (S (S (S (S (S (S later))))))))) = MkSystemState ()
  (MkCoeffectContext [Bind 1 (MkFiber r45Child Root False emptyOwned (Active id EmptyView)), Bind 0 (MkFiber r45Child Root False emptyOwned (Reloading [] id EmptyView))]
    (uniqueBindings (the (Registry Nat R45Key R45Value Unit String) (insertBinding @{r45NameEq} 1 (freshFiber r45Child Root)
      (insertBinding @{r45NameEq} 0 (freshFiber r45Child Root) emptyContext Refl) Refl))))

||| A6: BOTH full six-edge orders execute from the same empty origin to the
||| SAME explicit final state. Every equation is of one small explicit edge;
||| there is no nested builder/fallback or scalar execution observer.
public export
0 r182IndependentTrace : Bool -> Transitions (r182IndependentState 0) (r182IndependentState 6)
r182IndependentTrace False =
  MoreTransitions
   (Fired {before = r182IndependentState 0} {afterState = r182IndependentState 1}
     r45NameEq r45KeyEq (OInsert 0 Root r45Child) OInsertTag Refl)
   (MoreTransitions
    (Fired {before = r182IndependentState 1} {afterState = r182IndependentState 2}
      r45NameEq r45KeyEq (OInsert 1 Root r45Child) OInsertTag Refl)
    (MoreTransitions
     (Fired {before = r182IndependentState 2} {afterState = r182IndependentState 3}
       r45NameEq r45KeyEq (LBegin 0) LBeginTag Refl)
     (MoreTransitions
      (Fired {before = r182IndependentState 3} {afterState = r182IndependentState 4}
        r45NameEq r45KeyEq (LAdvance 0) LFinishTag Refl)
      (MoreTransitions
       (Fired {before = r182IndependentState 4} {afterState = r182IndependentState 5}
         r45NameEq r45KeyEq (LBegin 1) LBeginTag Refl)
       (MoreTransitions
        (Fired {before = r182IndependentState 5} {afterState = r182IndependentState 6}
          r45NameEq r45KeyEq (LAdvance 1) LFinishTag Refl)
        NoTransitions)))))
r182IndependentTrace True =
  MoreTransitions
   (Fired {before = r182IndependentState 0} {afterState = r182IndependentState 1}
     r45NameEq r45KeyEq (OInsert 0 Root r45Child) OInsertTag Refl)
   (MoreTransitions
    (Fired {before = r182IndependentState 1} {afterState = r182IndependentState 2}
      r45NameEq r45KeyEq (OInsert 1 Root r45Child) OInsertTag Refl)
    (MoreTransitions
     (Fired {before = r182IndependentState 2} {afterState = r182IndependentState 7}
       r45NameEq r45KeyEq (LBegin 1) LBeginTag Refl)
     (MoreTransitions
      (Fired {before = r182IndependentState 7} {afterState = r182IndependentState 8}
        r45NameEq r45KeyEq (LAdvance 1) LFinishTag Refl)
      (MoreTransitions
       (Fired {before = r182IndependentState 8} {afterState = r182IndependentState 9}
         r45NameEq r45KeyEq (LBegin 0) LBeginTag Refl)
       (MoreTransitions
        (Fired {before = r182IndependentState 9} {afterState = r182IndependentState 6}
          r45NameEq r45KeyEq (LAdvance 0) LFinishTag Refl)
        NoTransitions)))))
