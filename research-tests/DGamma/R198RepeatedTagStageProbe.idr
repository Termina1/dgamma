module DGamma.R198RepeatedTagStageProbe

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import Data.List.Elem
import Decidable.Equality

%default total
%unbound_implicits off

||| A two-step parent with the SAME registration tag on both actual steps.
||| No schedule, synchronization or accepted-capital claim is contained here.
public export
r198RepeatedParent : Component R45Key R45Value Unit String
r198RepeatedParent = MkComponent r45Spec r45Spec [r45YieldingStep, r45YieldingStep]

||| Literal cuts for one fork/join execution: left 2->3->5, right 2->4->5.
||| Both paths share the SAME states 0,1,2,5,6,7,8; no state equality oracle.
public export
r198StageState : Nat -> SystemState Nat R45Key R45Value Unit String
r198StageState Z = r45Initial
r198StageState (S Z) = MkSystemState ()
  (MkCoeffectContext [Bind 0 (freshFiber r198RepeatedParent Root)]
    (uniqueBindings (the (Registry Nat R45Key R45Value Unit String) (insertBinding @{r45NameEq} 0 (freshFiber r198RepeatedParent Root) emptyContext Refl))))
r198StageState (S (S Z)) = MkSystemState ()
  (MkCoeffectContext [Bind 0 (MkFiber r198RepeatedParent Root False emptyOwned (Reloading [r45YieldingStep, r45YieldingStep] id EmptyView))]
    (uniqueBindings (the (Registry Nat R45Key R45Value Unit String) (insertBinding @{r45NameEq} 0 (freshFiber r198RepeatedParent Root) emptyContext Refl))))
r198StageState (S (S (S Z))) = MkSystemState ()
  (MkCoeffectContext [Bind 1 r45ChildFresh, Bind 0 (MkFiber r198RepeatedParent Root False emptyOwned (Reloading [r45YieldingStep, r45YieldingStep] id EmptyView))]
    (uniqueBindings (the (Registry Nat R45Key R45Value Unit String) (insertBinding @{r45NameEq} 1 r45ChildFresh (insertBinding @{r45NameEq} 0 (freshFiber r198RepeatedParent Root) emptyContext Refl) Refl))))
r198StageState (S (S (S (S Z)))) = MkSystemState ()
  (MkCoeffectContext [Bind 0 (MkFiber r198RepeatedParent Root False (restrictOwnedPreservingOrder @{r45KeyEq} r45Spec emptyContext) (Reloading [r45YieldingStep] (pushLocalUndo @{r45KeyEq} r45Spec id id) EmptyView))]
    (uniqueBindings (the (Registry Nat R45Key R45Value Unit String) (insertBinding @{r45NameEq} 0 (freshFiber r198RepeatedParent Root) emptyContext Refl))))
r198StageState (S (S (S (S (S Z))))) = MkSystemState ()
  (MkCoeffectContext [Bind 1 r45ChildFresh, Bind 0 (MkFiber r198RepeatedParent Root False (restrictOwnedPreservingOrder @{r45KeyEq} r45Spec emptyContext) (Reloading [r45YieldingStep] (pushLocalUndo @{r45KeyEq} r45Spec id id) EmptyView))]
    (uniqueBindings (the (Registry Nat R45Key R45Value Unit String) (insertBinding @{r45NameEq} 1 r45ChildFresh (insertBinding @{r45NameEq} 0 (freshFiber r198RepeatedParent Root) emptyContext Refl) Refl))))
r198StageState (S (S (S (S (S (S Z)))))) = MkSystemState ()
  (MkCoeffectContext [Bind 1 r45ChildFresh, Bind 0 (MkFiber r198RepeatedParent Root False (restrictOwnedPreservingOrder @{r45KeyEq} r45Spec emptyContext) (Active (pushLocalUndo @{r45KeyEq} r45Spec (pushLocalUndo @{r45KeyEq} r45Spec id id) id) EmptyView))]
    (uniqueBindings (the (Registry Nat R45Key R45Value Unit String) (insertBinding @{r45NameEq} 1 r45ChildFresh (insertBinding @{r45NameEq} 0 (freshFiber r198RepeatedParent Root) emptyContext Refl) Refl))))
r198StageState (S (S (S (S (S (S (S Z))))))) = MkSystemState ()
  (MkCoeffectContext [Bind 1 (MkFiber r45Child (ChildOf 0) False emptyOwned (Reloading [] id EmptyView)), Bind 0 (MkFiber r198RepeatedParent Root False (restrictOwnedPreservingOrder @{r45KeyEq} r45Spec emptyContext) (Active (pushLocalUndo @{r45KeyEq} r45Spec (pushLocalUndo @{r45KeyEq} r45Spec id id) id) EmptyView))]
    (uniqueBindings (the (Registry Nat R45Key R45Value Unit String) (insertBinding @{r45NameEq} 1 r45ChildFresh (insertBinding @{r45NameEq} 0 (freshFiber r198RepeatedParent Root) emptyContext Refl) Refl))))
r198StageState (S (S (S (S (S (S (S (S later)))))))) = MkSystemState ()
  (MkCoeffectContext [Bind 1 (MkFiber r45Child (ChildOf 0) False emptyOwned (Active id EmptyView)), Bind 0 (MkFiber r198RepeatedParent Root False (restrictOwnedPreservingOrder @{r45KeyEq} r45Spec emptyContext) (Active (pushLocalUndo @{r45KeyEq} r45Spec (pushLocalUndo @{r45KeyEq} r45Spec id id) id) EmptyView))]
    (uniqueBindings (the (Registry Nat R45Key R45Value Unit String) (insertBinding @{r45NameEq} 1 r45ChildFresh (insertBinding @{r45NameEq} 0 (freshFiber r198RepeatedParent Root) emptyContext Refl) Refl))))
