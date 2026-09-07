module DGamma.R178GeneratedOrchestrationFixtures

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.Metatheory
import DGamma.CP4ProgressNoDeadlock
import DGamma.CP5GeneratedOrchestrationMatched
import DGamma.CP5RawClosingRankSpike
import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import Decidable.Equality
import Data.Nat

%default total
%unbound_implicits off

||| Exact state selected by R177 P2-4 after the common parent's LFinish.
||| State expressions retain the evaluator's actual table/accumulator structure.
public export
r178ParentDoneState : SystemState Nat R45Key R45Value Unit String
r178ParentDoneState = MkSystemState ()
  (replaceBinding @{r45NameEq} 0
    (setFiberRuntime r45ParentBegun
      (restrictOwnedPreservingOrder @{r45KeyEq} r45Spec (ownedValues (fiberTable r45ParentBegun)))
      (Active (pushLocalUndo @{r45KeyEq} r45Spec id id) EmptyView))
    r45SourcePairFinalRegistry)

||| Use the PREVIOUS CHECKED transition's target-validity theorem, not an
||| independently recomputed raw child insertion equation (R177 P2-2 wall).
public export
r178ParentFinish : Transition r45SourcePairFinal r178ParentDoneState
r178ParentFinish = Fired r45NameEq r45KeyEq (LAdvance 0) LFinishTag
  (DGamma.CP4ProgressNoDeadlock.checkedFromRaw r45NameEq r45KeyEq
    (LAdvance 0) r45SourcePairFinal r178ParentDoneState LFinishTag
    (checkedTransitionTargetValid r45ChildInsert) Refl)

public export
r178ChildBegunState : SystemState Nat R45Key R45Value Unit String
r178ChildBegunState = MkSystemState ()
  (replaceBinding @{r45NameEq} 1
    (setFiberLifecycle r45ChildFresh (Reloading [] id EmptyView))
    (registry r178ParentDoneState))

public export
r178ChildBegin : Transition r178ParentDoneState r178ChildBegunState
r178ChildBegin = Fired r45NameEq r45KeyEq (LBegin 1) LBeginTag
  (DGamma.CP4ProgressNoDeadlock.checkedFromRaw r45NameEq r45KeyEq
    (LBegin 1) r178ParentDoneState r178ChildBegunState LBeginTag
    (checkedTransitionTargetValid r178ParentFinish) Refl)

public export
r178LeftFinal : SystemState Nat R45Key R45Value Unit String
r178LeftFinal = MkSystemState ()
  (replaceBinding @{r45NameEq} 1
    (setFiberLifecycle r45ChildFresh (Active id EmptyView))
    (registry r178ParentDoneState))

public export
r178ChildFinish : Transition r178ChildBegunState r178LeftFinal
r178ChildFinish = Fired r45NameEq r45KeyEq (LAdvance 1) LFinishTag
  (DGamma.CP4ProgressNoDeadlock.checkedFromRaw r45NameEq r45KeyEq
    (LAdvance 1) r178ChildBegunState r178LeftFinal LFinishTag
    (checkedTransitionTargetValid r178ChildBegin) Refl)

public export
r178RightFinal : SystemState Nat R45Key R45Value Unit String
r178RightFinal = MkSystemState ()
  (replaceBinding @{r45NameEq} 1 r45ChildRetired (registry r178ParentDoneState))
