module DGamma.L2R3BarrierOrder

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4ProgressNoDeadlock
import DGamma.CP5ActorLifecycleOnlyExtended
import DGamma.L2R2SmallStates
import DGamma.L2R2SmallExecution
import DGamma.L2R2SmallPlacement
import DGamma.L2R3Attached
import DGamma.L2R3BarrierStates
import DGamma.L2R3BarrierExecution
import DGamma.L2R3ForcedClosure
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Direct inversion of frozen CP3 SameExternalOrchestration:2051 and actual
||| RootOrchestrationStep:1986. Two actual root heads cannot be skipped: their
||| actions must match. In particular moving S before R cannot preserve it.
export
0 externalRootHeadsMatch :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} ->
  {leftFirst, leftMiddle, leftLast, rightFirst, rightMiddle, rightLast : SystemState name key value world error} ->
  {left : Transition leftFirst leftMiddle} -> {right : Transition rightFirst rightMiddle} ->
  {leftRest : Transitions leftMiddle leftLast} -> {rightRest : Transitions rightMiddle rightLast} ->
  (0 leftRoot : RootOrchestrationStep nameEq left) ->
  (0 rightRoot : RootOrchestrationStep nameEq right) ->
  SameExternalOrchestration nameEq (MoreTransitions left leftRest) (MoreTransitions right rightRest) ->
  transitionAction left = transitionAction right
externalRootHeadsMatch leftRoot rightRoot (SkipLeftInternal step rest rejected later) = void (rejected leftRoot)
externalRootHeadsMatch leftRoot rightRoot (SkipRightInternal step rest rejected later) = void (rejected rightRoot)
externalRootHeadsMatch leftRoot rightRoot (MatchExternalInput action left leftRest leftIsRoot right rightRest rightIsRoot leftSame rightSame later) =
  trans leftSame (sym rightSame)

||| Actual R/S birth locations, root classification and order on barrierTrace.
||| The least-closure instance uses the displayed root ordinals [4,5] and the
||| key-forced seed4; it does not classify arbitrary raw fiber names as roots.
||| Frozen strict placement is refuted uniformly in support state and order.
public export
record BarrierOrderEvidence where
  constructor MkBarrierOrderEvidence
  rBirth : LocatedActionOccurrence (OInsert 3 Root (smallComponent True)) barrierTrace
  sBirth : LocatedActionOccurrence (OInsert 4 Root (smallComponent False)) barrierTrace
  0 rOrdinal : locatedActionOrdinal rBirth = 4
  0 sOrdinal : locatedActionOrdinal sBirth = 5
  0 rRoot : RootOrchestrationStep %search (locatedTransition rBirth)
  0 sRoot : RootOrchestrationStep %search (locatedTransition sBirth)
  0 originalInputOrder : LT (locatedActionOrdinal rBirth) (locatedActionOrdinal sBirth)
  0 sForcedByOrder : ForcedRootInput (\n => Elem n [4,5]) (\n => n = 4) 5
  0 strictRejected : (supportState : SystemState Nat Bool (\key => Unit) Unit String) ->
    (order : List Nat) ->
    CanonicalInputPlacement Nat Bool Unit String (\key => Unit) %search %search supportState order barrierTrace -> Void

||| Simultaneous literal birth locations and strict-order contradiction; not
||| a scalar equality observer over a nested trace producer. S is forced by
||| OrderForces from R even though its own provisions are always free.
public export
0 barrierOrderEvidence : BarrierOrderEvidence
barrierOrderEvidence = MkBarrierOrderEvidence
  (MkLocatedActionOccurrence (barrierState 4) (barrierState 5) (MoreTransitions (Fired {before = barrierState 0} {afterState = barrierState 1} %search %search (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution)) (MoreTransitions (Fired {before = barrierState 1} {afterState = barrierState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) (MoreTransitions (Fired {before = barrierState 2} {afterState = barrierState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) (MoreTransitions (Fired {before = barrierState 3} {afterState = barrierState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) NoTransitions)))) (Fired {before = barrierState 4} {afterState = barrierState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) (MoreTransitions (Fired {before = barrierState 5} {afterState = barrierState 6} %search %search (OInsert 4 Root (smallComponent False)) OInsertTag (insertS barrierNativeExecution)) (MoreTransitions (Fired {before = barrierState 6} {afterState = barrierState 7} %search %search (LBegin 2) LBeginTag (beginFollowing barrierNativeExecution)) (MoreTransitions (Fired {before = barrierState 7} {afterState = barrierState 8} %search %search (LAdvance 2) LFinishTag (finishFollowing barrierNativeExecution)) NoTransitions))) Refl Refl)
  (MkLocatedActionOccurrence (barrierState 5) (barrierState 6) (MoreTransitions (Fired {before = barrierState 0} {afterState = barrierState 1} %search %search (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution)) (MoreTransitions (Fired {before = barrierState 1} {afterState = barrierState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) (MoreTransitions (Fired {before = barrierState 2} {afterState = barrierState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) (MoreTransitions (Fired {before = barrierState 3} {afterState = barrierState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) (MoreTransitions (Fired {before = barrierState 4} {afterState = barrierState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) NoTransitions))))) (Fired {before = barrierState 5} {afterState = barrierState 6} %search %search (OInsert 4 Root (smallComponent False)) OInsertTag (insertS barrierNativeExecution)) (MoreTransitions (Fired {before = barrierState 6} {afterState = barrierState 7} %search %search (LBegin 2) LBeginTag (beginFollowing barrierNativeExecution)) (MoreTransitions (Fired {before = barrierState 7} {afterState = barrierState 8} %search %search (LAdvance 2) LFinishTag (finishFollowing barrierNativeExecution)) NoTransitions)) Refl Refl)
  Refl Refl (RootInsertStep Refl) (RootInsertStep Refl)
  (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc LTEZero)))))
  (OrderForces (KeyForces Here Refl) (There Here)
    (LTESucc (LTESucc (LTESucc (LTESucc (LTESucc LTEZero))))))
  (\supportState, order, placement => succNotLTEzero
    (rootGenerationBeforeLifecycle placement (MkLocatedActionOccurrence (barrierState 4) (barrierState 5) (MoreTransitions (Fired {before = barrierState 0} {afterState = barrierState 1} %search %search (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution)) (MoreTransitions (Fired {before = barrierState 1} {afterState = barrierState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) (MoreTransitions (Fired {before = barrierState 2} {afterState = barrierState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) (MoreTransitions (Fired {before = barrierState 3} {afterState = barrierState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) NoTransitions)))) (Fired {before = barrierState 4} {afterState = barrierState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) (MoreTransitions (Fired {before = barrierState 5} {afterState = barrierState 6} %search %search (OInsert 4 Root (smallComponent False)) OInsertTag (insertS barrierNativeExecution)) (MoreTransitions (Fired {before = barrierState 6} {afterState = barrierState 7} %search %search (LBegin 2) LBeginTag (beginFollowing barrierNativeExecution)) (MoreTransitions (Fired {before = barrierState 7} {afterState = barrierState 8} %search %search (LAdvance 2) LFinishTag (finishFollowing barrierNativeExecution)) NoTransitions))) Refl Refl)
      (MkLocatedActionOccurrence (barrierState 0) (barrierState 1) NoTransitions (Fired {before = barrierState 0} {afterState = barrierState 1} %search %search (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution)) (MoreTransitions (Fired {before = barrierState 1} {afterState = barrierState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) (MoreTransitions (Fired {before = barrierState 2} {afterState = barrierState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) (MoreTransitions (Fired {before = barrierState 3} {afterState = barrierState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) (MoreTransitions (Fired {before = barrierState 4} {afterState = barrierState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) (MoreTransitions (Fired {before = barrierState 5} {afterState = barrierState 6} %search %search (OInsert 4 Root (smallComponent False)) OInsertTag (insertS barrierNativeExecution)) (MoreTransitions (Fired {before = barrierState 6} {afterState = barrierState 7} %search %search (LBegin 2) LBeginTag (beginFollowing barrierNativeExecution)) (MoreTransitions (Fired {before = barrierState 7} {afterState = barrierState 8} %search %search (LAdvance 2) LFinishTag (finishFollowing barrierNativeExecution)) NoTransitions))))))) Refl Refl) Refl))

||| Keeping the frozen external-input relation cannot make S the first root
||| of the actual R/S post-release suffix, for ANY checked S-headed candidate
||| and any continuation. Uses actual RootOrchestrationStep, not a tag list.
||| Generic transport of arbitrary internal prefixes is not asserted here.
export
0 rThenSCannotReverse :
  {first, middle, finalState : SystemState Nat Bool (\key => Unit) Unit String} ->
  (right : Transition first middle) -> (rest : Transitions middle finalState) ->
  (0 isS : transitionAction right = OInsert 4 Root (smallComponent False)) ->
  SameExternalOrchestration %search
    (MoreTransitions (Fired {before = barrierState 4} {afterState = barrierState 5} %search %search (OInsert 3 Root (smallComponent True)) OInsertTag (smallInsert3 smallNativeExecution)) (MoreTransitions (Fired {before = barrierState 5} {afterState = barrierState 6} %search %search (OInsert 4 Root (smallComponent False)) OInsertTag (insertS barrierNativeExecution)) (MoreTransitions (Fired {before = barrierState 6} {afterState = barrierState 7} %search %search (LBegin 2) LBeginTag (beginFollowing barrierNativeExecution)) (MoreTransitions (Fired {before = barrierState 7} {afterState = barrierState 8} %search %search (LAdvance 2) LFinishTag (finishFollowing barrierNativeExecution)) NoTransitions))))
    (MoreTransitions right rest) -> Void
rThenSCannotReverse right rest isS same =
  uninhabited (cong actionOwner
    (trans (externalRootHeadsMatch (RootInsertStep Refl) (RootInsertStep isS) same) isS))
