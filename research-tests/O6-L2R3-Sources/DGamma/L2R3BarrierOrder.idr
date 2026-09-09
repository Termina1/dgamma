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
