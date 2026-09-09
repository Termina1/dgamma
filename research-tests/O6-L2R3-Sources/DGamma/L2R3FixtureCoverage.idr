module DGamma.L2R3FixtureCoverage

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4ProgressNoDeadlock
import DGamma.CP5ActorLifecycleOnlyExtended
import DGamma.CP5L2R1ExtendedZeroGap
import DGamma.L2R2ConditionalGap
import DGamma.L2R2SmallStates
import DGamma.L2R2SmallExecution
import DGamma.L2R3Attached
import DGamma.L2R3AttachedGap
import DGamma.L2R3SmallAttached
import DGamma.L2R3BarrierStates
import DGamma.L2R3BarrierExecution
import DGamma.L2R3BarrierBlocks
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| No actual action occurrence exists in an empty residual gap. This is the
||| HONESTLY VACUOUS post-attachment NF case, not nonvacuous root membership.
||| Exact occurrence decomposition and structural count additivity refute it.
export
0 emptyGapHasNoOccurrence :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {state : SystemState name key value world error} ->
  {action : Action name key value world error} ->
  LocatedActionOccurrence action (NoTransitions {state}) -> Void
emptyGapHasNoOccurrence occurrence =
  uninhabited (trans
    (plusSuccRightSucc (transitionCount (beforeActionOccurrence occurrence)) (transitionCount (afterActionOccurrence occurrence)))
    (trans (sym (extendedCountAppend (beforeActionOccurrence occurrence)
      (MoreTransitions (locatedTransition occurrence) (afterActionOccurrence occurrence))))
      (cong transitionCount (actionOccurrenceDecomposition occurrence))))
