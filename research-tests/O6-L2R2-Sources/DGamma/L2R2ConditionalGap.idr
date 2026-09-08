module DGamma.L2R2ConditionalGap

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ActorLifecycleOnlyExtended
import DGamma.CP5L2R1ExtendedZeroGap
import Decidable.Equality

%default total
%unbound_implicits off

||| Explicit residual-gap coverage obligation: a nonempty physical gap starts
||| with actual root orchestration. Normalization must PRODUCE this evidence;
||| it does not follow from ActorLifecycleOnlyExtended alone. No new block
||| grammar or availability-attachment variant is defined by this family.
public export
0 RemainingGapHeadIsRoot :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) ->
  {first, finalState : SystemState name key value world error} ->
  Transitions first finalState -> Type
RemainingGapHeadIsRoot nameEq NoTransitions = Unit
RemainingGapHeadIsRoot nameEq (MoreTransitions step rest) = RootOrchestrationStep nameEq step
