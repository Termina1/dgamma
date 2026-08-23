module DGamma.R6GeneratedChildSafetyPositive

import DGamma.Calculus
import DGamma.CP5ConfluenceCrossTraceSpike

%default total

||| Exact parent/child licensing rejection now occurs at NoGeneratedChild,
||| independently of O20 or an effect-map correspondence.
public export
0 generatedChildBoundaryRejectedBeforeO20 :
  {key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState Nat key value world error} ->
  (component : Component key value world error) ->
  (insert : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  transitionAction insert = OInsert 1 (ChildOf 0) component ->
  NoGeneratedChild 1 (MoreTransitions insert rest) -> Void
generatedChildBoundaryRejectedBeforeO20 component insert rest exact safety =
  generatedChildAtHeadContradictsSafety insert rest exact safety
