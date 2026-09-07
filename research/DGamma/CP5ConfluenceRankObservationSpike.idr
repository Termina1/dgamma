module DGamma.CP5ConfluenceRankObservationSpike

import DGamma.Calculus

%default total
%unbound_implicits off

||| An action-only observation of the ACTUAL checked trace, with arbitrary seed.
||| No origin selector, target word, or endpoint equality is taken as evidence.
public export
0 traceActionFold :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (observation : Type) ->
  (observe : Action name key value world error -> observation -> observation) ->
  (seed : observation) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) -> observation
traceActionFold name key world error value observation observe seed NoTransitions = seed
traceActionFold name key world error value observation observe seed (MoreTransitions step rest) =
  observe (transitionAction step) (traceActionFold name key world error value observation observe seed rest)
