module DGamma.CP5O20RightOpeningTransportSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5O20BeginObservationSpike
import DGamma.CP5O19OpeningPropagationSpike
import DGamma.CP5RankedEarlyApplicabilitySpike
import Decidable.Equality

%default total
%unbound_implicits off

||| Backward physical Begin transport from the LATER actual opening's owned
||| component/view. The earlier evaluator destination is constructed here.
||| The two primitive lookup/resolver frames remain explicit obligations;
||| this is NOT yet their extraction from supported incomparability.
export
0 o20RightBeginAtEarlierObservation :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (earlier, later, laterAfter : SystemState name key value world error) ->
  (observation : O20BeginObservation name key world error value nameEq keyEq actor later laterAfter) ->
  (registryWellFormed @{nameEq} @{keyEq} earlier = True) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry earlier) =
   lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry later)) ->
  (resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (dependencies (componentDependencies (beginObservedComponent observation))) (registry earlier) =
   resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (dependencies (componentDependencies (beginObservedComponent observation))) (registry later)) ->
  CheckedEarlyApplication name key world error value nameEq keyEq earlier (LBegin actor) LBeginTag
o20RightBeginAtEarlierObservation nameEq keyEq actor earlier later laterAfter
  (MkO20BeginObservation component parent table view found resolved afterExact) wellFormed ownerFrame resolverFrame =
    o19CheckObservedRawMove nameEq keyEq (LBegin actor) LBeginTag earlier wellFormed
      (MkRawActivationMove
        (MkSystemState (worldState earlier) (replaceBinding @{nameEq} actor
          (MkFiber component parent False table (Reloading (componentProgram component) id view)) (registry earlier)))
        (rewrite trans ownerFrame found in rewrite trans resolverFrame resolved in Refl))
