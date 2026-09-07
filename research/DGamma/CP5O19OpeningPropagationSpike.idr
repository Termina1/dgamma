module DGamma.CP5O19OpeningPropagationSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5RankedEarlyApplicabilitySpike
import DGamma.CP5O19AdjacentReplayProducerSpike
import Decidable.Equality

%default total
%unbound_implicits off

||| Convert an OBSERVED raw move to an actual checked early guard. Both target
||| data and its equation are the existing producer's projections; preservation
||| derives the target-domain check, with no assumed intermediate applicability.
public export
0 o19CheckObservedRawMove :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (before : SystemState name key value world error) ->
  (registryWellFormed @{nameEq} @{keyEq} before = True) ->
  (raw : RawActivationMove nameEq keyEq action tag before) ->
  CheckedEarlyApplication name key world error value nameEq keyEq before action tag
o19CheckObservedRawMove nameEq keyEq action tag before wellFormed raw =
  MkCheckedEarlyApplication (rawActivationAfter raw)
    (rewrite rawActivationRuns raw in
     rewrite preservationTheoremProof nameEq keyEq action before
       (rawActivationAfter raw) tag wellFormed (rawActivationRuns raw) in Refl)
