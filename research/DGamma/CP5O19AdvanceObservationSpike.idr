module DGamma.CP5O19AdvanceObservationSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import Data.List
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Captured-map rebasing from EXPLICIT equal owner observations. The source
||| states may differ in ambient state and every foreign fiber. This observes
||| the primitive map, not a nested existential replay/diamond builder.
export
0 o19AdvanceCapturedMapAt :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (earlier, later : SystemState name key value world error) ->
  (fiber : Fiber name key value world error) -> (tag : RuleTag) ->
  (lookupFiber @{nameEq} actor (registry earlier) = Just fiber) ->
  (lookupFiber @{nameEq} actor (registry later) = Just fiber) ->
  (state : EffectState name key value world) ->
  partialEffectMapFor nameEq keyEq (LAdvance actor) tag earlier state =
  partialEffectMapFor nameEq keyEq (LAdvance actor) tag later state
o19AdvanceCapturedMapAt nameEq keyEq actor earlier later fiber OInsertTag foundEarly foundLate state = Refl
o19AdvanceCapturedMapAt nameEq keyEq actor earlier later fiber ORetireTag foundEarly foundLate state = Refl
o19AdvanceCapturedMapAt nameEq keyEq actor earlier later fiber ORemoveTag foundEarly foundLate state = Refl
o19AdvanceCapturedMapAt nameEq keyEq actor earlier later fiber LBeginTag foundEarly foundLate state = Refl
o19AdvanceCapturedMapAt nameEq keyEq actor earlier later fiber LIterTag foundEarly foundLate state =
  rewrite foundEarly in rewrite foundLate in Refl
o19AdvanceCapturedMapAt nameEq keyEq actor earlier later fiber LFinishTag foundEarly foundLate state =
  rewrite foundEarly in rewrite foundLate in Refl
o19AdvanceCapturedMapAt nameEq keyEq actor earlier later fiber LDivertTag foundEarly foundLate state =
  rewrite foundEarly in rewrite foundLate in Refl
o19AdvanceCapturedMapAt nameEq keyEq actor earlier later fiber LRaiseTag foundEarly foundLate state = Refl
o19AdvanceCapturedMapAt nameEq keyEq actor earlier later fiber LLeaveTag foundEarly foundLate state = Refl
o19AdvanceCapturedMapAt nameEq keyEq actor earlier later fiber LUnloadTag foundEarly foundLate state = Refl
