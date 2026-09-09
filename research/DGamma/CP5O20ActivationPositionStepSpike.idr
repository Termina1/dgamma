module DGamma.CP5O20ActivationPositionStepSpike

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import Data.List
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| A classified deleted birth leaves BOTH inputs to every parent's surviving
||| activation-position observation unchanged. Live generations and the deleted
||| list do change; no equality of full indexes or physical ordinals is claimed.
||| This local law is not canonical prefix-transport completeness.
export
0 o20DeletedBirthKeepsActivationPosition :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (ordinal : Nat) ->
  (child, parent : name) -> (component : Component key value world error) ->
  (index : RegistrationIndexState name) ->
  (indexedParentActivations (advanceDeletedRegistrationIndex @{nameEq} ordinal child parent component index) =
    indexedParentActivations index,
   indexedSurvivingChildCounts (advanceDeletedRegistrationIndex @{nameEq} ordinal child parent component index) =
    indexedSurvivingChildCounts index)
o20DeletedBirthKeepsActivationPosition nameEq ordinal child parent component
  (MkRegistrationIndexState live activations counts deleted) = (Refl, Refl)

||| Observe the native iterator position through an EXPLICIT activation
||| equation. This avoids an inferred case-view or an assumed position value.
export
0 o20EventActivationPositionKnown :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (ordinal : Nat) ->
  (child, parent : name) -> (component : Component key value world error) ->
  (index : RegistrationIndexState name) -> (activation : RegistrationActivation name) ->
  (lookupParentActivation @{nameEq} parent (indexedParentActivations index) = Just activation) ->
  (eventChildPosition (registrationEventAt @{nameEq} ordinal index child parent component) =
    childrenBornInActivation @{nameEq} activation (indexedSurvivingChildCounts index))
o20EventActivationPositionKnown nameEq ordinal child parent component
  (MkRegistrationIndexState live activations counts deleted) activation observed = rewrite observed in Refl
