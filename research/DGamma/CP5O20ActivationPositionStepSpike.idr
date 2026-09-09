module DGamma.CP5O20ActivationPositionStepSpike

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import Prelude.Types
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

||| Exact native position preservation across one classified deleted birth.
||| Its source activation is observed, not its target position. The target
||| activation and counter equations are PRODUCED by A8 and used by A9.
export
0 o20DeletedBirthPreservesObservedPosition :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (ordinal, nextOrdinal : Nat) ->
  (child, parent, nextChild, nextParent : name) ->
  (component, nextComponent : Component key value world error) ->
  (index : RegistrationIndexState name) -> (activation : RegistrationActivation name) ->
  (lookupParentActivation @{nameEq} nextParent (indexedParentActivations index) = Just activation) ->
  (eventChildPosition (registrationEventAt @{nameEq} nextOrdinal
      (advanceDeletedRegistrationIndex @{nameEq} ordinal child parent component index)
      nextChild nextParent nextComponent) =
    eventChildPosition (registrationEventAt @{nameEq} nextOrdinal index nextChild nextParent nextComponent))
o20DeletedBirthPreservesObservedPosition nameEq ordinal nextOrdinal child parent nextChild nextParent
  component nextComponent index activation observed =
    trans
      (o20EventActivationPositionKnown nameEq nextOrdinal nextChild nextParent nextComponent
        (advanceDeletedRegistrationIndex @{nameEq} ordinal child parent component index) activation
        (trans (cong (lookupParentActivation @{nameEq} nextParent)
          (fst (o20DeletedBirthKeepsActivationPosition nameEq ordinal child parent component index))) observed))
      (trans (cong (childrenBornInActivation @{nameEq} activation)
        (snd (o20DeletedBirthKeepsActivationPosition nameEq ordinal child parent component index)))
        (sym (o20EventActivationPositionKnown nameEq nextOrdinal nextChild nextParent nextComponent index activation observed)))

||| Boolean Nat equality used by the executable activation-counter key.
export
0 o20ActivationOrdinalSelf : (ordinal : Nat) -> (ordinal == ordinal = True)
o20ActivationOrdinalSelf Z = Refl
o20ActivationOrdinalSelf (S ordinal) = o20ActivationOrdinalSelf ordinal
