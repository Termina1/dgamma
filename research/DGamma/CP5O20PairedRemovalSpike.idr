module DGamma.CP5O20PairedRemovalSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionFrameCore
import DGamma.CP5O20EpisodeSynchronizationSpike
import DGamma.CP5O20PairedPrefixProducerSpike
import DGamma.CP5O20AllNameSynchronizationSpike
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Exact lookup absence from an actual finite-domain exclusion. Observe the
||| primitive lookup explicitly; no computed dependent package is eliminated.
export
0 o20AbsentLookupObserved :
  {key : Type} -> {value : key -> Type} ->
  (keyEq : DecEq key) -> (wanted : key) -> (context : CoeffectContext key value) ->
  (Not (Elem wanted (bindingKeys (bindings context)))) ->
  (observed : Maybe (value wanted)) ->
  (lookupBinding @{keyEq} wanted context = observed) ->
  (lookupBinding @{keyEq} wanted context = Nothing)
o20AbsentLookupObserved keyEq wanted context absent Nothing exact = exact
o20AbsentLookupObserved keyEq wanted (MkCoeffectContext entries unique) absent (Just provided) exact =
  void (absent (lookupJustElem @{keyEq} wanted entries provided exact))

||| Removing a binding really makes that lookup absent. Uses the finite
||| unique-key invariant of the executable context, not a control postulate.
export
0 o20DeletedLookupAbsent :
  {key : Type} -> {value : key -> Type} ->
  (keyEq : DecEq key) -> (removed : key) -> (context : CoeffectContext key value) ->
  (lookupBinding @{keyEq} removed (deleteBinding @{keyEq} removed context) = Nothing)
o20DeletedLookupAbsent keyEq removed (MkCoeffectContext entries unique) =
  o20AbsentLookupObserved keyEq removed (deleteBinding @{keyEq} removed (MkCoeffectContext entries unique))
    (deletedKeyNotElem @{keyEq} removed entries unique)
    (lookupBinding @{keyEq} removed (deleteBinding @{keyEq} removed (MkCoeffectContext entries unique))) Refl
