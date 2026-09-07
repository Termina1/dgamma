module DGamma.CP5RegistrationParentBirthSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP4DeletionBoundaryPlan
import DGamma.CP5CurrentGenerationBirthSpike
import DGamma.CP5ImmutableBirthMetadataSpike
import Data.List.Elem
import Decidable.Equality

%default total
%unbound_implicits off

||| Every stored current generation AND parent-activation generation has a
||| genuine birth of its stored raw name in the fixed ORIGINAL global trace.
||| Historical parent stamps need not be endpoint-current; that is separate.
public export
record RegistrationIndexBirths
  (name, key, world, error : Type) (value : key -> Type)
  {initial, finalState : SystemState name key value world error}
  (global : Transitions initial finalState) (index : RegistrationIndexState name) where
  constructor MkRegistrationIndexBirths
  0 indexCurrentBirths : (selected : name) -> (generation : RegistrationGeneration name) ->
    Elem (selected, generation) (indexedLiveGenerations index) ->
    CurrentGenerationBirth name key world error value global selected generation
  0 indexActivationBirths : (selected : name) -> (activation : RegistrationActivation name) ->
    Elem (selected, activation) (indexedParentActivations index) ->
    CurrentGenerationBirth name key world error value global selected (activationParentGeneration activation)

||| Observe the actual parent-activation dictionary branch explicitly.
0 parentPutObserved :
  (name : Type) -> (nameEq : DecEq name) ->
  (inserted : name) -> (fresh : RegistrationActivation name) ->
  (candidate : name) -> (current : RegistrationActivation name) ->
  (rest : List (name, RegistrationActivation name)) -> (observed : Dec (inserted = candidate)) ->
  (decEq @{nameEq} inserted candidate = observed) ->
  (putParentActivation @{nameEq} inserted fresh ((candidate, current) :: rest) =
    (case observed of
      Yes same => (inserted, fresh) :: rest
      No distinct => (candidate, current) :: putParentActivation @{nameEq} inserted fresh rest))
parentPutObserved name nameEq inserted fresh candidate current rest (Yes same) exact =
  rewrite exact in case same of Refl => Refl
parentPutObserved name nameEq inserted fresh candidate current rest (No distinct) exact =
  rewrite exact in Refl

