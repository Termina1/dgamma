module DGamma.CP5CurrentGenerationBirthSpike

import DGamma.Calculus
import DGamma.CP3
import DGamma.CP4DeletionBoundaryPlan
import DGamma.CP5RawClosingRankSpike
import DGamma.CP5UniqueRawNameInsertions
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| An authenticated scanner stamp names an actual insertion of the selected
||| raw name in the ORIGINAL checked trace. No caller-selected origin map.
public export
record CurrentGenerationBirth
  (name, key, world, error : Type) (value : key -> Type)
  {initial, finalState : SystemState name key value world error}
  (trace : Transitions initial finalState) (selected : name)
  (generation : RegistrationGeneration name) where
  constructor MkCurrentGenerationBirth
  currentBirthParent : Parent name
  currentBirthComponent : Component key value world error
  currentLocatedBirth : LocatedActionOccurrence
    (OInsert selected currentBirthParent currentBirthComponent) trace
  0 currentBirthStampExact : generation =
    MkRegistrationGeneration selected (locatedActionOrdinal currentLocatedBirth)

||| Observe the exact dictionary decision once, retaining its equation.
0 currentPutObserved :
  (name : Type) -> (nameEq : DecEq name) ->
  (inserted : name) -> (fresh : RegistrationGeneration name) ->
  (candidate : name) -> (current : RegistrationGeneration name) ->
  (rest : GenerationEnvironment name) -> (observed : Dec (inserted = candidate)) ->
  (decEq @{nameEq} inserted candidate = observed) ->
  (putCurrentGeneration @{nameEq} inserted fresh ((candidate, current) :: rest) =
    (case observed of
      Yes same => (inserted, fresh) :: rest
      No distinct => (candidate, current) :: putCurrentGeneration @{nameEq} inserted fresh rest))
currentPutObserved name nameEq inserted fresh candidate current rest (Yes same) exact =
  rewrite exact in case same of Refl => Refl
currentPutObserved name nameEq inserted fresh candidate current rest (No distinct) exact =
  rewrite exact in Refl
