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


||| Typed observed entry transport for parent activations.
0 parentPutEntryObserved :
  (name : Type) -> (nameEq : DecEq name) ->
  (inserted : name) -> (fresh : RegistrationActivation name) ->
  (candidate : name) -> (current : RegistrationActivation name) ->
  (rest : List (name, RegistrationActivation name)) -> (observed : Dec (inserted = candidate)) ->
  (decEq @{nameEq} inserted candidate = observed) ->
  ((selected : name) -> (generation : RegistrationActivation name) ->
    Elem (selected, generation) (putParentActivation @{nameEq} inserted fresh rest) ->
    Either ((selected, generation) = (inserted, fresh)) (Elem (selected, generation) rest)) ->
  (selected : name) -> (generation : RegistrationActivation name) ->
  Elem (selected, generation) (putParentActivation @{nameEq} inserted fresh ((candidate, current) :: rest)) ->
  Either ((selected, generation) = (inserted, fresh)) (Elem (selected, generation) ((candidate, current) :: rest))
parentPutEntryObserved name nameEq inserted fresh candidate current rest (Yes same) exact recur selected generation member =
  case replace {p = Elem (selected, generation)}
    (parentPutObserved name nameEq inserted fresh candidate current rest (Yes same) exact) member of
    Here => Left Refl
    There later => Right (There later)
parentPutEntryObserved name nameEq inserted fresh candidate current rest (No distinct) exact recur selected generation member =
  case replace {p = Elem (selected, generation)}
    (parentPutObserved name nameEq inserted fresh candidate current rest (No distinct) exact) member of
    Here => Right Here
    There later => case recur selected generation later of
      Left same => Left same
      Right old => Right (There old)


||| A stored parent activation is the inserted one or a genuine prior entry.
0 parentPutEntryOrigin :
  (name : Type) -> (nameEq : DecEq name) ->
  (inserted : name) -> (fresh : RegistrationActivation name) ->
  (live : List (name, RegistrationActivation name)) ->
  (selected : name) -> (generation : RegistrationActivation name) ->
  Elem (selected, generation) (putParentActivation @{nameEq} inserted fresh live) ->
  Either ((selected, generation) = (inserted, fresh)) (Elem (selected, generation) live)
parentPutEntryOrigin name nameEq inserted fresh [] selected generation member = case member of
  Here => Left Refl
  There later => absurd later
parentPutEntryOrigin name nameEq inserted fresh ((candidate, current) :: rest) selected generation member =
  parentPutEntryObserved name nameEq inserted fresh candidate current rest
    (decEq @{nameEq} inserted candidate) Refl
    (parentPutEntryOrigin name nameEq inserted fresh rest) selected generation member


||| A parent activation carries the genuine insertion birth of its stamped generation.
0 parentBirthAfterPut :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) ->
  {initial, finalState : SystemState name key value world error} ->
  (global : Transitions initial finalState) -> (live : List (name, RegistrationActivation name)) ->
  (inserted : name) -> (fresh : RegistrationActivation name) ->
  CurrentGenerationBirth name key world error value global inserted (activationParentGeneration fresh) ->
  ((selected : name) -> (generation : RegistrationActivation name) ->
    Elem (selected, generation) live -> CurrentGenerationBirth name key world error value global selected (activationParentGeneration generation)) ->
  (selected : name) -> (generation : RegistrationActivation name) ->
  Elem (selected, generation) (putParentActivation @{nameEq} inserted fresh live) ->
  CurrentGenerationBirth name key world error value global selected (activationParentGeneration generation)
parentBirthAfterPut name key world error value nameEq global live inserted fresh birth previous selected generation member =
  case parentPutEntryOrigin name nameEq inserted fresh live selected generation member of
    Left exact => case exact of Refl => birth
    Right old => previous selected generation old


||| Observe only activation-index deletion; this is not a trace withdrawal proof.
0 parentDeleteObserved :
  (name : Type) -> (nameEq : DecEq name) -> (removed, candidate : name) ->
  (current : RegistrationActivation name) -> (rest : List (name, RegistrationActivation name)) ->
  (observed : Dec (removed = candidate)) -> decEq @{nameEq} removed candidate = observed ->
  deleteParentActivation @{nameEq} removed ((candidate, current) :: rest) =
    (case observed of
      Yes same => rest
      No distinct => (candidate, current) :: deleteParentActivation @{nameEq} removed rest)
parentDeleteObserved name nameEq removed candidate current rest (Yes same) exact =
  rewrite exact in case same of Refl => Refl
parentDeleteObserved name nameEq removed candidate current rest (No distinct) exact =
  rewrite exact in Refl

0 parentDeleteEntryObserved :
  (name : Type) -> (nameEq : DecEq name) -> (removed, candidate : name) ->
  (current : RegistrationActivation name) -> (rest : List (name, RegistrationActivation name)) ->
  (observed : Dec (removed = candidate)) -> decEq @{nameEq} removed candidate = observed ->
  ((selected : name) -> (activation : RegistrationActivation name) ->
    Elem (selected, activation) (deleteParentActivation @{nameEq} removed rest) -> Elem (selected, activation) rest) ->
  (selected : name) -> (activation : RegistrationActivation name) ->
  Elem (selected, activation) (deleteParentActivation @{nameEq} removed ((candidate, current) :: rest)) ->
  Elem (selected, activation) ((candidate, current) :: rest)
parentDeleteEntryObserved name nameEq removed candidate current rest (Yes same) exact recur selected activation member =
  There (replace {p = Elem (selected, activation)}
    (parentDeleteObserved name nameEq removed candidate current rest (Yes same) exact) member)
parentDeleteEntryObserved name nameEq removed candidate current rest (No distinct) exact recur selected activation member =
  case replace {p = Elem (selected, activation)}
    (parentDeleteObserved name nameEq removed candidate current rest (No distinct) exact) member of
    Here => Here
    There later => There (recur selected activation later)

0 parentDeleteEntryOrigin :
  (name : Type) -> (nameEq : DecEq name) -> (removed : name) ->
  (activations : List (name, RegistrationActivation name)) ->
  (selected : name) -> (activation : RegistrationActivation name) ->
  Elem (selected, activation) (deleteParentActivation @{nameEq} removed activations) ->
  Elem (selected, activation) activations
parentDeleteEntryOrigin name nameEq removed [] selected activation member = absurd member
parentDeleteEntryOrigin name nameEq removed ((candidate, current) :: rest) selected activation member =
  parentDeleteEntryObserved name nameEq removed candidate current rest
    (decEq @{nameEq} removed candidate) Refl
    (parentDeleteEntryOrigin name nameEq removed rest) selected activation member
