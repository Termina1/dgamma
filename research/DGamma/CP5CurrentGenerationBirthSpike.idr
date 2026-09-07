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

||| A put entry is either the exact inserted pair or an actual old entry.
||| The recursive view is typed explicitly, never inferred through a local let.
0 currentPutEntryObserved :
  (name : Type) -> (nameEq : DecEq name) ->
  (inserted : name) -> (fresh : RegistrationGeneration name) ->
  (candidate : name) -> (current : RegistrationGeneration name) ->
  (rest : GenerationEnvironment name) -> (observed : Dec (inserted = candidate)) ->
  (decEq @{nameEq} inserted candidate = observed) ->
  ((selected : name) -> (generation : RegistrationGeneration name) ->
    Elem (selected, generation) (putCurrentGeneration @{nameEq} inserted fresh rest) ->
    Either ((selected, generation) = (inserted, fresh)) (Elem (selected, generation) rest)) ->
  (selected : name) -> (generation : RegistrationGeneration name) ->
  Elem (selected, generation) (putCurrentGeneration @{nameEq} inserted fresh ((candidate, current) :: rest)) ->
  Either ((selected, generation) = (inserted, fresh)) (Elem (selected, generation) ((candidate, current) :: rest))
currentPutEntryObserved name nameEq inserted fresh candidate current rest (Yes same) exact recur selected generation member =
  case replace {p = Elem (selected, generation)}
    (currentPutObserved name nameEq inserted fresh candidate current rest (Yes same) exact) member of
    Here => Left Refl
    There later => Right (There later)
currentPutEntryObserved name nameEq inserted fresh candidate current rest (No distinct) exact recur selected generation member =
  case replace {p = Elem (selected, generation)}
    (currentPutObserved name nameEq inserted fresh candidate current rest (No distinct) exact) member of
    Here => Right Here
    There later => case recur selected generation later of
      Left same => Left same
      Right old => Right (There old)

0 currentPutEntryOrigin :
  (name : Type) -> (nameEq : DecEq name) ->
  (inserted : name) -> (fresh : RegistrationGeneration name) ->
  (live : GenerationEnvironment name) ->
  (selected : name) -> (generation : RegistrationGeneration name) ->
  Elem (selected, generation) (putCurrentGeneration @{nameEq} inserted fresh live) ->
  Either ((selected, generation) = (inserted, fresh)) (Elem (selected, generation) live)
currentPutEntryOrigin name nameEq inserted fresh [] selected generation member = case member of
  Here => Left Refl
  There later => absurd later
currentPutEntryOrigin name nameEq inserted fresh ((candidate, current) :: rest) selected generation member =
  currentPutEntryObserved name nameEq inserted fresh candidate current rest
    (decEq @{nameEq} inserted candidate) Refl
    (currentPutEntryOrigin name nameEq inserted fresh rest) selected generation member

0 currentBirthAfterPut :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) ->
  {initial, finalState : SystemState name key value world error} ->
  (global : Transitions initial finalState) -> (live : GenerationEnvironment name) ->
  (inserted : name) -> (fresh : RegistrationGeneration name) ->
  CurrentGenerationBirth name key world error value global inserted fresh ->
  ((selected : name) -> (generation : RegistrationGeneration name) ->
    Elem (selected, generation) live -> CurrentGenerationBirth name key world error value global selected generation) ->
  (selected : name) -> (generation : RegistrationGeneration name) ->
  Elem (selected, generation) (putCurrentGeneration @{nameEq} inserted fresh live) ->
  CurrentGenerationBirth name key world error value global selected generation
currentBirthAfterPut name key world error value nameEq global live inserted fresh birth previous selected generation member =
  case currentPutEntryOrigin name nameEq inserted fresh live selected generation member of
    Left exact => case exact of Refl => birth
    Right old => previous selected generation old

||| The generation update introduces only the actual head insertion at its
||| authenticated global ordinal; all other entries retain their real births.
0 currentBirthAfterAction :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) ->
  {initial, finalState : SystemState name key value world error} ->
  (global : Transitions initial finalState) -> (ordinal : Nat) ->
  (live : GenerationEnvironment name) -> (action : Action name key value world error) ->
  (occurrence : LocatedActionOccurrence action global) ->
  (locatedActionOrdinal occurrence = ordinal) ->
  ((selected : name) -> (generation : RegistrationGeneration name) ->
    Elem (selected, generation) live -> CurrentGenerationBirth name key world error value global selected generation) ->
  (selected : name) -> (generation : RegistrationGeneration name) ->
  Elem (selected, generation) (advanceGenerationEnvironment @{nameEq} ordinal action live) ->
  CurrentGenerationBirth name key world error value global selected generation
currentBirthAfterAction name key world error value nameEq global ordinal live (OInsert inserted parent component) occurrence exact previous =
  currentBirthAfterPut name key world error value nameEq global live inserted (MkRegistrationGeneration inserted ordinal)
    (MkCurrentGenerationBirth parent component occurrence (sym (cong (MkRegistrationGeneration inserted) exact))) previous
currentBirthAfterAction name key world error value nameEq global ordinal live (ORetire actor) occurrence exact previous = previous
currentBirthAfterAction name key world error value nameEq global ordinal live (ORemove actor) occurrence exact previous =
  \selected, generation, member => previous selected generation (entryAfterDeleteComesFromOld nameEq actor live selected generation member)
currentBirthAfterAction name key world error value nameEq global ordinal live (LBegin actor) occurrence exact previous = previous
currentBirthAfterAction name key world error value nameEq global ordinal live (LAdvance actor) occurrence exact previous = previous
currentBirthAfterAction name key world error value nameEq global ordinal live (LDivert actor) occurrence exact previous = previous
currentBirthAfterAction name key world error value nameEq global ordinal live (LLeave actor) occurrence exact previous = previous
currentBirthAfterAction name key world error value nameEq global ordinal live (LUnload actor) occurrence exact previous = previous
