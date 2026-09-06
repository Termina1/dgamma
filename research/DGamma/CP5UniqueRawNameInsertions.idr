module DGamma.CP5UniqueRawNameInsertions

import DGamma.Calculus
import DGamma.CP3
import Decidable.Equality

%default total
%unbound_implicits off

||| R173 strong global hypothesis: each raw name has at most one insertion
||| position, including root and generated insertions across all lifetimes.
||| Equality compares counts, not dependent states, components, or proof tokens.
public export
record UniqueRawNameInsertions
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, finalState : SystemState name key value world error}
  (trace : Transitions initial finalState) where
  constructor MkUniqueRawNameInsertions
  0 uniqueInsertionPosition :
    (selected : name) -> (leftParent, rightParent : Parent name) ->
    (leftComponent, rightComponent : Component key value world error) ->
    (left : LocatedActionOccurrence (OInsert selected leftParent leftComponent) trace) ->
    (right : LocatedActionOccurrence (OInsert selected rightParent rightComponent) trace) ->
    (locatedActionOrdinal left = locatedActionOrdinal right)

||| Executable insertion-only observation of an absolute transition position.
public export
rawInsertionNameAt :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {0 initial, finalState : SystemState name key value world error} ->
  Nat -> Transitions initial finalState -> Maybe name
rawInsertionNameAt name key world error value ordinal NoTransitions = Nothing
rawInsertionNameAt name key world error value Z (MoreTransitions (Fired nameEq keyEq action tag checked) rest) =
  case action of
    OInsert selected parent component => Just selected
    ORetire selected => Nothing
    ORemove selected => Nothing
    LBegin selected => Nothing
    LAdvance selected => Nothing
    LDivert selected => Nothing
    LLeave selected => Nothing
    LUnload selected => Nothing
rawInsertionNameAt name key world error value (S ordinal) (MoreTransitions step rest) =
  rawInsertionNameAt name key world error value ordinal rest
