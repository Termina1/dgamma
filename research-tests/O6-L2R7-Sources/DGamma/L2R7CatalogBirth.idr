module DGamma.L2R7CatalogBirth

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R5RootCatalog
import Data.List
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| A decoded actual native root birth for a catalog item. Offset is explicit:
||| the catalog ordinal is the scan offset plus the exact local occurrence.
||| This is not yet bundle placement or general gap coverage.
public export
record CatalogBirthAt
  (name, key, world, error : Type) (value : key -> Type)
  (entry : RootCatalogEntry name key world error value) (offset : Nat)
  {first, finalState : SystemState name key value world error}
  (trace : Transitions first finalState) where
  constructor MkCatalogBirthAt
  catalogBirthOccurrence : LocatedActionOccurrence (OInsert (catalogRoot entry) Root (catalogComponent entry)) trace
  0 catalogBirthOrdinal : catalogOrdinal entry = offset + locatedActionOrdinal catalogBirthOccurrence

||| Lift a decoded tail occurrence through exactly one native head. The
||| dependent endpoints are preserved by decomposition and count transport.
export
0 catalogBirthTail : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (step : Transition first middle) -> (rest : Transitions middle finalState) ->
  (entry : RootCatalogEntry name key world error value) -> (offset : Nat) ->
  CatalogBirthAt name key world error value entry (S offset) rest ->
  CatalogBirthAt name key world error value entry offset (MoreTransitions step rest)
catalogBirthTail step rest entry offset (MkCatalogBirthAt occurrence ordinal) = MkCatalogBirthAt
  (MkLocatedActionOccurrence (actionBeforeState occurrence) (actionAfterState occurrence)
    (MoreTransitions step (beforeActionOccurrence occurrence)) (locatedTransition occurrence)
    (afterActionOccurrence occurrence) (locatedAction occurrence)
    (cong (MoreTransitions step) (actionOccurrenceDecomposition occurrence)))
  (trans ordinal (plusSuccRightSucc offset (locatedActionOrdinal occurrence)))

||| A root-insertion catalog cons: decode either its genuine head birth or
||| the recursively decoded tail. Only membership is eliminated here.
export
0 catalogBirthInsertMember : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (step : Transition first middle) -> (rest : Transitions middle finalState) ->
  (root : name) -> (component : Component key value world error) -> (offset : Nat) ->
  (0 inserted : transitionAction step = OInsert root Root component) ->
  (tailCatalog : List (RootCatalogEntry name key world error value)) ->
  (0 tail : (item : RootCatalogEntry name key world error value) -> Elem item tailCatalog ->
    CatalogBirthAt name key world error value item (S offset) rest) ->
  (entry : RootCatalogEntry name key world error value) ->
  (0 member : Elem entry (MkRootCatalogEntry offset root component :: tailCatalog)) ->
  CatalogBirthAt name key world error value entry offset (MoreTransitions step rest)
catalogBirthInsertMember {first} {middle} step rest root component offset inserted tailCatalog tail _ Here =
  MkCatalogBirthAt (MkLocatedActionOccurrence first middle NoTransitions step rest inserted Refl)
    (sym (plusZeroRightNeutral offset))
catalogBirthInsertMember step rest root component offset inserted tailCatalog tail entry (There later) =
  catalogBirthTail step rest entry offset (tail entry later)
