module DGamma.L2R4Localization

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5L2R1ExtendedZeroGap
import DGamma.L2R3Attached
import DGamma.L2R3AttachedGap
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| An actual checked root-insert occurrence at an exact physical ordinal.
||| The occurrence owns its native step and full trace decomposition; this is
||| not a tag-list assertion or an independently reconstructed system state.
public export
record RootInsertionAt
  (name, key, world, error : Type) (value : key -> Type)
  {first, finalState : SystemState name key value world error}
  (trace : Transitions first finalState) (ordinal : Nat) where
  constructor MkRootInsertionAt
  insertedRoot : name
  insertedComponent : Component key value world error
  rootOccurrence : LocatedActionOccurrence (OInsert insertedRoot Root insertedComponent) trace
  0 rootOrdinal : locatedActionOrdinal rootOccurrence = ordinal

||| Lift the SAME native root occurrence through a checked front, transporting
||| its ordinal by count additivity (not equality of reconstructed states).
export
0 rootInsertionAfterPrefix :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (front : Transitions first middle) -> (trace : Transitions middle finalState) ->
  {ordinal : Nat} -> RootInsertionAt name key world error value trace ordinal ->
  RootInsertionAt name key world error value (appendTransitions front trace)
    (transitionCount front + ordinal)
rootInsertionAfterPrefix front trace found =
  MkRootInsertionAt (insertedRoot found) (insertedComponent found)
    (MkLocatedActionOccurrence
      (actionBeforeState (rootOccurrence found)) (actionAfterState (rootOccurrence found))
      (appendTransitions front (beforeActionOccurrence (rootOccurrence found)))
      (locatedTransition (rootOccurrence found)) (afterActionOccurrence (rootOccurrence found))
      (locatedAction (rootOccurrence found))
      (trans (appendTransitionsAssociative front (beforeActionOccurrence (rootOccurrence found))
        (MoreTransitions (locatedTransition (rootOccurrence found)) (afterActionOccurrence (rootOccurrence found))))
        (cong (appendTransitions front) (actionOccurrenceDecomposition (rootOccurrence found)))))
    (trans (extendedCountAppend front (beforeActionOccurrence (rootOccurrence found)))
      (cong (transitionCount front +) (rootOrdinal found)))

||| Extend a root occurrence's suffix without changing its native step or
||| ordinal. Associativity supplies the actual extended trace decomposition.
export
0 rootInsertionBeforeSuffix :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (trace : Transitions first middle) -> (back : Transitions middle finalState) ->
  {ordinal : Nat} -> RootInsertionAt name key world error value trace ordinal ->
  RootInsertionAt name key world error value (appendTransitions trace back) ordinal
rootInsertionBeforeSuffix trace back found =
  MkRootInsertionAt (insertedRoot found) (insertedComponent found)
    (MkLocatedActionOccurrence
      (actionBeforeState (rootOccurrence found)) (actionAfterState (rootOccurrence found))
      (beforeActionOccurrence (rootOccurrence found)) (locatedTransition (rootOccurrence found))
      (appendTransitions (afterActionOccurrence (rootOccurrence found)) back)
      (locatedAction (rootOccurrence found))
      (trans (sym (appendTransitionsAssociative (beforeActionOccurrence (rootOccurrence found))
        (MoreTransitions (locatedTransition (rootOccurrence found)) (afterActionOccurrence (rootOccurrence found))) back))
        (cong (\part => appendTransitions part back) (actionOccurrenceDecomposition (rootOccurrence found)))))
    (rootOrdinal found)
