module DGamma.L2R8RegionEmbedding

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5L2R1ExtendedZeroGap
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| GENERAL occurrence embedding through a native beforeRegion. The actual source,
||| target and Transition object are reused, not reconstructed from its word.
export
0 prependOccurrence : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  {action : Action name key value world error} ->
  (beforeRegion : Transitions first middle) -> (region : Transitions middle finalState) ->
  LocatedActionOccurrence action region -> LocatedActionOccurrence action (appendTransitions beforeRegion region)
prependOccurrence beforeRegion region occurrence = MkLocatedActionOccurrence
  (actionBeforeState occurrence) (actionAfterState occurrence)
  (appendTransitions beforeRegion (beforeActionOccurrence occurrence)) (locatedTransition occurrence)
  (afterActionOccurrence occurrence) (locatedAction occurrence)
  (trans (appendTransitionsAssociative beforeRegion (beforeActionOccurrence occurrence)
    (MoreTransitions (locatedTransition occurrence) (afterActionOccurrence occurrence)))
    (cong (appendTransitions beforeRegion) (actionOccurrenceDecomposition occurrence)))
