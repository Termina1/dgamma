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

||| GENERAL suffix extension preserving the very same occurrence source and
||| step. Only the after-occurrence trail changes; no replay theorem is used.
export
0 extendOccurrence : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  {action : Action name key value world error} ->
  (region : Transitions first middle) -> (afterRegion : Transitions middle finalState) ->
  LocatedActionOccurrence action region -> LocatedActionOccurrence action (appendTransitions region afterRegion)
extendOccurrence region afterRegion occurrence = MkLocatedActionOccurrence
  (actionBeforeState occurrence) (actionAfterState occurrence) (beforeActionOccurrence occurrence)
  (locatedTransition occurrence) (appendTransitions (afterActionOccurrence occurrence) afterRegion)
  (locatedAction occurrence)
  (trans (sym (appendTransitionsAssociative (beforeActionOccurrence occurrence)
    (MoreTransitions (locatedTransition occurrence) (afterActionOccurrence occurrence)) afterRegion))
    (cong (\trace => appendTransitions trace afterRegion) (actionOccurrenceDecomposition occurrence)))

||| Full region-to-global observation contract: same physical action source,
||| exact offset + local ordinal, and source-aware root-control classification
||| transported too. The embedded occurrence is not just a matching name.
public export
record RegionEmbedding
  {name, key, world, error : Type} {value : key -> Type}
  {first, finalState, regionStart, regionEnd : SystemState name key value world error}
  {action : Action name key value world error}
  {region : Transitions regionStart regionEnd}
  (0 original : LocatedActionOccurrence action region)
  (global : Transitions first finalState) (offset : Nat) where
  constructor MkRegionEmbedding
  embeddedOccurrence : LocatedActionOccurrence action global
  0 embeddedOrdinal : locatedActionOrdinal embeddedOccurrence = offset + locatedActionOrdinal original
  0 embeddedSourceSame : actionBeforeState embeddedOccurrence = actionBeforeState original
  0 embeddedRootKind : (nameEq : DecEq name) ->
    RootOrchestrationStep nameEq (locatedTransition original) ->
    RootOrchestrationStep nameEq (locatedTransition embeddedOccurrence)
