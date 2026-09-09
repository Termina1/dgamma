module DGamma.CP5O20StampedOrdinalNecessitySpike

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionInactiveInvariant
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorOpen
import DGamma.CP5O20HistoryNameTransportSpike
import DGamma.CP5O20StampedHistoryFoldSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| A pointwise stamp predicate survives put at the observed name decision.
||| Both library lookup laws concern the SAME updated environment. The observed
||| Dec carries its own library equation; no computed branch is hidden.
export
0 o20LivePredicatePutAtDecision :
  {name : Type} -> (nameEq : DecEq name) ->
  (predicate : RegistrationGeneration name -> Type) ->
  (actor : name) -> (newStamp : RegistrationGeneration name) ->
  (live : GenerationEnvironment name) ->
  predicate newStamp ->
  ((selected : name) -> (stamp : RegistrationGeneration name) ->
    (lookupCurrentGeneration @{nameEq} selected live = Just stamp) -> predicate stamp) ->
  (selected : name) -> (stamp : RegistrationGeneration name) ->
  (decision : Dec (selected = actor)) -> (decEq @{nameEq} selected actor = decision) ->
  (lookupCurrentGeneration @{nameEq} selected (putCurrentGeneration @{nameEq} actor newStamp live) = Just stamp) ->
  predicate stamp
o20LivePredicatePutAtDecision nameEq predicate actor newStamp live inserted previous
  selected stamp (Yes same) observed found =
    replace {p = predicate}
      (justInjective (trans (sym (lookupPutCurrentSelf nameEq actor newStamp live))
        (trans (sym (cong (\query => lookupCurrentGeneration @{nameEq} query
          (putCurrentGeneration @{nameEq} actor newStamp live)) same)) found))) inserted
o20LivePredicatePutAtDecision nameEq predicate actor newStamp live inserted previous
  selected stamp (No different) observed found =
    previous selected stamp
      (trans (sym (lookupPutCurrentOther nameEq selected actor different newStamp live)) found)

||| Observe the ACTUAL library decider, then preserve a pointwise stamp
||| predicate through the same native generation-environment put.
export
0 o20LivePredicatePut :
  {name : Type} -> (nameEq : DecEq name) ->
  (predicate : RegistrationGeneration name -> Type) ->
  (actor : name) -> (newStamp : RegistrationGeneration name) ->
  (live : GenerationEnvironment name) ->
  predicate newStamp ->
  ((selected : name) -> (stamp : RegistrationGeneration name) ->
    (lookupCurrentGeneration @{nameEq} selected live = Just stamp) -> predicate stamp) ->
  (selected : name) -> (stamp : RegistrationGeneration name) ->
  (lookupCurrentGeneration @{nameEq} selected (putCurrentGeneration @{nameEq} actor newStamp live) = Just stamp) ->
  predicate stamp
o20LivePredicatePut nameEq predicate actor newStamp live inserted previous selected stamp found =
  o20LivePredicatePutAtDecision nameEq predicate actor newStamp live inserted previous
    selected stamp (decEq @{nameEq} selected actor) Refl found
