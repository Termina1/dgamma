module DGamma.CP4DeletionPlanBoundary

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionGenerationUnique
import DGamma.CP4DeletionInactiveInvariant
import DGamma.CP4DeletionPlanBuilder
import DGamma.CP4DeletionPlanSuccess
import Data.List.Elem
import Decidable.Equality

%default total

||| The one structural residue still needed beside proved inactivity: no current
||| exact R generation has a child at the boundary. Generation membership, not
||| raw-name membership, prevents a later reissue from inheriting this duty.
public export
CurrentRegisteredChildless :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) ->
  List (RegistrationGeneration name) -> GenerationEnvironment name ->
  SystemState name key value world error -> Type
CurrentRegisteredChildless name key world error value nameEq registered live
  state =
    (selected : name) -> (generation : RegistrationGeneration name) ->
    Elem (selected, generation) live -> Elem generation registered ->
    hasChild @{nameEq} selected (registry state) = False

||| Combine the proved lookup-indexed Inactive invariant with childlessness into
||| the exact plan-success boundary record.
public export
0 inactiveAndChildlessGiveLeaves :
  (nameEq : DecEq name) ->
  (registered : List (RegistrationGeneration name)) ->
  (live : GenerationEnvironment name) ->
  GenerationEnvironmentNamesUnique live ->
  (state : SystemState name key value world error) ->
  CurrentRegisteredInactiveFibers name key world error value nameEq registered
    live state ->
  CurrentRegisteredChildless name key world error value nameEq registered live
    state ->
  CurrentRegisteredInactiveLeaves name key world error value nameEq registered
    live (registry state)
inactiveAndChildlessGiveLeaves nameEq registered live unique state inactive
  childless selected generation present member =
    let current = lookupCurrentGenerationFromElem nameEq live unique present
    in case inactive selected generation member current of
      MkInactiveFiberAt component parent retiredFlag table outcome found =>
        MkInactiveLeafAt component parent retiredFlag table outcome found
          (childless selected generation present member)

||| Exact plan derivation at a reached boundary. All generation mechanics and
||| Inactive control facts are discharged; only `CurrentRegisteredChildless`
||| remains as a structural registration-provenance theorem.
public export
0 reachedBoundaryGivesDeletionPlan :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (registered : List (RegistrationGeneration name)) ->
  (trace : Transitions initial finalState) ->
  (finalOrdinal : Nat) -> (finalLive : GenerationEnvironment name) ->
  (scan : GenerationTraceScan nameEq 0 [] trace finalOrdinal finalLive) ->
  AlignedTransitions name key world error value nameEq keyEq trace ->
  NoRegisteredEpisode nameEq registered 0 [] trace ->
  CurrentRegisteredChildless name key world error value nameEq registered
    finalLive finalState ->
  CurrentRegisteredPlanResult name key world error value nameEq registered
    finalLive (registry finalState)
reachedBoundaryGivesDeletionPlan nameEq keyEq registered trace finalOrdinal
  finalLive scan aligned noEpisodes childless =
    let 0 unique = generationTraceScanPreservesUnique nameEq scan UniqueNil
        0 inactive = reachedCurrentRegisteredInactive nameEq keyEq registered trace
          finalOrdinal finalLive scan aligned noEpisodes
        0 leaves = inactiveAndChildlessGiveLeaves nameEq registered finalLive
          unique finalState inactive childless
    in currentRegisteredLeavesGivePlan nameEq registered finalLive unique
      (registry finalState) leaves
