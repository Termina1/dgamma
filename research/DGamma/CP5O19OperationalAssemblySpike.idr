module DGamma.CP5O19OperationalAssemblySpike

import DGamma.CP5O19SameChainAssemblySpike
import DGamma.CP5O19ReachedDecompositionSpike
import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5O19SurfaceSpike
import DGamma.CP5O19ReplayObservationSpike
import DGamma.CP5O19CartesianCursorSpike
import DGamma.CP5O19CartesianColumnsSpike
import DGamma.CP5O19CartesianNumericSpike
import DGamma.CP5O19OrdinalPlanSpike
import DGamma.CP5O19ActualCartesianSpike
import DGamma.CP5O19GridCertificationSpike
import DGamma.CP5O19WholeBlockSpike
import DGamma.CP5O19OriginalBlockClassSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5GeneratedOrchestrationMatched
import Data.List
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Genuine external orchestration correspondence along the actual finite
||| derivation. Every node contributes its OWN complete filtered relation,
||| including actual transition occurrences; this is not a label-word map.
export
0 o19FiniteSameExternalInputs :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> {keyEq : DecEq key} ->
  {protocol : RegistrationProtocol key value world error} ->
  {initial, sourceFinal, targetFinal : SystemState name key value world error} ->
  {source : Transitions initial sourceFinal} -> {target : Transitions initial targetFinal} ->
  FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq source target ->
  SameExternalOrchestration nameEq source target
o19FiniteSameExternalInputs {source} nameEq FiniteAdjacentSwapDone =
  sameExternalOrchestrationReflexiveSpike nameEq source
o19FiniteSameExternalInputs nameEq
  (FiniteAdjacentSwapStep source earlier left right later orientation diamond result target rest) =
    sameExternalOrchestrationTransitiveSpike nameEq (swappedSameExternalInputs result)
      (o19FiniteSameExternalInputs nameEq rest)

||| The ACTUAL reached endpoint on the SAME cursor derivation, using the
||| full original bundle's final well-formedness at D1's base boundary.
export
0 o19ActualTargetEndpoint :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal : SystemState name key value world error} -> (source : Transitions initial sourceFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
  (legacyBlocks : (selected : name) -> (member : Elem selected sourceOrder) ->
    LegacyActorOnly selected (blockBody (decomposedBlock blocks selected member))) ->
  RelationalReplayEndpoint name key world error value nameEq keyEq sourceFinal
    (cursorFinal (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique (legacyBlocks (actorLeft swap) (safetyLeftInOrder safety)) (legacyBlocks (actorRight swap) (safetyRightInOrder safety)))))
o19ActualTargetEndpoint nameEq keyEq protocol swap source blocks premises safety unique legacyBlocks =
  o19FiniteEndpoint nameEq keyEq
    (cursorDerivation (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique (legacyBlocks (actorLeft swap) (safetyLeftInOrder safety)) (legacyBlocks (actorRight swap) (safetyRightInOrder safety)))))
    (replayFinalWellFormed premises)

||| Retain the ENTIRE reached invariant bundle together with raw-insertion
||| uniqueness from the SAME cursor, never reconstructing a weakened bundle.
||| GeneratedOrchestrationMatched remains at its original cross-trace inputs;
||| the sanctioned O19 surface contains no such field (R189 supervisor ruling).
export
0 o19ActualTargetPremises :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal : SystemState name key value world error} -> (source : Transitions initial sourceFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
  (legacyBlocks : (selected : name) -> (member : Elem selected sourceOrder) ->
    LegacyActorOnly selected (blockBody (decomposedBlock blocks selected member))) ->
  (ReplayInvariantBundle name key world error value protocol nameEq keyEq
      (cursorTrace (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique (legacyBlocks (actorLeft swap) (safetyLeftInOrder safety)) (legacyBlocks (actorRight swap) (safetyRightInOrder safety))))),
   UniqueRawNameInsertions name key world error value nameEq keyEq
      (cursorTrace (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique (legacyBlocks (actorLeft swap) (safetyLeftInOrder safety)) (legacyBlocks (actorRight swap) (safetyRightInOrder safety))))))
o19ActualTargetPremises nameEq keyEq protocol swap source blocks premises safety unique legacyBlocks =
  (cursorBundle (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique (legacyBlocks (actorLeft swap) (safetyLeftInOrder safety)) (legacyBlocks (actorRight swap) (safetyRightInOrder safety)))),
   cursorUnique (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique (legacyBlocks (actorLeft swap) (safetyLeftInOrder safety)) (legacyBlocks (actorRight swap) (safetyRightInOrder safety)))))

||| Full genuine external-input relation for the actual Cartesian trace,
||| folded from the very chain that owns its whole-block derivation.
export
0 o19ActualTargetSameExternalInputs :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal : SystemState name key value world error} -> (source : Transitions initial sourceFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
  (legacyBlocks : (selected : name) -> (member : Elem selected sourceOrder) ->
    LegacyActorOnly selected (blockBody (decomposedBlock blocks selected member))) ->
  SameExternalOrchestration nameEq source
    (cursorTrace (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique (legacyBlocks (actorLeft swap) (safetyLeftInOrder safety)) (legacyBlocks (actorRight swap) (safetyRightInOrder safety)))))
o19ActualTargetSameExternalInputs nameEq keyEq protocol swap source blocks premises safety unique legacyBlocks =
  o19FiniteSameExternalInputs nameEq
    (cursorDerivation (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique (legacyBlocks (actorLeft swap) (safetyLeftInOrder safety)) (legacyBlocks (actorRight swap) (safetyRightInOrder safety)))))

||| LEGACY-CONDITIONAL same-chain operational whole-block swap. All fields belong to
||| the SAME actual Cartesian cursor: whole derivation, full reached block
||| decomposition, endpoint, full invariant bundle, and external inputs.
||| Every source decomposition body must be LegacyActorOnly. This is NOT an
||| unconditional expanded producer, and cannot satisfy frozen CrossTrace.
||| The source/raw uniqueness is consumed by the actual cursor derivation;
||| B4 retains reached uniqueness as accompanying erased capital.
export
0 o19ActualOperationalBlockSwap :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal : SystemState name key value world error} -> (source : Transitions initial sourceFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
  (legacyBlocks : (selected : name) -> (member : Elem selected sourceOrder) ->
    LegacyActorOnly selected (blockBody (decomposedBlock blocks selected member))) ->
  OperationalAdjacentBlockSwap name key world error value protocol nameEq keyEq
    swap source blocks premises safety
o19ActualOperationalBlockSwap nameEq keyEq protocol swap source blocks premises safety unique legacyBlocks =
  MkOperationalAdjacentBlockSwap
    (cursorFinal (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique (legacyBlocks (actorLeft swap) (safetyLeftInOrder safety)) (legacyBlocks (actorRight swap) (safetyRightInOrder safety)))))
    (cursorTrace (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique (legacyBlocks (actorLeft swap) (safetyLeftInOrder safety)) (legacyBlocks (actorRight swap) (safetyRightInOrder safety)))))
    (certifiedWholeBlock (o19ActualWholeBlock nameEq keyEq protocol swap source blocks premises safety unique (legacyBlocks (actorLeft swap) (safetyLeftInOrder safety)) (legacyBlocks (actorRight swap) (safetyRightInOrder safety))))
    (o19ActualTargetDecomposition nameEq keyEq protocol swap source blocks premises safety unique legacyBlocks)
    (o19ActualTargetEndpoint nameEq keyEq protocol swap source blocks premises safety unique legacyBlocks)
    (fst (o19ActualTargetPremises nameEq keyEq protocol swap source blocks premises safety unique legacyBlocks))
    (o19ActualTargetSameExternalInputs nameEq keyEq protocol swap source blocks premises safety unique legacyBlocks)

||| OPEN R207: the EXACT original unconditional producer type. This is
||| TYPE ONLY: no value of this type, implicit axiom, or hole is supplied.
||| Frozen CrossTrace requires an inhabitant; the legacy function above does
||| not provide one. Expanded root-order and metadata transport remain open.
public export
0 O19OperationalUnconditionalObligation : Type
O19OperationalUnconditionalObligation =
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal : SystemState name key value world error} -> (source : Transitions initial sourceFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
  OperationalAdjacentBlockSwap name key world error value protocol nameEq keyEq
    swap source blocks premises safety
