module DGamma.CP5O19WholeBlockSpike

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
import DGamma.CP5O19OriginalBlockClassSpike
import DGamma.CP5O19GridCertificationSpike
import Data.List
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Observe a nonempty view of an EXISTING finite chain. The forgetful
||| equation preserves its actual nodes, not just length or action labels.
public export
record O19NonEmptyChain
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, sourceFinal, targetFinal : SystemState name key value world error}
  {source : Transitions initial sourceFinal} {target : Transitions initial targetFinal}
  (derivation : FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq source target) where
  constructor MkO19NonEmptyChain
  observedNonEmptyChain : NonEmptyFiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq source target
  0 observedChainExact : (nonEmptyToFiniteAdjacentSwapDerivation observedNonEmptyChain = derivation)
  0 observedChainCount : (nonEmptyAdjacentSwapNodeCount observedNonEmptyChain = finiteAdjacentSwapNodeCount derivation)

||| Structural observation of the SAME supplied chain. The zero constructor
||| contradicts its own node-count evidence; the step retains its exact tail.
export
0 o19ObserveNonEmptyChain :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} -> {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, sourceFinal, targetFinal : SystemState name key value world error} ->
  {source : Transitions initial sourceFinal} -> {target : Transitions initial targetFinal} ->
  (derivation : FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq source target) ->
  Not (finiteAdjacentSwapNodeCount derivation = Z) ->
  O19NonEmptyChain name key world error value protocol nameEq keyEq derivation
o19ObserveNonEmptyChain FiniteAdjacentSwapDone nonzero = void (nonzero Refl)
o19ObserveNonEmptyChain (FiniteAdjacentSwapStep source earlier left right later orientation diamond result target rest) nonzero =
  MkO19NonEmptyChain
    (NonEmptyAdjacentSwap source earlier left right later orientation diamond result target rest) Refl Refl

||| R207 legacy-restricted twin: SAME actual-chain count, with both shapes explicit.
export
0 o19ActualFiniteProductCount :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal : SystemState name key value world error} -> (source : Transitions initial sourceFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
  (leftLegacy : LegacyActorOnly (actorLeft swap) (blockBody (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) ->
  (rightLegacy : LegacyActorOnly (actorRight swap) (blockBody (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) ->
  (finiteAdjacentSwapNodeCount (cursorDerivation (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique leftLegacy rightLegacy))) =
    actorBlockTransitionCount (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)) *
    actorBlockTransitionCount (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))
o19ActualFiniteProductCount nameEq keyEq protocol swap source blocks premises safety unique leftLegacy rightLegacy =
  trans (sym (globalCrossingCount (o19ActualGlobalOriginPlan nameEq keyEq protocol swap source blocks premises safety unique leftLegacy rightLegacy)))
    (o19ActualGlobalOriginProductCount nameEq keyEq protocol swap source blocks premises safety unique leftLegacy rightLegacy)

||| R207 legacy-restricted twin: both selected blocks contain Begin.
||| Their SAME-chain product law excludes zero nodes and retains exact replay.
export
0 o19ActualNonEmptyChain :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal : SystemState name key value world error} -> (source : Transitions initial sourceFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
  (leftLegacy : LegacyActorOnly (actorLeft swap) (blockBody (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) ->
  (rightLegacy : LegacyActorOnly (actorRight swap) (blockBody (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) ->
  O19NonEmptyChain name key world error value protocol nameEq keyEq
    (cursorDerivation (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique leftLegacy rightLegacy)))
o19ActualNonEmptyChain nameEq keyEq protocol swap source blocks premises safety unique leftLegacy rightLegacy =
  o19ObserveNonEmptyChain
    (cursorDerivation (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique leftLegacy rightLegacy)))
    (\zero => uninhabited
      (trans (sym (o19ActualFiniteProductCount nameEq keyEq protocol swap source blocks premises safety unique leftLegacy rightLegacy)) zero))

||| Whole-block certificate plus its SAME-chain authentication, constructed
||| together so later assembly never substitutes a separately replayed chain.
public export
record O19WholeBlockResult
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {sourceOrder, targetOrder : List name}
  (swap : AdjacentActorOrderSwap name sourceOrder targetOrder)
  {initial, sourceFinal, targetFinal : SystemState name key value world error}
  (source : Transitions initial sourceFinal)
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source)
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source)
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises)
  (target : Transitions initial targetFinal)
  (derivation : FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq source target) where
  constructor MkO19WholeBlockResult
  certifiedWholeBlock : WholeBlockSwapDerivation name key world error value protocol nameEq keyEq swap source blocks premises safety target
  0 certifiedWholeChainExact : (wholeBlockFiniteDerivation certifiedWholeBlock = derivation)

||| Internal observation boundary: assemble every WholeBlockSwapDerivation
||| field from the observed SAME chain, its own local plan/count and the now
||| proved numeric grid. The next entry discharges every internal premise.
export
0 o19WholeFromObservedChain :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal, targetFinal : SystemState name key value world error} -> (source : Transitions initial sourceFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  (target : Transitions initial targetFinal) ->
  (derivation : FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq source target) ->
  (observed : O19NonEmptyChain name key world error value protocol nameEq keyEq derivation) ->
  (finiteAdjacentSwapNodeCount derivation =
    actorBlockTransitionCount (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)) *
    actorBlockTransitionCount (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety))) ->
  BlockCrossingOriginPlan name key world error value protocol nameEq keyEq source
    (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))
    (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety))
    (identityActionRegistrationReplayCorrespondence source) derivation
    (o19GridPairs Z Z (actorBlockTransitionCount (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))
      (actorBlockTransitionCount (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) ->
  O19WholeBlockResult name key world error value protocol nameEq keyEq swap source blocks premises safety target derivation
o19WholeFromObservedChain nameEq keyEq protocol swap source blocks premises safety target derivation observed count plan =
  MkO19WholeBlockResult
    (MkWholeBlockSwapDerivation (observedNonEmptyChain observed)
      (o19GridPairs Z Z (actorBlockTransitionCount (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))
        (actorBlockTransitionCount (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety))))
      (replace {p = \chain => BlockCrossingOriginPlan name key world error value protocol nameEq keyEq source
          (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))
          (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety))
          (identityActionRegistrationReplayCorrespondence source) chain
          (o19GridPairs Z Z (actorBlockTransitionCount (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))
            (actorBlockTransitionCount (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety))))}
        (sym (observedChainExact observed)) plan)
      (gridEveryPair (o19CertifyGrid
        (actorBlockTransitionCount (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))
        (actorBlockTransitionCount (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))))
      (gridEveryMember (o19CertifyGrid
        (actorBlockTransitionCount (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))
        (actorBlockTransitionCount (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))))
      (gridPairsUnique (o19CertifyGrid
        (actorBlockTransitionCount (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))
        (actorBlockTransitionCount (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))))
      (trans (observedChainCount observed) count))
    (observedChainExact observed)

||| WholeBlockSwapDerivation on the SAME actual B3/B13/F14 chain, from O19
||| inputs only. All internal count, nonempty, local-plan and grid obligations
||| are discharged. This quantity-0 witness is not yet the operational body:
||| reached installed blocks and final same-chain assembly remain separate.
export
0 o19ActualWholeBlock :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal : SystemState name key value world error} -> (source : Transitions initial sourceFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
  (leftLegacy : LegacyActorOnly (actorLeft swap) (blockBody (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) ->
  (rightLegacy : LegacyActorOnly (actorRight swap) (blockBody (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) ->
  O19WholeBlockResult name key world error value protocol nameEq keyEq swap source blocks premises safety
    (cursorTrace (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique leftLegacy rightLegacy)))
    (cursorDerivation (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique leftLegacy rightLegacy)))
o19ActualWholeBlock nameEq keyEq protocol swap source blocks premises safety unique leftLegacy rightLegacy =
  o19WholeFromObservedChain nameEq keyEq protocol swap source blocks premises safety
    (cursorTrace (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique leftLegacy rightLegacy)))
    (cursorDerivation (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique leftLegacy rightLegacy)))
    (o19ActualNonEmptyChain nameEq keyEq protocol swap source blocks premises safety unique leftLegacy rightLegacy)
    (o19ActualFiniteProductCount nameEq keyEq protocol swap source blocks premises safety unique leftLegacy rightLegacy)
    (o19ActualLocalOriginPlan nameEq keyEq protocol swap source blocks premises safety unique leftLegacy rightLegacy)

||| OPEN: needs the expanded unconditional producer / the reached separation
||| theorem. TYPE ONLY, with NO inhabitant. These are the three ORIGINAL
||| unconditional WholeBlock conclusions jointly indexed by the SAME required
||| expanded run, rather than invoking a nonexistent unconditional function.
||| Exact original value types are in O6-R207-CROSSTRACE-NEEDS.json.
public export
record O19WholeBlockUnconditionalObligation
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (protocol : RegistrationProtocol key value world error)
  {sourceOrder, targetOrder : List name} (swap : AdjacentActorOrderSwap name sourceOrder targetOrder)
  {initial, sourceFinal : SystemState name key value world error} (source : Transitions initial sourceFinal)
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source)
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source)
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises)
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq source) where
  constructor MkO19WholeBlockUnconditionalObligation
  0 expandedRun : O19ColumnRun name key world error value protocol nameEq keyEq source
    (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))
    (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))))
    (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety))))
    (o19ActionWord (traceAfterBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety))))
  0 o19ActualFiniteProductCountObligation :
    finiteAdjacentSwapNodeCount (cursorDerivation (columnCursor expandedRun)) =
      actorBlockTransitionCount (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)) *
      actorBlockTransitionCount (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety))
  0 o19ActualNonEmptyChainObligation :
    O19NonEmptyChain name key world error value protocol nameEq keyEq (cursorDerivation (columnCursor expandedRun))
  0 o19ActualWholeBlockObligation :
    O19WholeBlockResult name key world error value protocol nameEq keyEq swap source blocks premises safety
      (cursorTrace (columnCursor expandedRun)) (cursorDerivation (columnCursor expandedRun))
