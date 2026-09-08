module DGamma.CP5O19WholeBlockSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5O19ReplayObservationSpike
import DGamma.CP5O19CartesianCursorSpike
import DGamma.CP5O19CartesianColumnsSpike
import DGamma.CP5O19CartesianNumericSpike
import DGamma.CP5O19OrdinalPlanSpike
import DGamma.CP5O19ActualCartesianSpike
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

||| The SAME actual-chain node count, via its own global plan product law.
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
  (finiteAdjacentSwapNodeCount (cursorDerivation (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique))) =
    actorBlockTransitionCount (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)) *
    actorBlockTransitionCount (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))
o19ActualFiniteProductCount nameEq keyEq protocol swap source blocks premises safety unique =
  trans (sym (globalCrossingCount (o19ActualGlobalOriginPlan nameEq keyEq protocol swap source blocks premises safety unique)))
    (o19ActualGlobalOriginProductCount nameEq keyEq protocol swap source blocks premises safety unique)

||| Both selected blocks contain Begin, hence both counts are successors.
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
  O19NonEmptyChain name key world error value protocol nameEq keyEq
    (cursorDerivation (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)))
o19ActualNonEmptyChain nameEq keyEq protocol swap source blocks premises safety unique =
  o19ObserveNonEmptyChain
    (cursorDerivation (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)))
    (\zero => uninhabited
      (trans (sym (o19ActualFiniteProductCount nameEq keyEq protocol swap source blocks premises safety unique)) zero))

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
