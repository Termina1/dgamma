module DGamma.CP5O19ExpandedAssemblySpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5O19SurfaceSpike
import DGamma.CP5O19ReplayObservationSpike
import DGamma.CP5O19OrdinalPlanSpike
import DGamma.CP5O19CartesianNumericSpike
import DGamma.CP5ConfluenceRankObservationSpike
import DGamma.CP5O19CartesianCursorSpike
import DGamma.CP5O19CartesianColumnsSpike
import DGamma.CP5O19WholeBlockSpike
import DGamma.CP5O19ReachedBlocksSpike
import DGamma.CP5O19ReachedDecompositionSpike
import DGamma.CP5O19SameChainAssemblySpike
import DGamma.CP5O19OperationalAssemblySpike
import Data.List
import Data.List.Elem
import Decidable.Equality

%default total
%unbound_implicits off

||| CONDITIONAL on the R207 packaged expandedRun (not a Legacy body).
||| Its actual finite derivation gives native origins; source decomposition
||| and the exact actor transposition give coverage. This does not produce
||| expandedRun and does not inhabit the universal Operational obligation.
export
0 o19ExpandedTargetLifecycleCoverage :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal : SystemState name key value world error} -> (source : Transitions initial sourceFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
  (expanded : O19WholeBlockUnconditionalObligation name key world error value nameEq keyEq protocol swap source blocks premises safety unique) ->
  LifecycleActorsCovered targetOrder (cursorTrace (columnCursor (expandedRun expanded)))
o19ExpandedTargetLifecycleCoverage nameEq keyEq protocol swap source blocks premises safety unique expanded =
  o19LifecycleCoverageFromOrigins source (cursorTrace (columnCursor (expandedRun expanded)))
    (replayActionOrigin (finiteDerivationOccurrenceCorrespondence (cursorDerivation (columnCursor (expandedRun expanded)))))
    (o19SwapActorMembership swap) (decomposedLifecycleCoverage blocks)

||| Inhabit the R207 erased decomposition TYPE FAMILY for the SAME supplied
||| WholeBlock and Reached packages. The two selector/order fields are used
||| literally; disjointness and lifecycle coverage are DERIVED here. Neither
||| package is produced, so this is a conditional producer, not closure of O19.
export
0 o19ExpandedTargetDecomposition :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal : SystemState name key value world error} -> (source : Transitions initial sourceFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
  (expanded : O19WholeBlockUnconditionalObligation name key world error value nameEq keyEq protocol swap source blocks premises safety unique) ->
  (reached : O19ReachedUnconditionalObligation name key world error value nameEq keyEq protocol swap source blocks premises safety unique expanded) ->
  O19ReachedDecompositionUnconditionalObligation nameEq keyEq protocol swap source blocks premises safety unique expanded
o19ExpandedTargetDecomposition nameEq keyEq protocol swap source blocks premises safety unique expanded reached =
  MkActorBlockDecomposition
    (o19ActualTargetBlockObligation reached)
    (o19ActualTargetBlocksFollowOrderObligation reached)
    (\early, late, earlyIn, lateIn, ordered =>
      o19OrderedBlockRangesDisjoint (cursorTrace (columnCursor (expandedRun expanded)))
        (o19ActualTargetBlockObligation reached early earlyIn)
        (o19ActualTargetBlockObligation reached late lateIn)
        (o19ActualTargetBlocksFollowOrderObligation reached early late earlyIn lateIn ordered))
    (o19ExpandedTargetLifecycleCoverage nameEq keyEq protocol swap source blocks premises safety unique expanded)

||| The expandedRun's actual derivation, and original final well-formedness,
||| produce its endpoint relation. No Legacy parameter, independent endpoint,
||| or preselected relation is required; existence of expandedRun remains open.
export
0 o19ExpandedTargetEndpoint :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal : SystemState name key value world error} -> (source : Transitions initial sourceFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
  (expanded : O19WholeBlockUnconditionalObligation name key world error value nameEq keyEq protocol swap source blocks premises safety unique) ->
  RelationalReplayEndpoint name key world error value nameEq keyEq sourceFinal
    (cursorFinal (columnCursor (expandedRun expanded)))
o19ExpandedTargetEndpoint nameEq keyEq protocol swap source blocks premises safety unique expanded =
  o19FiniteEndpoint nameEq keyEq (cursorDerivation (columnCursor (expandedRun expanded)))
    (replayFinalWellFormed premises)

||| Project the ENTIRE replay bundle and raw insertion uniqueness from the
||| SAME expandedRun cursor. This conditional adapter introduces no Legacy
||| restriction and no weakened substitute for the original capital.
export
0 o19ExpandedTargetPremises :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal : SystemState name key value world error} -> (source : Transitions initial sourceFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
  (expanded : O19WholeBlockUnconditionalObligation name key world error value nameEq keyEq protocol swap source blocks premises safety unique) ->
  (ReplayInvariantBundle name key world error value protocol nameEq keyEq
      (cursorTrace (columnCursor (expandedRun expanded))),
   UniqueRawNameInsertions name key world error value nameEq keyEq
      (cursorTrace (columnCursor (expandedRun expanded))))
o19ExpandedTargetPremises nameEq keyEq protocol swap source blocks premises safety unique expanded =
  (cursorBundle (columnCursor (expandedRun expanded)), cursorUnique (columnCursor (expandedRun expanded)))
