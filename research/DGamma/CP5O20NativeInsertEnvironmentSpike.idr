module DGamma.CP5O20NativeInsertEnvironmentSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionGenerationScan
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5GeneratedOrchestrationMatched
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5O20StampedHistoryFoldSpike
import DGamma.CP5O20StampedOrdinalNecessitySpike
import DGamma.CP5O20CanonicalOrdinalAttachmentSpike
import DGamma.CP5O20PhysicalInsertPositionSpike
import DGamma.CP5O20PhysicalInsertStageSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Every native scan's final ordinal is its starting ordinal plus the
||| physical trace count, including the original edges absent after filtering.
export
0 o20NativeScanCount :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} ->
  {first, finalState : SystemState name key value world error} ->
  {trace : Transitions first finalState} ->
  {ordinal, finalOrdinal : Nat} -> {live, finalLive : GenerationEnvironment name} ->
  GenerationTraceScan nameEq ordinal live trace finalOrdinal finalLive ->
  (finalOrdinal = ordinal + transitionCount trace)
o20NativeScanCount {ordinal} GenerationTraceScanEnd = sym (plusZeroRightNeutral ordinal)
o20NativeScanCount {ordinal} (GenerationTraceScanStep step rest later) =
  trans (o20NativeScanCount later) (plusSuccRightSucc ordinal (transitionCount rest))

||| Scan the actual finite preceding trace from the empty origin. The live
||| environment is COMPUTED, not a caller parameter; its ordinal is the same
||| physical count used by LocatedGeneratedRegistration.
export
0 o20NativePrefixScan :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) ->
  GenerationTraceScan nameEq Z [] trace (transitionCount trace)
    (o20ScannedFinalLive nameEq Z [] trace)
o20NativePrefixScan {name} {key} {world} {error} {value} nameEq trace =
  replace {p = \live => GenerationTraceScan nameEq Z [] trace (transitionCount trace) live}
    (o20GenerationScanFinalLiveExact (generationScan (scanGenerations nameEq Z [] trace)))
    (replace {p = \ordinal => GenerationTraceScan nameEq Z [] trace ordinal
      (scanFinalLive (scanGenerations nameEq Z [] trace))}
      (o20NativeScanCount (generationScan (scanGenerations nameEq Z [] trace)))
      (generationScan (scanGenerations nameEq Z [] trace)))
