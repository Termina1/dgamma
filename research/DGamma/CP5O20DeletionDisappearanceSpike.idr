module DGamma.CP5O20DeletionDisappearanceSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5CurrentGenerationBirthSpike
import DGamma.CP5O20CanonicalMaybeControlSpike
import DGamma.CP5O20StampedOrdinalNecessitySpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Join scans of actual adjacent trace segments. Only the first scan is
||| eliminated; the actual ordinal/live indices are preserved at the cut.
export
0 o20AppendGenerationScans :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} ->
  {first, middle, finalState : SystemState name key value world error} ->
  {ordinal, middleOrdinal, finalOrdinal : Nat} ->
  {live, middleLive, finalLive : GenerationEnvironment name} ->
  {earlier : Transitions first middle} -> {later : Transitions middle finalState} ->
  GenerationTraceScan nameEq ordinal live earlier middleOrdinal middleLive ->
  GenerationTraceScan nameEq middleOrdinal middleLive later finalOrdinal finalLive ->
  GenerationTraceScan nameEq ordinal live (appendTransitions earlier later) finalOrdinal finalLive
o20AppendGenerationScans GenerationTraceScanEnd right = right
o20AppendGenerationScans (GenerationTraceScanStep step rest left) right =
  GenerationTraceScanStep step _ (o20AppendGenerationScans left right)

||| The actual deletion construction owns a whole ORIGINAL generation scan
||| by joining its before/episode/after scans at this episode's decomposition.
export
0 o20DeletionOriginalScan :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, finalState : SystemState name key value world error} ->
  {original : Transitions initial finalState} ->
  (candidate : DeletableClosingEpisode name key world error value nameEq keyEq original) ->
  (result : DeletionResult name key world error value nameEq keyEq original
    (selectedActor candidate) (selectedEpisode candidate) (selectedRegistrations candidate)
    (selectedStartOrdinal candidate) (selectedStartLive candidate)) ->
  GenerationTraceScan nameEq Z [] original (originalFinalOrdinal result) (originalFinalLive result)
o20DeletionOriginalScan {nameEq} candidate result =
  replace {p = \trace => GenerationTraceScan nameEq Z [] trace (originalFinalOrdinal result) (originalFinalLive result)}
    (locatedDecomposition (selectedEpisode candidate))
    (o20AppendGenerationScans (beforeGenerationScan result)
      (o20AppendGenerationScans (episodeGenerationScan result) (afterGenerationScan result)))
