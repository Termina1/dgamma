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
