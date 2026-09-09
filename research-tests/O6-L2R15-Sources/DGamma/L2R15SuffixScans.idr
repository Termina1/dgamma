module DGamma.L2R15SuffixScans

import Builtin
import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import Prelude.EqOrd
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R5RootCatalog
import DGamma.L2R6ForcedScan
import DGamma.L2R13NativeSuffixFrames
import Data.Bool
import Data.List
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Every existing native Root/Retire frame PRODUCES exact dictionary
||| alignment on BOTH suffixes. This discharges alignment for these frames,
||| not for an arbitrary unaligned transition or a general admitted move.
export
0 nativeSuffixAligned : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {oldFirst, oldFinal, newFirst, newFinal : SystemState name key value world error} ->
  {oldTrace : Transitions oldFirst oldFinal} -> {newTrace : Transitions newFirst newFinal} ->
  NativeSuffixFrames nameEq keyEq oldTrace newTrace ->
  (AlignedTransitions name key world error value nameEq keyEq oldTrace,
   AlignedTransitions name key world error value nameEq keyEq newTrace)
nativeSuffixAligned nameEq keyEq SuffixFramesEnd = (AlignedEnd, AlignedEnd)
nativeSuffixAligned nameEq keyEq
  (SuffixFramesRoot {oldRest} {newRest} actor component oldChecked newChecked valid frame later) =
  (AlignedStep (OInsert actor Root component) OInsertTag oldChecked oldRest (fst (nativeSuffixAligned nameEq keyEq later)),
   AlignedStep (OInsert actor Root component) OInsertTag newChecked newRest (snd (nativeSuffixAligned nameEq keyEq later)))
nativeSuffixAligned nameEq keyEq
  (SuffixFramesRetire {oldRest} {newRest} actor tag oldChecked newChecked valid later) =
  (AlignedStep (ORetire actor) tag oldChecked oldRest (fst (nativeSuffixAligned nameEq keyEq later)),
   AlignedStep (ORetire actor) tag newChecked newRest (snd (nativeSuffixAligned nameEq keyEq later)))
