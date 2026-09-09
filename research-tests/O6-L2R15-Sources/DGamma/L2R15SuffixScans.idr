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

||| One observed native head yields its ACTUAL tail and exact catalog
||| equation at arbitrary offsets. Eliminating the trail authenticates the
||| forced transition index; native release guards need separate decoding.
export
0 nativeHeadScanEquations : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq} action first = Just (tag, middle)) ->
  (rest : Transitions middle finalState) ->
  (trail : AvailabilityTrace name key world error value
    (MoreTransitions (Fired {before = first} {afterState = middle} nameEq keyEq action tag checked) rest)) ->
  (later : AvailabilityTrace name key world error value rest **
    ((offset : Nat) -> scanRootCatalog offset trail =
       rootCatalogStep offset action (scanRootCatalog (S offset) later)))
nativeHeadScanEquations nameEq keyEq _ _ _ _
  (AvailabilityStep source (Fired _ _ action tag checked) rest later) =
  (later ** (\offset => Refl))

||| Arbitrary-length native suffix CATALOG transport from actual frames.
||| Every root contributes the same physical ordinal/name/component; Retire
||| contributes no birth. No supplied catalog equality or global frame is used.
export
0 nativeSuffixCatalog : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {oldFirst, oldFinal, newFirst, newFinal : SystemState name key value world error} ->
  {oldTrace : Transitions oldFirst oldFinal} -> {newTrace : Transitions newFirst newFinal} ->
  NativeSuffixFrames nameEq keyEq oldTrace newTrace ->
  (oldTrail : AvailabilityTrace name key world error value oldTrace) ->
  (newTrail : AvailabilityTrace name key world error value newTrace) -> (offset : Nat) ->
  scanRootCatalog offset oldTrail = scanRootCatalog offset newTrail
nativeSuffixCatalog nameEq keyEq SuffixFramesEnd (AvailabilityEnd _) (AvailabilityEnd _) offset = Refl
nativeSuffixCatalog nameEq keyEq (SuffixFramesRoot {oldRest} {newRest} actor component oldChecked newChecked valid frame later) oldTrail newTrail offset =
  trans (snd (nativeHeadScanEquations nameEq keyEq (OInsert actor Root component) OInsertTag oldChecked oldRest oldTrail) offset)
    (trans (cong (rootCatalogStep offset (OInsert actor Root component))
      (nativeSuffixCatalog nameEq keyEq later (fst (nativeHeadScanEquations nameEq keyEq (OInsert actor Root component) OInsertTag oldChecked oldRest oldTrail)) (fst (nativeHeadScanEquations nameEq keyEq (OInsert actor Root component) OInsertTag newChecked newRest newTrail)) (S offset)))
      (sym (snd (nativeHeadScanEquations nameEq keyEq (OInsert actor Root component) OInsertTag newChecked newRest newTrail) offset)))
nativeSuffixCatalog nameEq keyEq (SuffixFramesRetire {oldRest} {newRest} actor tag oldChecked newChecked valid later) oldTrail newTrail offset =
  trans (snd (nativeHeadScanEquations nameEq keyEq (ORetire actor) tag oldChecked oldRest oldTrail) offset)
    (trans (cong (rootCatalogStep offset (ORetire actor))
      (nativeSuffixCatalog nameEq keyEq later (fst (nativeHeadScanEquations nameEq keyEq (ORetire actor) tag oldChecked oldRest oldTrail)) (fst (nativeHeadScanEquations nameEq keyEq (ORetire actor) tag newChecked newRest newTrail)) (S offset)))
      (sym (snd (nativeHeadScanEquations nameEq keyEq (ORetire actor) tag newChecked newRest newTrail) offset)))

||| Native no-release head reduction, without reconstructing an if-family.
||| The authentic classifier equation is rewritten before its guard closes.
||| Root and Retire supply False directly; no Remove equation is attempted.
export
0 nativeNonReleaseTail : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (0 checked : checkedApplyAction @{nameEq} @{keyEq} action first = Just (tag, middle)) ->
  (rest : Transitions middle finalState) ->
  (trail : AvailabilityTrace name key world error value
    (MoreTransitions (Fired {before = first} {afterState = middle} nameEq keyEq action tag checked) rest)) ->
  (component : Component key value world error) -> (offset, cut : Nat) ->
  (0 inactive : ownChildReleaseStep nameEq keyEq component first action = False) ->
  (later : AvailabilityTrace name key world error value rest **
    scanReleaseOrdinals nameEq keyEq component offset cut trail =
      scanReleaseOrdinals nameEq keyEq component (S offset) cut later)
nativeNonReleaseTail nameEq keyEq _ _ _ _
  (AvailabilityStep source (Fired _ _ action tag checked) rest later) component offset cut inactive =
  (later ** (rewrite inactive in rewrite andFalseFalse (offset < cut) in Refl))

||| Native Root/Retire suffixes preserve the exact release scan for EVERY
||| component and physical offset/cut. These suffixes contain no Remove;
||| this is not a crossing-release identity or shifted-ordinal theorem.
export
0 nativeSuffixReleases : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {oldFirst, oldFinal, newFirst, newFinal : SystemState name key value world error} ->
  {oldTrace : Transitions oldFirst oldFinal} -> {newTrace : Transitions newFirst newFinal} ->
  NativeSuffixFrames nameEq keyEq oldTrace newTrace ->
  (oldTrail : AvailabilityTrace name key world error value oldTrace) ->
  (newTrail : AvailabilityTrace name key world error value newTrace) ->
  (component : Component key value world error) -> (offset, cut : Nat) ->
  scanReleaseOrdinals nameEq keyEq component offset cut oldTrail =
    scanReleaseOrdinals nameEq keyEq component offset cut newTrail
nativeSuffixReleases nameEq keyEq SuffixFramesEnd (AvailabilityEnd _) (AvailabilityEnd _) component offset cut = Refl
nativeSuffixReleases nameEq keyEq (SuffixFramesRoot {oldRest} {newRest} actor inserted oldChecked newChecked valid frame later) oldTrail newTrail component offset cut =
  trans (snd (nativeNonReleaseTail nameEq keyEq (OInsert actor Root inserted) OInsertTag oldChecked oldRest oldTrail component offset cut Refl))
    (trans (nativeSuffixReleases nameEq keyEq later (fst (nativeNonReleaseTail nameEq keyEq (OInsert actor Root inserted) OInsertTag oldChecked oldRest oldTrail component offset cut Refl)) (fst (nativeNonReleaseTail nameEq keyEq (OInsert actor Root inserted) OInsertTag newChecked newRest newTrail component offset cut Refl)) component (S offset) cut)
      (sym (snd (nativeNonReleaseTail nameEq keyEq (OInsert actor Root inserted) OInsertTag newChecked newRest newTrail component offset cut Refl))))
nativeSuffixReleases nameEq keyEq (SuffixFramesRetire {oldRest} {newRest} actor tag oldChecked newChecked valid later) oldTrail newTrail component offset cut =
  trans (snd (nativeNonReleaseTail nameEq keyEq (ORetire actor) tag oldChecked oldRest oldTrail component offset cut Refl))
    (trans (nativeSuffixReleases nameEq keyEq later (fst (nativeNonReleaseTail nameEq keyEq (ORetire actor) tag oldChecked oldRest oldTrail component offset cut Refl)) (fst (nativeNonReleaseTail nameEq keyEq (ORetire actor) tag newChecked newRest newTrail component offset cut Refl)) component (S offset) cut)
      (sym (snd (nativeNonReleaseTail nameEq keyEq (ORetire actor) tag newChecked newRest newTrail component offset cut Refl))))
