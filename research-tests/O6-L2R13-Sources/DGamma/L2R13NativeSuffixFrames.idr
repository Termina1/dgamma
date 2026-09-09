module DGamma.L2R13NativeSuffixFrames

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.L2R5Extensional
import DGamma.L2R5ExtensionalRetire
import DGamma.L2R13InsertExtensional
import Data.List
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Per-edge native Root/Retire suffix hypotheses at EXPLICIT dictionaries.
||| There is NO endpoint-equivalence field and no evaluator replay oracle.
||| Root edges retain their actual finite provision-scan frame; both checked
||| edges authenticate the desired native endpoint selected by determinism.
public export
data NativeSuffixFrames :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {oldFirst, oldFinal, newFirst, newFinal : SystemState name key value world error} ->
  Transitions oldFirst oldFinal -> Transitions newFirst newFinal -> Type where
  SuffixFramesEnd : {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {keyEq : DecEq key} ->
    {oldState, newState : SystemState name key value world error} ->
    NativeSuffixFrames nameEq keyEq
      (the (Transitions oldState oldState) NoTransitions) (the (Transitions newState newState) NoTransitions)
  SuffixFramesRoot : {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {keyEq : DecEq key} ->
    {oldBefore, oldAfter, oldEnd, newBefore, newAfter, newEnd : SystemState name key value world error} ->
    {oldRest : Transitions oldAfter oldEnd} -> {newRest : Transitions newAfter newEnd} ->
    (actor : name) -> (component : Component key value world error) ->
    (0 oldChecked : checkedApplyAction @{nameEq} @{keyEq} (OInsert actor Root component) oldBefore = Just (OInsertTag, oldAfter)) ->
    (0 newChecked : checkedApplyAction @{nameEq} @{keyEq} (OInsert actor Root component) newBefore = Just (OInsertTag, newAfter)) ->
    (0 valid : registryWellFormed @{nameEq} @{keyEq} newBefore = True) ->
    (0 frame : provisionsDisjointFrom {name} {key} {world} {error} {value} @{keyEq}
      (componentProvisions component) (bindings (registry newBefore)) =
      provisionsDisjointFrom {name} {key} {world} {error} {value} @{keyEq}
        (componentProvisions component) (bindings (registry oldBefore))) ->
    (0 later : NativeSuffixFrames nameEq keyEq oldRest newRest) ->
    NativeSuffixFrames nameEq keyEq
      (MoreTransitions (Fired {before = oldBefore} {afterState = oldAfter} nameEq keyEq (OInsert actor Root component) OInsertTag oldChecked) oldRest)
      (MoreTransitions (Fired {before = newBefore} {afterState = newAfter} nameEq keyEq (OInsert actor Root component) OInsertTag newChecked) newRest)
  SuffixFramesRetire : {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {keyEq : DecEq key} ->
    {oldBefore, oldAfter, oldEnd, newBefore, newAfter, newEnd : SystemState name key value world error} ->
    {oldRest : Transitions oldAfter oldEnd} -> {newRest : Transitions newAfter newEnd} ->
    (actor : name) -> (tag : RuleTag) ->
    (0 oldChecked : checkedApplyAction @{nameEq} @{keyEq} (ORetire actor) oldBefore = Just (tag, oldAfter)) ->
    (0 newChecked : checkedApplyAction @{nameEq} @{keyEq} (ORetire actor) newBefore = Just (tag, newAfter)) ->
    (0 valid : registryWellFormed @{nameEq} @{keyEq} newBefore = True) ->
    (0 later : NativeSuffixFrames nameEq keyEq oldRest newRest) ->
    NativeSuffixFrames nameEq keyEq
      (MoreTransitions (Fired {before = oldBefore} {afterState = oldAfter} nameEq keyEq (ORetire actor) tag oldChecked) oldRest)
      (MoreTransitions (Fired {before = newBefore} {afterState = newAfter} nameEq keyEq (ORetire actor) tag newChecked) newRest)

||| Native root frame endpoint: B7 produces the successor; the given actual
||| right edge identifies that successor by checked determinism.
export
0 nativeRootFrameEndpoint : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (component : Component key value world error) ->
  (oldBefore, oldAfter, newBefore, newAfter : SystemState name key value world error) ->
  (0 oldChecked : checkedApplyAction @{nameEq} @{keyEq} (OInsert actor Root component) oldBefore = Just (OInsertTag, oldAfter)) ->
  (0 newChecked : checkedApplyAction @{nameEq} @{keyEq} (OInsert actor Root component) newBefore = Just (OInsertTag, newAfter)) ->
  (0 valid : registryWellFormed @{nameEq} @{keyEq} newBefore = True) ->
  (0 frame : provisionsDisjointFrom {name} {key} {world} {error} {value} @{keyEq}
    (componentProvisions component) (bindings (registry newBefore)) =
    provisionsDisjointFrom {name} {key} {world} {error} {value} @{keyEq}
      (componentProvisions component) (bindings (registry oldBefore))) ->
  (0 same : RegistryExtensional name key world error value nameEq oldBefore newBefore) ->
  RegistryExtensional name key world error value nameEq oldAfter newAfter
nativeRootFrameEndpoint {name} {key} {world} {error} {value}
  nameEq keyEq actor component oldBefore oldAfter newBefore newAfter oldChecked newChecked valid frame same =
  replace {p = \next => RegistryExtensional name key world error value nameEq oldAfter next}
    (cong snd (justInjective (trans (sym (extensionalChecked
      (checkedRootAcrossExtensional nameEq keyEq actor component oldBefore oldAfter newBefore OInsertTag
        oldChecked same valid (provisionsDisjointFrom {name} {key} {world} {error} {value} @{keyEq}
          (componentProvisions component) (bindings (registry oldBefore))) Refl frame))) newChecked)))
    (extensionalAfterSame
      (checkedRootAcrossExtensional nameEq keyEq actor component oldBefore oldAfter newBefore OInsertTag
        oldChecked same valid (provisionsDisjointFrom {name} {key} {world} {error} {value} @{keyEq}
          (componentProvisions component) (bindings (registry oldBefore))) Refl frame))
