module DGamma.CP5O20PairedPrefixProducerSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionFrameCore
import DGamma.CP4RecoveryAccumulator
import DGamma.CP5O20EpisodeSynchronizationSpike
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Connect R180's observed-head recursion to the ACTUAL committed resolver.
||| The effect/view arguments are an induction hypothesis, not new O20 premises.
||| At canonical cuts the caller must instantiate the fixed accepted bijection.
export
0 pairedCommittedResolution :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (renaming : NameBijection name) -> (deps : List key) ->
  (leftView, rightView : View name deps) ->
  (left, right : SystemState name key value world error) ->
  RenamedRuntimeEffects name key world value renaming
    (projectEffectState {name = name} {key = key} {value = value} {world = world}
      {error = error} @{nameEq} left)
    (projectEffectState {name = name} {key = key} {value = value} {world = world}
      {error = error} @{nameEq} right) ->
  ViewRelatedBy renaming leftView rightView ->
  (resolveCommittedValues {name = name} {key = key} {value = value} {world = world}
    {error = error} @{nameEq} @{keyEq} deps leftView (registry left) =
   resolveCommittedValues {name = name} {key = key} {value = value} {world = world}
    {error = error} @{nameEq} @{keyEq} deps rightView (registry right))
pairedCommittedResolution name key world error value nameEq keyEq renaming deps
  leftView rightView left right effects views =
    trans (sym (resolveEffectValuesProjected nameEq keyEq deps leftView left))
      (trans (synchronizationResolutionFromObservedHeads name key world value keyEq
        renaming deps leftView rightView (projectEffectState @{nameEq} left)
        (projectEffectState @{nameEq} right) effects views)
        (resolveEffectValuesProjected nameEq keyEq deps rightView right))
