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

||| Transport a paired induction hypothesis through independently PRODUCED
||| exact runtime projection frames. These frames compare each side only to
||| its own observation; no cross-cut agreement is invented by this helper.
export
0 pairedEffectsAcrossFrames :
  (name, key, world : Type) -> (value : key -> Type) ->
  (keyEq : DecEq key) -> (renaming : NameBijection name) ->
  (leftBefore, leftAfter, rightBefore, rightAfter : EffectState name key value world) ->
  EffectStateRelated keyEq leftBefore leftAfter ->
  RenamedRuntimeEffects name key world value renaming leftBefore rightBefore ->
  EffectStateRelated keyEq rightBefore rightAfter ->
  RenamedRuntimeEffects name key world value renaming leftAfter rightAfter
pairedEffectsAcrossFrames name key world value keyEq renaming leftBefore leftAfter
  rightBefore rightAfter leftFrame paired rightFrame =
    MkRenamedRuntimeEffects
      (trans (sym (ambientExact leftFrame))
        (trans (synchronizedAmbient paired) (ambientExact rightFrame)))
      (\selected => trans (sym (tablesExact leftFrame selected))
        (trans (synchronizedTables paired selected)
          (tablesExact rightFrame (renameForward renaming selected))))

||| Observe the actual decision before projecting a foreign table update.
||| The producer passes decEq itself; this equation is never a caller oracle.
export
0 pairedForeignTableObserved :
  (name, key, world : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (selected, actor : name) ->
  Not (selected = actor) -> (table : CoeffectContext key value) ->
  (state : EffectState name key value world) ->
  (decision : Dec (selected = actor)) ->
  (decEq @{nameEq} selected actor = decision) ->
  (bindings (effectTables (setEffectTable @{nameEq} actor table state) selected) =
    bindings (effectTables state selected))
pairedForeignTableObserved name key world value nameEq selected actor distinct table
  state (Yes same) observed = void (distinct same)
pairedForeignTableObserved name key world value nameEq selected actor distinct table
  state (No different) observed = rewrite observed in Refl
