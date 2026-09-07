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

||| Simultaneous table-update law at the SAME bijection. Both equality
||| decisions are generated here; injectivity derives the foreign right case.
export
0 pairedSetTableBindings :
  (name, key, world : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (renaming : NameBijection name) -> (actor : name) ->
  (leftTable, rightTable : CoeffectContext key value) ->
  (bindings leftTable = bindings rightTable) ->
  (left, right : EffectState name key value world) ->
  RenamedRuntimeEffects name key world value renaming left right ->
  (selected : name) ->
  (bindings (effectTables (setEffectTable @{nameEq} actor leftTable left) selected) =
   bindings (effectTables (setEffectTable @{nameEq} (renameForward renaming actor)
      rightTable right) (renameForward renaming selected)))
pairedSetTableBindings name key world value nameEq renaming actor leftTable rightTable
  tableSame left right paired selected =
    case decEq @{nameEq} selected actor of
      Yes same => rewrite same in
        trans (cong bindings (effectTableAfterSetSelf nameEq actor leftTable left))
          (trans tableSame (sym (cong bindings (effectTableAfterSetSelf nameEq
            (renameForward renaming actor) rightTable right))))
      No different =>
        trans (pairedForeignTableObserved name key world value nameEq selected actor
          different leftTable left (decEq @{nameEq} selected actor) Refl)
          (trans (synchronizedTables paired selected)
            (sym (pairedForeignTableObserved name key world value nameEq
              (renameForward renaming selected) (renameForward renaming actor)
              (\same => different (trans (sym (renameLeftInverse renaming selected))
                (trans (cong (renameBackward renaming) same)
                  (renameLeftInverse renaming actor))))
              rightTable right (decEq @{nameEq} (renameForward renaming selected)
                (renameForward renaming actor)) Refl)))

||| Simultaneously update GLOBAL ambient and the two mapped actor tables.
||| These are actual executable setEffectTable/setEffectAmbient outputs.
export
0 pairedSetRuntimeEffects :
  (name, key, world : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (renaming : NameBijection name) -> (actor : name) ->
  (leftWorld, rightWorld : world) -> (leftWorld = rightWorld) ->
  (leftTable, rightTable : CoeffectContext key value) ->
  (bindings leftTable = bindings rightTable) ->
  (left, right : EffectState name key value world) ->
  RenamedRuntimeEffects name key world value renaming left right ->
  RenamedRuntimeEffects name key world value renaming
    (setEffectTable @{nameEq} actor leftTable (setEffectAmbient leftWorld left))
    (setEffectTable @{nameEq} (renameForward renaming actor) rightTable
      (setEffectAmbient rightWorld right))
pairedSetRuntimeEffects name key world value nameEq renaming actor leftWorld rightWorld
  worldSame leftTable rightTable tableSame left right paired =
    MkRenamedRuntimeEffects worldSame
      (pairedSetTableBindings name key world value nameEq renaming actor leftTable
        rightTable tableSame (setEffectAmbient leftWorld left)
        (setEffectAmbient rightWorld right)
        (MkRenamedRuntimeEffects worldSame (synchronizedTables paired)))

||| Simultaneous registration EFFECT producer at the two actual insertBinding
||| outputs. The surrounding paired trace must authenticate the OInsert guards;
||| this lemma neither assumes nor produces the missing canonical prefix choice.
export
0 pairedInsertEffects :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (renaming : NameBijection name) -> (actor : name) ->
  (component : Component key value world error) ->
  (leftParent, rightParent : Parent name) ->
  (leftWorld, rightWorld : world) ->
  (leftRegistry, rightRegistry : Registry name key value world error) ->
  (leftAbsent : (lookupFiber {name = name} {key = key} {value = value}
    {world = world} {error = error} @{nameEq} actor leftRegistry = Nothing)) ->
  (rightAbsent : (lookupFiber {name = name} {key = key} {value = value}
    {world = world} {error = error} @{nameEq} (renameForward renaming actor)
      rightRegistry = Nothing)) ->
  RenamedRuntimeEffects name key world value renaming
    (projectEffectState {name = name} {key = key} {value = value} {world = world}
      {error = error} @{nameEq} (MkSystemState leftWorld leftRegistry))
    (projectEffectState {name = name} {key = key} {value = value} {world = world}
      {error = error} @{nameEq} (MkSystemState rightWorld rightRegistry)) ->
  RenamedRuntimeEffects name key world value renaming
    (projectEffectState {name = name} {key = key} {value = value} {world = world}
      {error = error} @{nameEq} (MkSystemState leftWorld (insertBinding @{nameEq}
        actor (freshFiber component leftParent) leftRegistry leftAbsent)))
    (projectEffectState {name = name} {key = key} {value = value} {world = world}
      {error = error} @{nameEq} (MkSystemState rightWorld (insertBinding @{nameEq}
        (renameForward renaming actor) (freshFiber component rightParent)
          rightRegistry rightAbsent)))
pairedInsertEffects name key world error value nameEq keyEq renaming actor component
  leftParent rightParent leftWorld rightWorld leftRegistry rightRegistry leftAbsent
  rightAbsent paired =
    pairedEffectsAcrossFrames name key world value keyEq renaming
      (setEffectTable @{nameEq} actor emptyContext
        (projectEffectState @{nameEq} (MkSystemState leftWorld leftRegistry)))
      (projectEffectState @{nameEq} (MkSystemState leftWorld (insertBinding @{nameEq}
        actor (freshFiber component leftParent) leftRegistry leftAbsent)))
      (setEffectTable @{nameEq} (renameForward renaming actor) emptyContext
        (projectEffectState @{nameEq} (MkSystemState rightWorld rightRegistry)))
      (projectEffectState @{nameEq} (MkSystemState rightWorld (insertBinding @{nameEq}
        (renameForward renaming actor) (freshFiber component rightParent)
          rightRegistry rightAbsent)))
      (projectInsertEffectFrame nameEq keyEq actor leftWorld component leftParent
        leftRegistry leftAbsent)
      (pairedSetRuntimeEffects name key world value nameEq renaming actor leftWorld
        rightWorld (synchronizedAmbient paired) emptyContext emptyContext Refl
        (projectEffectState @{nameEq} (MkSystemState leftWorld leftRegistry))
        (projectEffectState @{nameEq} (MkSystemState rightWorld rightRegistry)) paired)
      (projectInsertEffectFrame nameEq keyEq (renameForward renaming actor) rightWorld
        component rightParent rightRegistry rightAbsent)

||| Actual inserted/foreign lookup split, preserving the selected control cut.
||| No selected-name opacity: fresh and foreign cases use actual lookup laws.
export
0 pairedInsertControls :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (renaming : NameBijection name) -> (actor : name) ->
  (component : Component key value world error) ->
  (leftParent, rightParent : Parent name) ->
  ParentRelatedBy renaming leftParent rightParent ->
  (leftRegistry, rightRegistry : Registry name key value world error) ->
  (leftAbsent : (lookupFiber {name = name} {key = key} {value = value}
    {world = world} {error = error} @{nameEq} actor leftRegistry = Nothing)) ->
  (rightAbsent : (lookupFiber {name = name} {key = key} {value = value}
    {world = world} {error = error} @{nameEq} (renameForward renaming actor)
      rightRegistry = Nothing)) ->
  (selected : name) ->
  MaybeFiberRelatedBy {name = name} {key = key} {world = world} {error = error}
    {value = value} renaming (lookupFiber {name = name} {key = key} {value = value} {world = world}
      {error = error} @{nameEq} selected leftRegistry)
    (lookupFiber {name = name} {key = key} {value = value} {world = world}
      {error = error} @{nameEq} (renameForward renaming selected) rightRegistry) ->
  MaybeFiberRelatedBy {name = name} {key = key} {world = world} {error = error}
    {value = value} renaming
    (lookupFiber {name = name} {key = key} {value = value} {world = world}
      {error = error} @{nameEq} selected (insertBinding @{nameEq} actor
      (freshFiber component leftParent) leftRegistry leftAbsent))
    (lookupFiber {name = name} {key = key} {value = value} {world = world}
      {error = error} @{nameEq} (renameForward renaming selected) (insertBinding @{nameEq}
      (renameForward renaming actor) (freshFiber component rightParent)
        rightRegistry rightAbsent))
pairedInsertControls name key world error value nameEq renaming actor component
  leftParent rightParent parents leftRegistry rightRegistry leftAbsent rightAbsent
  selected controls = case decEq @{nameEq} selected actor of
    Yes same => rewrite same in
      rewrite lookupInserted @{nameEq} actor (freshFiber component leftParent)
        leftRegistry leftAbsent in
      rewrite lookupInserted @{nameEq} (renameForward renaming actor)
        (freshFiber component rightParent) rightRegistry rightAbsent in
      RenamedPresent (RenamedFibers {component = component} leftParent rightParent
        False False emptyOwned emptyOwned (Inactive Nothing) (Inactive Nothing)
        parents Refl (RenamedInactive Refl))
    No different =>
      rewrite lookupInsertOther @{nameEq} selected actor different
        (freshFiber component leftParent) leftRegistry leftAbsent in
      rewrite lookupInsertOther @{nameEq} (renameForward renaming selected)
        (renameForward renaming actor)
        (\same => different (trans (sym (renameLeftInverse renaming selected))
          (trans (cong (renameBackward renaming) same)
            (renameLeftInverse renaming actor))))
        (freshFiber component rightParent) rightRegistry rightAbsent in controls
