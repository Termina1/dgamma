module DGamma.CP4RecoverySelectedEffect

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP4RecoveryAccumulator
import DGamma.Unified
import Decidable.Equality

%default total

||| The effect-level recovery equation for one successful selected L-Advance.
||| The target accumulator first receives Definition 60's normalized returned
||| state, then the pushed undo recovers the canonical source before delegating
||| to the older accumulator.
public export
0 successfulPushEffectRecovery :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {deps : List key} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (provision : CoeffectSpec key) ->
  (accumulator : LocalState key value world provision ->
    LocalState key value world provision) ->
  (step : StepEffect key value world error deps provision) ->
  (capability : DepValues key value deps) ->
  (source : EffectState name key value world) ->
  (after : LocalState key value world provision) ->
  (undo : LocalState key value world provision ->
    LocalState key value world provision) ->
  runStepEffect step capability
    (MkLocalState (effectAmbient source)
      (restrictOwnedPreservingOrder provision
        (effectTables source selected))) = Right (after, undo) ->
  let moved = setEffectTable @{nameEq} selected
        (ownedValues (localTable after))
        (setEffectAmbient (localWorld after) source)
  in PartialRelated (EffectState name key value world)
    (EffectStateRelated keyEq)
    (accumulatorRuntimeEffectMap nameEq keyEq selected
      (pushLocalUndo provision accumulator undo) moved)
    (accumulatorRuntimeEffectMap nameEq keyEq selected accumulator source)
successfulPushEffectRecovery nameEq keyEq selected provision accumulator step
  capability (MkEffectState ambient tables)
  (MkLocalState afterWorld afterTable) undo ran
  with (decEq @{nameEq} selected selected)
  successfulPushEffectRecovery nameEq keyEq selected provision accumulator step
    capability (MkEffectState ambient tables)
    (MkLocalState afterWorld afterTable) undo ran | No contra =
      void (contra Refl)
  successfulPushEffectRecovery nameEq keyEq selected provision accumulator step
    capability (MkEffectState ambient tables)
    (MkLocalState afterWorld afterTable) undo ran | Yes Refl =
      let 0 afterCanonical : (normalizeLocal provision
              (normalizeLocal provision (MkLocalState afterWorld afterTable)) =
            normalizeLocal provision (MkLocalState afterWorld afterTable))
          afterCanonical = normalizeLocalIdempotent provision
            (MkLocalState afterWorld afterTable)
          0 recovered : (undo
              (normalizeLocal provision (MkLocalState afterWorld afterTable)) =
            MkLocalState ambient
              (restrictOwnedPreservingOrder provision (tables selected)))
          recovered = restrictedStepRecovery step capability ambient
            (tables selected) (MkLocalState afterWorld afterTable) undo ran
          0 sourceCanonical : (normalizeLocal provision
              (MkLocalState ambient
                (restrictOwnedPreservingOrder provision (tables selected))) =
            MkLocalState ambient
              (restrictOwnedPreservingOrder provision (tables selected)))
          sourceCanonical = restrictedLocalCanonical provision ambient
            (tables selected)
          finalLocal : LocalState key value world provision
          finalLocal = accumulator
            (MkLocalState ambient
              (restrictOwnedPreservingOrder provision (tables selected)))
          sourceToMoved : EffectStateRelated keyEq
            (setEffectTable @{nameEq} selected
              (ownedValues (localTable finalLocal))
              (setEffectAmbient (localWorld finalLocal)
                (MkEffectState ambient tables)))
            (setEffectTable @{nameEq} selected
              (ownedValues (localTable finalLocal))
              (setEffectAmbient (localWorld finalLocal)
                (setEffectTable @{nameEq} selected (ownedValues afterTable)
                  (setEffectAmbient afterWorld
                    (MkEffectState ambient tables)))))
          sourceToMoved = effectOverwriteSameActor nameEq keyEq selected
            (localWorld finalLocal) afterWorld
            (ownedValues (localTable finalLocal)) (ownedValues afterTable)
            (MkEffectState ambient tables)
      in rewrite afterCanonical in rewrite recovered in
        rewrite sourceCanonical in
        PartialDefined (symmetric (EffectStateEquivalence keyEq) sourceToMoved)
