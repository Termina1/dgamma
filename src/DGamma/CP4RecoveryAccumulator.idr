module DGamma.CP4RecoveryAccumulator

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.Unified
import Decidable.Equality

%default total

||| The effect-level counterpart of `normalizeLocal`. It changes only the
||| selected table's erased confinement certificates and preserves its complete
||| runtime binding list and order.
public export
actorNormalizationMap :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (provision : CoeffectSpec key) -> PartialEffectMap name key value world
actorNormalizationMap nameEq keyEq selected provision state =
  let normalized = restrictOwnedPreservingOrder @{keyEq} provision
        (effectTables state selected)
  in Just (setEffectTable @{nameEq} selected (ownedValues normalized) state)

public export
0 effectTableAfterSetSelf : (nameEq : DecEq name) -> (selected : name) ->
  (table : CoeffectContext key value) ->
  (state : EffectState name key value world) ->
  effectTables (setEffectTable @{nameEq} selected table state) selected = table
effectTableAfterSetSelf nameEq selected table state
  with (decEq @{nameEq} selected selected)
  effectTableAfterSetSelf nameEq selected table state | Yes Refl = Refl
  effectTableAfterSetSelf nameEq selected table state | No contra =
    void (contra Refl)

public export
0 effectAmbientAfterSetTable : (nameEq : DecEq name) -> (selected : name) ->
  (table : CoeffectContext key value) ->
  (state : EffectState name key value world) ->
  effectAmbient (setEffectTable @{nameEq} selected table state) =
    effectAmbient state
effectAmbientAfterSetTable nameEq selected table
  (MkEffectState ambient tables) = Refl

public export
0 normalizeLocalExact : (keyEq : DecEq key) ->
  (provision : CoeffectSpec key) ->
  (local : LocalState key value world provision) ->
  normalizeLocal provision local = MkLocalState (localWorld local)
    (restrictOwnedPreservingOrder provision
      (ownedValues (localTable local)))
normalizeLocalExact keyEq provision (MkLocalState ambient table) = Refl

||| Overwriting the same actor's ambient/table contribution twice makes the
||| intermediate contribution observationally irrelevant. This is the exact
||| relation needed between a lifecycle accumulator and one yielded map.
public export
0 effectOverwriteSameActor :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (finalWorld, intermediateWorld : world) ->
  (finalTable, intermediateTable : CoeffectContext key value) ->
  (state : EffectState name key value world) ->
  EffectStateRelated keyEq
    (setEffectTable @{nameEq} selected finalTable
      (setEffectAmbient finalWorld state))
    (setEffectTable @{nameEq} selected finalTable
      (setEffectAmbient finalWorld
        (setEffectTable @{nameEq} selected intermediateTable
          (setEffectAmbient intermediateWorld state))))
effectOverwriteSameActor nameEq keyEq selected finalWorld intermediateWorld
  finalTable intermediateTable (MkEffectState ambient tables) =
    MkEffectStateRelated Refl tableLookups
  where
  0 tableLookups : (candidate : name) -> (k : key) ->
    lookupBinding @{keyEq} k
      (effectTables
        (setEffectTable @{nameEq} selected finalTable
          (setEffectAmbient finalWorld (MkEffectState ambient tables))) candidate) =
    lookupBinding @{keyEq} k
      (effectTables
        (setEffectTable @{nameEq} selected finalTable
          (setEffectAmbient finalWorld
            (setEffectTable @{nameEq} selected intermediateTable
              (setEffectAmbient intermediateWorld
                (MkEffectState ambient tables))))) candidate)
  tableLookups candidate k with (decEq @{nameEq} candidate selected) proof decision
    tableLookups candidate k | Yes same = case same of Refl => Refl
    tableLookups candidate k | No distinct = rewrite decision in Refl

public export
AccumulatorFactorization :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, last : SystemState name key value world error} ->
  {trace : Transitions first last} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (provision : CoeffectSpec key) ->
  (accumulator : LocalState key value world provision ->
    LocalState key value world provision) ->
  TraceEffectTransformation name key world error value selected trace -> Type
AccumulatorFactorization {name} {key} {world} {value} nameEq keyEq selected
  provision accumulator transformation =
    PartialMapsEquivalent (EffectStateEquivalence keyEq)
      (accumulatorEffectMap nameEq keyEq selected
        (MkAccumulatorHandle provision
          (the (OwnedTable key value provision) DGamma.Calculus.emptyOwned) accumulator))
      (partialCompose (actorNormalizationMap nameEq keyEq selected provision)
        (runTraceEffectTransformation transformation))

||| L-Begin's identity accumulator is exactly one trailing actor normalization.
public export
0 identityAccumulatorFactorization :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, last : SystemState name key value world error} ->
  {trace : Transitions first last} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (provision : CoeffectSpec key) ->
  AccumulatorFactorization {trace = trace} nameEq keyEq selected provision
    (\local => local) TraceIdentity
identityAccumulatorFactorization nameEq keyEq selected provision
  state@(MkEffectState ambient tables) =
    PartialDefined (effectStateReflexive keyEq
      (setEffectTable @{nameEq} selected
        (ownedValues (restrictOwnedPreservingOrder provision (tables selected)))
        state))

0 factorizationPushPoint :
  (keyEq : DecEq key) ->
  (normalizer, oldRun, generatorRun :
    PartialEffectMap name key value world) ->
  (state, moved, oldOutput, newOutput : EffectState name key value world) ->
  generatorRun state = Just moved ->
  PartialRelated (EffectState name key value world)
    (EffectStateRelated keyEq) (Just oldOutput)
    (partialCompose normalizer oldRun moved) ->
  EffectStateRelated keyEq newOutput oldOutput ->
  PartialRelated (EffectState name key value world)
    (EffectStateRelated keyEq) (Just newOutput)
    (partialCompose normalizer (partialCompose oldRun generatorRun) state)
factorizationPushPoint keyEq normalizer oldRun generatorRun state moved
  oldOutput newOutput generatorRuns oldFactor newToOld
  with (oldRun moved) proof oldRuns
  factorizationPushPoint keyEq normalizer oldRun generatorRun state moved
    oldOutput newOutput generatorRuns oldFactor newToOld | Nothing =
      case oldFactor of _ impossible
  factorizationPushPoint keyEq normalizer oldRun generatorRun state moved
    oldOutput newOutput generatorRuns oldFactor newToOld | Just generated
    with (normalizer generated) proof normalized
    factorizationPushPoint keyEq normalizer oldRun generatorRun state moved
      oldOutput newOutput generatorRuns oldFactor newToOld |
        Just generated | Nothing = case oldFactor of _ impossible
    factorizationPushPoint keyEq normalizer oldRun generatorRun state moved
      oldOutput newOutput generatorRuns oldFactor newToOld |
        Just generated | Just normalizedState =
          case oldFactor of
            PartialDefined oldToGenerated =>
              rewrite generatorRuns in rewrite oldRuns in rewrite normalized in
                PartialDefined (transitive (EffectStateEquivalence keyEq)
                  newToOld oldToGenerated)

||| Finding #9's central definitional alignment: after one `pushLocalUndo`, the
||| lifecycle accumulator factors through the old generated transformation,
||| the exact yielded inverse generator, and one final normalization.
public export
0 pushAccumulatorFactorization :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, last : SystemState name key value world error} ->
  {trace : Transitions first last} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (provision : CoeffectSpec key) ->
  (accumulator : LocalState key value world provision ->
    LocalState key value world provision) ->
  (undo : LocalState key value world provision ->
    LocalState key value world provision) ->
  (old : TraceEffectTransformation name key world error value selected trace) ->
  (generator : TraceEffectGenerator name key world error value selected trace) ->
  AccumulatorFactorization nameEq keyEq selected provision accumulator old ->
  ((state : EffectState name key value world) ->
    traceGeneratorMap generator state =
      yieldedInverseEffectMap nameEq keyEq selected provision undo state) ->
  AccumulatorFactorization nameEq keyEq selected provision
    (pushLocalUndo provision accumulator undo)
    (TraceCompose old (TraceGenerator generator))
pushAccumulatorFactorization nameEq keyEq selected provision accumulator undo
  old generator oldFactor generatorMap state@(MkEffectState ambient tables) =
    let normalized : OwnedTable key value provision
        normalized = restrictOwnedPreservingOrder @{keyEq} provision
          (tables selected)
        restored : LocalState key value world provision
        restored = undo (MkLocalState ambient normalized)
        moved : EffectState name key value world
        moved = setEffectTable @{nameEq} selected
          (ownedValues (localTable restored))
          (setEffectAmbient (localWorld restored) state)
        finalLocal : LocalState key value world provision
        finalLocal = accumulator (normalizeLocal provision restored)
        0 generatorRuns : traceGeneratorMap generator state = Just moved
        generatorRuns = trans (generatorMap state) Refl
        0 normalizedMoved : MkLocalState (effectAmbient moved)
          (restrictOwnedPreservingOrder provision
            (effectTables moved selected)) = normalizeLocal provision restored
        normalizedMoved =
          rewrite effectAmbientAfterSetTable nameEq selected
            (ownedValues (localTable restored))
            (setEffectAmbient (localWorld restored) state) in
          rewrite effectTableAfterSetSelf nameEq selected
            (ownedValues (localTable restored))
            (setEffectAmbient (localWorld restored) state) in
          sym (normalizeLocalExact keyEq provision restored)
        oldOutput : EffectState name key value world
        oldOutput = setEffectTable @{nameEq} selected
          (ownedValues (localTable finalLocal))
          (setEffectAmbient (localWorld finalLocal) moved)
        0 oldAccumulatorRuns : accumulatorEffectMap nameEq keyEq selected
          (MkAccumulatorHandle provision
            (the (OwnedTable key value provision) DGamma.Calculus.emptyOwned) accumulator) moved =
          Just oldOutput
        oldAccumulatorRuns = rewrite normalizedMoved in Refl
        0 oldFactorAt : PartialRelated (EffectState name key value world)
          (EffectStateRelated keyEq) (Just oldOutput)
          (partialCompose
            (actorNormalizationMap nameEq keyEq selected provision)
            (runTraceEffectTransformation old) moved)
        oldFactorAt = rewrite sym oldAccumulatorRuns in oldFactor moved
        0 newToOld : EffectStateRelated keyEq
          (setEffectTable @{nameEq} selected
            (ownedValues (localTable finalLocal))
            (setEffectAmbient (localWorld finalLocal) state))
          (setEffectTable @{nameEq} selected
            (ownedValues (localTable finalLocal))
            (setEffectAmbient (localWorld finalLocal) moved))
        newToOld = effectOverwriteSameActor nameEq keyEq selected
          (localWorld finalLocal) (localWorld restored)
          (ownedValues (localTable finalLocal))
          (ownedValues (localTable restored)) state
    in factorizationPushPoint keyEq
      (actorNormalizationMap nameEq keyEq selected provision)
      (runTraceEffectTransformation old) (traceGeneratorMap generator)
      state moved oldOutput
      (setEffectTable @{nameEq} selected
        (ownedValues (localTable finalLocal))
        (setEffectAmbient (localWorld finalLocal) state))
      generatorRuns oldFactorAt newToOld
