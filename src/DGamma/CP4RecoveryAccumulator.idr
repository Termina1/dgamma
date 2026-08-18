module DGamma.CP4RecoveryAccumulator

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.Unified
import Data.List.Elem
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

||| One actor normalization is observationally identity on a provision-confined
||| runtime table. Finding #10 compares ordered bindings, not erased certificate
||| identity, so the Finding-7 order-preservation theorem closes this directly.
public export
0 actorNormalizationAtOwnedTable :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (provision : CoeffectSpec key) ->
  (table : OwnedTable key value provision) ->
  (state : EffectState name key value world) ->
  effectTables state selected = ownedValues table ->
  PartialRelated (EffectState name key value world) (EffectStateRelated keyEq)
    (actorNormalizationMap nameEq keyEq selected provision state) (Just state)
actorNormalizationAtOwnedTable nameEq keyEq selected provision table
  state@(MkEffectState ambient tables) tableAt = PartialDefined
    (MkEffectStateRelated Refl tableBindings)
  where
  0 tableBindings : (candidate : name) ->
    bindings (effectTables
      (setEffectTable @{nameEq} selected
        (ownedValues (restrictOwnedPreservingOrder provision (tables selected)))
        state) candidate) =
    bindings (effectTables state candidate)
  tableBindings candidate with (decEq @{nameEq} candidate selected) proof decision
    tableBindings candidate | Yes same = case same of
      Refl => rewrite tableAt in
        restrictOwnedPreservingOrderBindings provision table
    tableBindings candidate | No distinct = Refl

public export
0 identityAccumulatorMapIsNormalizer :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (provision : CoeffectSpec key) ->
  (table : OwnedTable key value provision) ->
  (state : EffectState name key value world) ->
  accumulatorEffectMap nameEq keyEq selected
    (MkAccumulatorHandle provision table (\local => local)) state =
  actorNormalizationMap nameEq keyEq selected provision state
identityAccumulatorMapIsNormalizer nameEq keyEq selected provision table
  (MkEffectState ambient tables) = Refl

0 justEffectInjective : Just left = Just right -> left = right
justEffectInjective Refl = Refl

||| The zero-step Theorem-61 base: the identity accumulator's mandatory input
||| normalization is related to the original owned table under ordered bindings.
public export
0 identityAccumulatorOwnedRecovery :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (provision : CoeffectSpec key) ->
  (table : OwnedTable key value provision) ->
  (state, restored : EffectState name key value world) ->
  effectTables state selected = ownedValues table ->
  accumulatorEffectMap nameEq keyEq selected
    (MkAccumulatorHandle provision table (\local => local)) state =
    Just restored ->
  EffectStateRelated keyEq state restored
identityAccumulatorOwnedRecovery nameEq keyEq selected provision table state
  restored tableAt restoredEquation =
    case actorNormalizationAtOwnedTable nameEq keyEq selected provision table
      state tableAt of
      PartialDefined normalizedToState =>
        let 0 normalizerEquation : (actorNormalizationMap nameEq keyEq selected
              provision state = Just restored)
            normalizerEquation = trans
              (sym (identityAccumulatorMapIsNormalizer nameEq keyEq selected
                provision table state)) restoredEquation
            0 normalizedIsRestored :
              (setEffectTable @{nameEq} selected
                 (ownedValues (restrictOwnedPreservingOrder provision
                   (effectTables state selected))) state = restored)
            normalizedIsRestored = justEffectInjective normalizerEquation
        in replace
          {p = \observed => EffectStateRelated keyEq state observed}
          normalizedIsRestored
          (symmetric (EffectStateEquivalence keyEq) normalizedToState)

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
  0 tableLookups : (candidate : name) ->
    bindings (effectTables
      (setEffectTable @{nameEq} selected finalTable
        (setEffectAmbient finalWorld (MkEffectState ambient tables))) candidate) =
    bindings (effectTables
      (setEffectTable @{nameEq} selected finalTable
        (setEffectAmbient finalWorld
          (setEffectTable @{nameEq} selected intermediateTable
            (setEffectAmbient intermediateWorld
              (MkEffectState ambient tables))))) candidate)
  tableLookups candidate with (decEq @{nameEq} candidate selected) proof decision
    tableLookups candidate | Yes same = case same of Refl => Refl
    tableLookups candidate | No distinct = rewrite decision in Refl

public export
ActorEffectTableConfined :
  {name, key, world : Type} -> {value : key -> Type} ->
  (selected : name) -> (provision : CoeffectSpec key) ->
  EffectState name key value world -> Type
ActorEffectTableConfined {key} selected provision state =
  (k : key) ->
  Elem k (bindingKeys (bindings (effectTables state selected))) ->
  Elem k (dependencies provision)

public export
TransformationPreservesConfinement :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, last : SystemState name key value world error} ->
  {trace : Transitions first last} ->
  (selected : name) -> (provision : CoeffectSpec key) ->
  TraceEffectTransformation name key world error value selected trace -> Type
TransformationPreservesConfinement {name} {key} {world} {value}
  selected provision transformation =
  (state, moved : EffectState name key value world) ->
  ActorEffectTableConfined selected provision state ->
  runTraceEffectTransformation transformation state = Just moved ->
  ActorEffectTableConfined selected provision moved

public export
0 identityTransformationPreservesConfinement :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, last : SystemState name key value world error} ->
  {trace : Transitions first last} ->
  (selected : name) -> (provision : CoeffectSpec key) ->
  TransformationPreservesConfinement selected provision
    (TraceIdentity {trace = trace})
identityTransformationPreservesConfinement selected provision state state
  confined Refl = confined

public export
0 actorNormalizationIdentityWhenConfined :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (provision : CoeffectSpec key) ->
  (state : EffectState name key value world) ->
  ActorEffectTableConfined selected provision state ->
  PartialRelated (EffectState name key value world) (EffectStateRelated keyEq)
    (actorNormalizationMap nameEq keyEq selected provision state) (Just state)
actorNormalizationIdentityWhenConfined nameEq keyEq selected provision
  state@(MkEffectState ambient tables) confined = PartialDefined
    (MkEffectStateRelated Refl tableBindings)
  where
  table : OwnedTable key value provision
  table = MkOwnedTable (tables selected) confined

  0 tableBindings : (candidate : name) ->
    bindings (effectTables
      (setEffectTable @{nameEq} selected
        (ownedValues (restrictOwnedPreservingOrder provision (tables selected)))
        state) candidate) = bindings (effectTables state candidate)
  tableBindings candidate with (decEq @{nameEq} candidate selected) proof decision
    tableBindings candidate | Yes same = case same of
      Refl => restrictOwnedPreservingOrderBindings provision table
    tableBindings candidate | No distinct = Refl

0 partialComposeRuns :
  (before, after : PartialEffectMap name key value world) ->
  (state, moved, final : EffectState name key value world) ->
  before state = Just moved ->
  partialCompose after before state = Just final ->
  after moved = Just final
partialComposeRuns before after state moved final beforeRuns composed
  with (before state)
  partialComposeRuns before after state moved final beforeRuns composed |
    Nothing = void (nothingIsNotJust beforeRuns)
  partialComposeRuns before after state moved final beforeRuns composed |
    Just actual = case justEffectInjective beforeRuns of
      Refl => composed

public export
0 pushTransformationPreservesConfinement :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (provision : CoeffectSpec key) ->
  (undo : LocalState key value world provision ->
    LocalState key value world provision) ->
  (old : TraceEffectTransformation name key world error value selected trace) ->
  (generator : TraceEffectGenerator name key world error value selected trace) ->
  TransformationPreservesConfinement selected provision old ->
  ((state : EffectState name key value world) ->
    traceGeneratorMap generator state =
      yieldedInverseEffectMap nameEq keyEq selected provision undo state) ->
  TransformationPreservesConfinement selected provision
    (TraceCompose old (TraceGenerator generator))
pushTransformationPreservesConfinement nameEq keyEq selected provision undo old
  generator oldPreserves generatorMap state final confined equation =
    let normalized : OwnedTable key value provision
        normalized = restrictOwnedPreservingOrder @{keyEq} provision
          (effectTables state selected)
        restored : LocalState key value world provision
        restored = undo (MkLocalState (effectAmbient state) normalized)
        moved : EffectState name key value world
        moved = setEffectTable @{nameEq} selected
          (ownedValues (localTable restored))
          (setEffectAmbient (localWorld restored) state)
        0 generatorRuns : (traceGeneratorMap generator state = Just moved)
        generatorRuns = trans (generatorMap state) Refl
        0 oldRuns : (runTraceEffectTransformation old moved = Just final)
        oldRuns = partialComposeRuns (traceGeneratorMap generator)
          (runTraceEffectTransformation old) state moved final generatorRuns
          equation
        0 movedConfined : ActorEffectTableConfined selected provision moved
        movedConfined k present =
          let tableAt = effectTableAfterSetSelf nameEq selected
                (ownedValues (localTable restored))
                (setEffectAmbient (localWorld restored) state)
          in ownedSound (localTable restored) k
            (replace
              {p = \context => Elem k (bindingKeys (bindings context))}
              tableAt present)
    in oldPreserves moved final movedConfined oldRuns

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
