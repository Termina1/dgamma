module DGamma.CP4RecoveryForeignCommute

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP4DeletionFrameCore
import DGamma.CP4DeletionFrames
import DGamma.CP4RecoveryAccumulator
import DGamma.CP4RecoveryTrace
import DGamma.CP4RecoveryEffectRespect
import DGamma.CP4RecoveryForeignEffect
import DGamma.Unified
import Data.List.Elem
import Decidable.Equality

%default total

0 partialNothingJustImpossible :
  PartialRelated state rel Nothing (Just right) -> Void
partialNothingJustImpossible relation impossible

0 partialJustNothingImpossible :
  PartialRelated state rel (Just left) Nothing -> Void
partialJustNothingImpossible relation impossible

0 partialRelatedRewrite :
  leftBefore = leftAfter -> rightBefore = rightAfter ->
  PartialRelated state rel leftBefore rightBefore ->
  PartialRelated state rel leftAfter rightAfter
partialRelatedRewrite Refl Refl related = related

0 partialComposeDefined :
  (after, before : PartialMap state) -> (origin, middle, final : state) ->
  before origin = Just middle -> after middle = Just final ->
  partialCompose after before origin = Just final
partialComposeDefined after before origin middle final beforeRuns afterRuns
  with (before origin)
  partialComposeDefined after before origin middle final beforeRuns afterRuns |
    Nothing = void (nothingIsNotJust beforeRuns)
  partialComposeDefined after before origin middle final beforeRuns afterRuns |
    Just actual = case justInjective beforeRuns of
      Refl => rewrite afterRuns in Refl

0 partialComposeUndefined :
  (after, before : PartialMap state) -> (origin : state) ->
  before origin = Nothing -> partialCompose after before origin = Nothing
partialComposeUndefined after before origin beforeRuns with (before origin)
  partialComposeUndefined after before origin beforeRuns | Nothing = Refl
  partialComposeUndefined after before origin beforeRuns | Just actual =
    void (nothingIsNotJust (sym beforeRuns))

0 partialComposeAfterUndefined :
  (after, before : PartialMap state) -> (origin, middle : state) ->
  before origin = Just middle -> after middle = Nothing ->
  partialCompose after before origin = Nothing
partialComposeAfterUndefined after before origin middle beforeRuns afterRuns
  with (before origin)
  partialComposeAfterUndefined after before origin middle beforeRuns afterRuns |
    Nothing = void (nothingIsNotJust beforeRuns)
  partialComposeAfterUndefined after before origin middle beforeRuns afterRuns |
    Just actual = case justInjective beforeRuns of
      Refl => rewrite afterRuns in Refl

0 partialDefinedRelation :
  PartialRelated state rel (Just left) (Just right) -> rel left right
partialDefinedRelation (PartialDefined related) = related

0 partialSymmetric : (eq : Equivalence state) ->
  PartialRelated state (relation eq) left right ->
  PartialRelated state (relation eq) right left
partialSymmetric eq PartialUndefined = PartialUndefined
partialSymmetric eq (PartialDefined related) =
  PartialDefined (symmetric eq related)

0 partialTransitive : (eq : Equivalence state) ->
  PartialRelated state (relation eq) left middle ->
  PartialRelated state (relation eq) middle right ->
  PartialRelated state (relation eq) left right
partialTransitive eq PartialUndefined PartialUndefined = PartialUndefined
partialTransitive eq (PartialDefined first) (PartialDefined second) =
  PartialDefined (transitive eq first second)

normalizationOutput :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (provision : CoeffectSpec key) -> EffectState name key value world ->
  EffectState name key value world
normalizationOutput nameEq keyEq selected provision state =
  setEffectTable @{nameEq} selected
    (ownedValues (restrictOwnedPreservingOrder provision
      (effectTables state selected))) state

0 normalizationOutputRuns :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (provision : CoeffectSpec key) -> (state : EffectState name key value world) ->
  actorNormalizationMap nameEq keyEq selected provision state =
  Just (normalizationOutput nameEq keyEq selected provision state)
normalizationOutputRuns nameEq keyEq selected provision
  (MkEffectState ambient tables) = Refl

accumulatorOutput :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (provision : CoeffectSpec key) ->
  (LocalState key value world provision -> LocalState key value world provision) ->
  EffectState name key value world -> EffectState name key value world
accumulatorOutput nameEq keyEq selected provision accumulator state =
  let restored = accumulator
        (MkLocalState (effectAmbient state)
          (restrictOwnedPreservingOrder provision (effectTables state selected)))
  in setEffectTable @{nameEq} selected (ownedValues (localTable restored))
    (setEffectAmbient (localWorld restored) state)

0 accumulatorOutputRuns :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (provision : CoeffectSpec key) ->
  (accumulator : LocalState key value world provision ->
    LocalState key value world provision) ->
  (state : EffectState name key value world) ->
  accumulatorEffectMap nameEq keyEq selected
    (MkAccumulatorHandle provision
      (the (OwnedTable key value provision) DGamma.Calculus.emptyOwned)
      accumulator) state =
  Just (accumulatorOutput nameEq keyEq selected provision accumulator state)
accumulatorOutputRuns nameEq keyEq selected provision accumulator
  (MkEffectState ambient tables) = Refl

record AccumulatorFactorPoint
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (selected : name)
  {first, last : SystemState name key value world error}
  {trace : Transitions first last}
  (provision : CoeffectSpec key)
  (accumulator : LocalState key value world provision ->
    LocalState key value world provision)
  (transformation : TraceEffectTransformation name key world error value selected
    trace)
  (state : EffectState name key value world) where
  constructor MkAccumulatorFactorPoint
  0 generated : EffectState name key value world
  0 normalized : EffectState name key value world
  0 recovered : EffectState name key value world
  0 generatedRuns : runTraceEffectTransformation transformation state =
    Just generated
  0 normalizerRuns : actorNormalizationMap nameEq keyEq selected provision
    generated = Just normalized
  0 accumulatorRuns : accumulatorEffectMap nameEq keyEq selected
    (MkAccumulatorHandle provision
      (the (OwnedTable key value provision) DGamma.Calculus.emptyOwned)
      accumulator) state = Just recovered
  0 recoveredToNormalized : EffectStateRelated keyEq recovered normalized

0 buildAccumulatorFactorPoint :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (provision : CoeffectSpec key) ->
  (accumulator : LocalState key value world provision ->
    LocalState key value world provision) ->
  (transformation : TraceEffectTransformation name key world error value selected
    trace) ->
  (0 factor : AccumulatorFactorization nameEq keyEq selected provision accumulator
    transformation) ->
  (state : EffectState name key value world) ->
  AccumulatorFactorPoint name key world error value nameEq keyEq selected
    provision accumulator transformation state
buildAccumulatorFactorPoint {name} {key} {world} {error} {value}
  nameEq keyEq selected provision accumulator transformation factor
  state@(MkEffectState ambient tables)
  with (runTraceEffectTransformation transformation
    (MkEffectState ambient tables)) proof generatedResult
  buildAccumulatorFactorPoint nameEq keyEq selected provision accumulator
    transformation factor state@(MkEffectState ambient tables) | Nothing =
      let recovered : EffectState name key value world
          recovered = setEffectTable @{nameEq} selected
            (ownedValues (localTable (accumulator
              (MkLocalState ambient
                (restrictOwnedPreservingOrder provision (tables selected))))))
            (setEffectAmbient (localWorld (accumulator
              (MkLocalState ambient
                (restrictOwnedPreservingOrder provision (tables selected)))))
              (MkEffectState ambient tables))
          0 leftEquation : (accumulatorEffectMap nameEq keyEq selected
            (MkAccumulatorHandle provision
              (the (OwnedTable key value provision) DGamma.Calculus.emptyOwned)
              accumulator) (MkEffectState ambient tables) = Just recovered)
          leftEquation = Refl
          0 rightEquation : (partialCompose
            (actorNormalizationMap nameEq keyEq selected provision)
            (runTraceEffectTransformation transformation)
            (MkEffectState ambient tables) = Nothing)
          rightEquation = partialComposeUndefined
            (actorNormalizationMap nameEq keyEq selected provision)
            (runTraceEffectTransformation transformation)
            (MkEffectState ambient tables) generatedResult
          0 contradiction : PartialRelated (EffectState name key value world)
            (EffectStateRelated keyEq) (Just recovered) Nothing
          contradiction = partialRelatedRewrite leftEquation rightEquation
            (factor (MkEffectState ambient tables))
      in void (partialJustNothingImpossible contradiction)
  buildAccumulatorFactorPoint nameEq keyEq selected provision accumulator
    transformation factor state@(MkEffectState ambient tables) | Just generated =
      let 0 normalizedRuns : (actorNormalizationMap nameEq keyEq selected
            provision generated = Just
              (normalizationOutput nameEq keyEq selected provision generated))
          normalizedRuns = normalizationOutputRuns nameEq keyEq selected provision
            generated
          0 recoveredRuns : (accumulatorEffectMap nameEq keyEq selected
            (MkAccumulatorHandle provision
              (the (OwnedTable key value provision) DGamma.Calculus.emptyOwned)
              accumulator) (MkEffectState ambient tables) = Just
                (accumulatorOutput nameEq keyEq selected provision accumulator
                  (MkEffectState ambient tables)))
          recoveredRuns = accumulatorOutputRuns nameEq keyEq selected provision
            accumulator (MkEffectState ambient tables)
          0 composedRuns : partialCompose
            (actorNormalizationMap nameEq keyEq selected provision)
            (runTraceEffectTransformation transformation)
            (MkEffectState ambient tables) = Just
              (normalizationOutput nameEq keyEq selected provision generated)
          composedRuns = partialComposeDefined
            (actorNormalizationMap nameEq keyEq selected provision)
            (runTraceEffectTransformation transformation)
            (MkEffectState ambient tables) generated
            (normalizationOutput nameEq keyEq selected provision generated)
            generatedResult normalizedRuns
          0 related : EffectStateRelated keyEq
            (accumulatorOutput nameEq keyEq selected provision accumulator
              (MkEffectState ambient tables))
            (normalizationOutput nameEq keyEq selected provision generated)
          related = case partialRelatedRewrite recoveredRuns composedRuns
            (factor (MkEffectState ambient tables)) of
            PartialDefined relation => relation
      in MkAccumulatorFactorPoint generated
        (normalizationOutput nameEq keyEq selected provision generated)
        (accumulatorOutput nameEq keyEq selected provision accumulator
          (MkEffectState ambient tables))
        generatedResult normalizedRuns recoveredRuns related

0 factorPointNormalizationIdentity :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (provision : CoeffectSpec key) ->
  (accumulator : LocalState key value world provision ->
    LocalState key value world provision) ->
  (transformation : TraceEffectTransformation name key world error value selected
    trace) ->
  (state : EffectState name key value world) ->
  (point : AccumulatorFactorPoint name key world error value nameEq keyEq selected
    provision accumulator transformation state) ->
  ActorEffectTableConfined selected provision (generated point) ->
  EffectStateRelated keyEq (normalized point) (generated point)
factorPointNormalizationIdentity nameEq keyEq selected provision accumulator
  transformation state point confined =
    case actorNormalizationIdentityWhenConfined nameEq keyEq selected provision
      (generated point) confined of
      PartialDefined canonicalToGenerated =>
        let 0 canonicalRuns :
              (actorNormalizationMap nameEq keyEq selected provision
                 (generated point) = Just
                   (normalizationOutput nameEq keyEq selected provision
                     (generated point)))
            canonicalRuns = normalizationOutputRuns nameEq keyEq selected
              provision (generated point)
            0 canonicalIsStored : normalizationOutput nameEq keyEq selected
              provision (generated point) = normalized point
            canonicalIsStored = justInjective
              (trans (sym canonicalRuns) (normalizerRuns point))
        in replace
          {p = \observed => EffectStateRelated keyEq observed (generated point)}
          canonicalIsStored canonicalToGenerated

0 projectedModelTableConfined :
  (nameEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} selected (registry state) = Just fiber ->
  ActorEffectTableConfined selected
    (componentProvisions (fiberComponent fiber))
    (projectEffectState @{nameEq} state)
projectedModelTableConfined nameEq selected state fiber found k present =
  let tableAt = projectedActorTable nameEq selected state fiber found
  in ownedSound (fiberTable fiber) k
    (replace {p = \context => Elem k (bindingKeys (bindings context))}
      tableAt present)

0 actualForwardGeneratorMap :
  (before, afterState : SystemState name key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  (occurs : OccursIn
    (Fired {before = before} {afterState = afterState}
      nameEq keyEq action tag checked) trace) ->
  (state : EffectState name key value world) ->
  traceGeneratorMap
    (ActualForwardGenerator before afterState nameEq keyEq action tag checked
      occurs Refl) state =
  partialEffectMap
    (Fired {before = before} {afterState = afterState}
      nameEq keyEq action tag checked) state
actualForwardGeneratorMap before afterState nameEq keyEq action tag checked occurs
  state = Refl

record CommuteRightResult
  (state : Type) (eq : Equivalence state)
  (leftMap, rightMap : PartialMap state)
  (origin, moved, leftOutput : state) where
  constructor MkCommuteRightResult
  0 rightInput : state
  0 rightOutput : state
  0 leftAtOrigin : leftMap origin = Just rightInput
  0 rightAfterLeft : rightMap rightInput = Just rightOutput
  0 outputsRelated : relation eq leftOutput rightOutput

0 commuteRightFromLeft :
  (eq : Equivalence state) -> (leftMap, rightMap : PartialMap state) ->
  (origin, moved, leftOutput : state) ->
  (0 rightRuns : rightMap origin = Just moved) ->
  (0 leftRuns : leftMap moved = Just leftOutput) ->
  (0 commutes : PartialCommute eq leftMap rightMap) ->
  CommuteRightResult state eq leftMap rightMap origin moved leftOutput
commuteRightFromLeft eq leftMap rightMap origin moved leftOutput rightRuns
  leftRuns commutes with (leftMap origin) proof leftAtOrigin
  commuteRightFromLeft eq leftMap rightMap origin moved leftOutput rightRuns
    leftRuns commutes | Nothing =
      let 0 leftEquation : (partialCompose leftMap rightMap origin =
            Just leftOutput)
          leftEquation = partialComposeDefined leftMap rightMap origin moved
            leftOutput rightRuns leftRuns
          0 rightEquation : (partialCompose rightMap leftMap origin = Nothing)
          rightEquation = partialComposeUndefined rightMap leftMap origin
            leftAtOrigin
          0 contradiction : PartialRelated state (relation eq)
            (Just leftOutput) Nothing
          contradiction = partialRelatedRewrite leftEquation rightEquation
            (commutes origin)
      in void (partialJustNothingImpossible contradiction)
  commuteRightFromLeft eq leftMap rightMap origin moved leftOutput rightRuns
    leftRuns commutes | Just rightInput
    with (rightMap rightInput) proof rightAfterLeft
    commuteRightFromLeft eq leftMap rightMap origin moved leftOutput rightRuns
      leftRuns commutes | Just rightInput | Nothing =
        let 0 leftEquation : (partialCompose leftMap rightMap origin =
              Just leftOutput)
            leftEquation = partialComposeDefined leftMap rightMap origin moved
              leftOutput rightRuns leftRuns
            0 rightEquation : (partialCompose rightMap leftMap origin = Nothing)
            rightEquation = partialComposeAfterUndefined rightMap leftMap origin
              rightInput leftAtOrigin rightAfterLeft
            0 contradiction : PartialRelated state (relation eq)
              (Just leftOutput) Nothing
            contradiction = partialRelatedRewrite leftEquation rightEquation
              (commutes origin)
        in void (partialJustNothingImpossible contradiction)
    commuteRightFromLeft eq leftMap rightMap origin moved leftOutput rightRuns
      leftRuns commutes | Just rightInput | Just rightOutput =
        let 0 leftEquation : (partialCompose leftMap rightMap origin =
              Just leftOutput)
            leftEquation = partialComposeDefined leftMap rightMap origin moved
              leftOutput rightRuns leftRuns
            0 rightEquation : (partialCompose rightMap leftMap origin =
              Just rightOutput)
            rightEquation = partialComposeDefined rightMap leftMap origin
              rightInput rightOutput leftAtOrigin rightAfterLeft
            0 relationAtPoint : PartialRelated state (relation eq)
              (Just leftOutput) (Just rightOutput)
            relationAtPoint = partialRelatedRewrite leftEquation rightEquation
              (commutes origin)
        in MkCommuteRightResult rightInput rightOutput leftAtOrigin
          rightAfterLeft (partialDefinedRelation relationAtPoint)

record RespectLeftResult
  (state : Type) (eq : Equivalence state) (effectMap : PartialMap state)
  (left, right, rightOutput : state) where
  constructor MkRespectLeftResult
  0 leftOutput : state
  0 leftRuns : effectMap left = Just leftOutput
  0 outputsRelated : relation eq leftOutput rightOutput

0 respectLeftFromRight :
  (keyEq : DecEq key) ->
  (effectMap : PartialEffectMap name key value world) ->
  (0 respects : EffectPartialMapRespects keyEq effectMap) ->
  (left, right, rightOutput : EffectState name key value world) ->
  (0 inputsRelated : EffectStateRelated keyEq left right) ->
  (0 rightRuns : effectMap right = Just rightOutput) ->
  RespectLeftResult (EffectState name key value world)
    (EffectStateEquivalence keyEq) effectMap left right rightOutput
respectLeftFromRight keyEq effectMap respects left right rightOutput inputsRelated
  rightRuns with (effectMap left) proof leftResult
  respectLeftFromRight keyEq effectMap respects left right rightOutput inputsRelated
    rightRuns | Nothing =
      let 0 contradiction : PartialRelated (EffectState name key value world)
            (EffectStateRelated keyEq) Nothing (Just rightOutput)
          contradiction = partialRelatedRewrite leftResult rightRuns
            (respects left right inputsRelated)
      in void (partialNothingJustImpossible contradiction)
  respectLeftFromRight keyEq effectMap respects left right rightOutput inputsRelated
    rightRuns | Just leftOutput =
      let 0 atPoint : PartialRelated (EffectState name key value world)
            (EffectStateRelated keyEq) (Just leftOutput) (Just rightOutput)
          atPoint = partialRelatedRewrite leftResult rightRuns
            (respects left right inputsRelated)
      in MkRespectLeftResult leftOutput leftResult
        (partialDefinedRelation atPoint)

public export
record ForeignAccumulatorStep
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (selected : name)
  {before, afterState : SystemState name key value world error}
  (transition : Transition before afterState)
  {wholeFirst, wholeLast : SystemState name key value world error}
  (whole : Transitions wholeFirst wholeLast)
  (model : AccumulatorModel name key world error value nameEq keyEq selected whole
    before) where
  constructor MkForeignAccumulatorStep
  0 sourceRecovered : EffectState name key value world
  0 targetRecovered : EffectState name key value world
  0 foreignRecovered : EffectState name key value world
  0 sourceAccumulatorRuns : accumulatorEffectMap nameEq keyEq selected
    (modelHandle model) (projectEffectState @{nameEq} before) =
    Just sourceRecovered
  0 targetAccumulatorRuns : accumulatorEffectMap nameEq keyEq selected
    (modelHandle model) (projectEffectState @{nameEq} afterState) =
    Just targetRecovered
  0 foreignRecoveredRuns : partialEffectMap transition sourceRecovered =
    Just foreignRecovered
  0 targetRecoveredRelated : EffectStateRelated keyEq targetRecovered
    foreignRecovered

||| One paper-Theorem-61 foreign induction step: the concrete accumulator at
||| the checked target equals replaying that foreign map over the source's
||| recovered state. The proof factors the accumulator through its generated
||| inverse transformation, applies Definition-60 commutation, and discharges
||| both trailing normalizations from the maintained confinement invariant.
public export
0 foreignAccumulatorStep :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  Not (selected = actionOwner action) ->
  (whole : Transitions wholeFirst wholeLast) ->
  (occurs : OccursIn
    (Fired {before = before} {afterState = afterState}
      nameEq keyEq action tag checked) whole) ->
  TraceIndependent name key world error value keyEq whole ->
  (model : AccumulatorModel name key world error value nameEq keyEq selected whole
    before) ->
  ForeignAccumulatorStep name key world error value nameEq keyEq selected
    (Fired nameEq keyEq action tag checked) whole model
foreignAccumulatorStep {name} {key} {world} {error} {value}
  nameEq keyEq selected action tag before afterState checked distinct whole occurs
  independent
  model@(MkAccumulatorModel
    fiber@(MkFiber component parent retiredFlag table lifecycle) found accumulator
    installed transformation factorization confinement)
  with (partialEffectMap
    (Fired {before = before} {afterState = afterState}
      nameEq keyEq action tag checked)
    (projectEffectState @{nameEq} before)) proof movedResult
  foreignAccumulatorStep nameEq keyEq selected action tag before afterState
    checked distinct whole occurs independent
    model@(MkAccumulatorModel
      fiber@(MkFiber component parent retiredFlag table lifecycle) found accumulator
      installed transformation factorization confinement) | Nothing =
      case actualTransitionEffectFrame nameEq keyEq action tag before afterState
        checked of
        MkActualEffectFrame framed =>
          let 0 contradiction : PartialRelated
                (EffectState name key value world) (EffectStateRelated keyEq)
                Nothing (Just (projectEffectState @{nameEq} afterState))
              contradiction = partialRelatedRewrite movedResult Refl framed
          in void (partialNothingJustImpossible contradiction)
  foreignAccumulatorStep nameEq keyEq selected action tag before afterState
    checked distinct whole occurs independent
    model@(MkAccumulatorModel
      fiber@(MkFiber component parent retiredFlag table lifecycle) found accumulator
      installed transformation factorization confinement) | Just moved =
      let sourcePoint = buildAccumulatorFactorPoint nameEq keyEq selected
            (componentProvisions component) accumulator transformation
            factorization (projectEffectState @{nameEq} before)
          movedPoint = buildAccumulatorFactorPoint nameEq keyEq selected
            (componentProvisions component) accumulator transformation
            factorization moved
          targetPoint = buildAccumulatorFactorPoint nameEq keyEq selected
            (componentProvisions component) accumulator transformation
            factorization (projectEffectState @{nameEq} afterState)
          foreignGenerator : TraceEffectGenerator name key world error value
            (actionOwner action) whole
          foreignGenerator = ActualForwardGenerator before afterState nameEq keyEq
            action tag checked occurs Refl
          foreignTransformation : TraceEffectTransformation name key world error
            value (actionOwner action) whole
          foreignTransformation = TraceGenerator foreignGenerator
          0 movedToTarget : EffectStateRelated keyEq moved
            (projectEffectState @{nameEq} afterState)
          movedToTarget = case actualTransitionEffectFrame nameEq keyEq action tag
            before afterState checked of
            MkActualEffectFrame framed =>
              case partialRelatedRewrite movedResult Refl framed of
                PartialDefined related => related
          0 sourceConfined : ActorEffectTableConfined selected
            (componentProvisions component)
            (projectEffectState @{nameEq} before)
          sourceConfined = projectedModelTableConfined nameEq selected before
            (MkFiber component parent retiredFlag table lifecycle) found
          0 movedBindings : bindings (effectTables moved selected) =
            bindings (effectTables (projectEffectState @{nameEq} before) selected)
          movedBindings = partialEffectMapForForeignPreservesBindings nameEq keyEq
            selected action distinct tag before
            (projectEffectState @{nameEq} before) moved movedResult
          0 movedConfined : ActorEffectTableConfined selected
            (componentProvisions component) moved
          movedConfined k present = sourceConfined k
            (replace {p = \bs => Elem k (bindingKeys bs)} movedBindings present)
          0 sourceGeneratedConfined : ActorEffectTableConfined selected
            (componentProvisions component) (generated sourcePoint)
          sourceGeneratedConfined = confinement
            (projectEffectState @{nameEq} before) (generated sourcePoint)
            sourceConfined (generatedRuns sourcePoint)
          0 movedGeneratedConfined : ActorEffectTableConfined selected
            (componentProvisions component) (generated movedPoint)
          movedGeneratedConfined = confinement moved (generated movedPoint)
            movedConfined (generatedRuns movedPoint)
          0 sourceNormalizedToGenerated : EffectStateRelated keyEq
            (normalized sourcePoint) (generated sourcePoint)
          sourceNormalizedToGenerated = factorPointNormalizationIdentity nameEq
            keyEq selected (componentProvisions component) accumulator
            transformation (projectEffectState @{nameEq} before) sourcePoint
            sourceGeneratedConfined
          0 movedNormalizedToGenerated : EffectStateRelated keyEq
            (normalized movedPoint) (generated movedPoint)
          movedNormalizedToGenerated = factorPointNormalizationIdentity nameEq
            keyEq selected (componentProvisions component) accumulator
            transformation moved movedPoint movedGeneratedConfined
          0 commutes : PartialCommute (EffectStateEquivalence keyEq)
            (runTraceEffectTransformation transformation)
            (runTraceEffectTransformation foreignTransformation)
          commutes = generatedMonoidsCommute independent selected
            (actionOwner action) distinct transformation foreignTransformation
          0 foreignMovedResult : runTraceEffectTransformation foreignTransformation
            (projectEffectState @{nameEq} before) = Just moved
          foreignMovedResult = trans
            (actualForwardGeneratorMap before afterState nameEq keyEq action tag
              checked occurs (projectEffectState @{nameEq} before)) movedResult
          0 commuted : CommuteRightResult
            (EffectState name key value world) (EffectStateEquivalence keyEq)
            (runTraceEffectTransformation transformation)
            (runTraceEffectTransformation foreignTransformation)
            (projectEffectState @{nameEq} before) moved (generated movedPoint)
          commuted = commuteRightFromLeft (EffectStateEquivalence keyEq)
            (runTraceEffectTransformation transformation)
            (runTraceEffectTransformation foreignTransformation)
            (projectEffectState @{nameEq} before) moved (generated movedPoint)
            foreignMovedResult (generatedRuns movedPoint) commutes
          0 sameSourceGenerated : generated sourcePoint = rightInput commuted
          sameSourceGenerated = justInjective
            (trans (sym (generatedRuns sourcePoint)) (leftAtOrigin commuted))
      in
        let 0 sourceRecoveredToGenerated : EffectStateRelated keyEq
              (recovered sourcePoint) (generated sourcePoint)
            sourceRecoveredToGenerated = transitive (EffectStateEquivalence keyEq)
              (recoveredToNormalized sourcePoint) sourceNormalizedToGenerated
            0 sourceRecoveredToRightInput : EffectStateRelated keyEq
              (recovered sourcePoint) (rightInput commuted)
            sourceRecoveredToRightInput = replace
              {p = \observed => EffectStateRelated keyEq
                (recovered sourcePoint) observed}
              sameSourceGenerated sourceRecoveredToGenerated
            0 movedRecoveredToGenerated : EffectStateRelated keyEq
              (recovered movedPoint) (generated movedPoint)
            movedRecoveredToGenerated = transitive (EffectStateEquivalence keyEq)
              (recoveredToNormalized movedPoint) movedNormalizedToGenerated
            0 actualForeignGeneratedRuns : partialEffectMap
              (Fired {before = before} {afterState = afterState}
                nameEq keyEq action tag checked) (rightInput commuted) =
              Just (rightOutput commuted)
            actualForeignGeneratedRuns = trans
              (sym (actualForwardGeneratorMap before afterState nameEq keyEq
                action tag checked occurs (rightInput commuted)))
              (rightAfterLeft commuted)
            0 respected : RespectLeftResult
              (EffectState name key value world) (EffectStateEquivalence keyEq)
              (partialEffectMap
                (Fired {before = before} {afterState = afterState}
                  nameEq keyEq action tag checked))
              (recovered sourcePoint) (rightInput commuted)
              (rightOutput commuted)
            respected = respectLeftFromRight keyEq (partialEffectMap
              (Fired {before = before} {afterState = afterState}
                nameEq keyEq action tag checked))
              (partialEffectMapRespects nameEq keyEq action tag before afterState
                checked)
              (recovered sourcePoint) (rightInput commuted)
              (rightOutput commuted) sourceRecoveredToRightInput
              actualForeignGeneratedRuns
            0 movedRecoveredToForeignGenerated : EffectStateRelated keyEq
              (recovered movedPoint) (rightOutput commuted)
            movedRecoveredToForeignGenerated = transitive
              (EffectStateEquivalence keyEq) movedRecoveredToGenerated
              (outputsRelated commuted)
            0 foreignGeneratedToForeignRecovered : EffectStateRelated keyEq
              (rightOutput commuted) (leftOutput respected)
            foreignGeneratedToForeignRecovered = symmetric
              (EffectStateEquivalence keyEq) (outputsRelated respected)
            0 movedRecoveredToForeignRecovered : EffectStateRelated keyEq
              (recovered movedPoint) (leftOutput respected)
            movedRecoveredToForeignRecovered = transitive
              (EffectStateEquivalence keyEq) movedRecoveredToForeignGenerated
              foreignGeneratedToForeignRecovered
            0 movedRecoveredToTargetRecovered : EffectStateRelated keyEq
              (recovered movedPoint) (recovered targetPoint)
            movedRecoveredToTargetRecovered =
              let respectedAccumulator = accumulatorEffectMapRespects nameEq
                    keyEq selected
                    (MkAccumulatorHandle (componentProvisions component) table
                      accumulator)
                    moved (projectEffectState @{nameEq} afterState) movedToTarget
                  0 atPoint : PartialRelated
                    (EffectState name key value world) (EffectStateRelated keyEq)
                    (Just (recovered movedPoint)) (Just (recovered targetPoint))
                  atPoint = partialRelatedRewrite (accumulatorRuns movedPoint)
                    (accumulatorRuns targetPoint) respectedAccumulator
              in partialDefinedRelation atPoint
            0 targetToForeign : EffectStateRelated keyEq
              (recovered targetPoint) (leftOutput respected)
            targetToForeign = transitive (EffectStateEquivalence keyEq)
              (symmetric (EffectStateEquivalence keyEq)
                movedRecoveredToTargetRecovered)
              movedRecoveredToForeignRecovered
        in MkForeignAccumulatorStep (recovered sourcePoint)
            (recovered targetPoint) (leftOutput respected)
            (accumulatorRuns sourcePoint) (accumulatorRuns targetPoint)
            (leftRuns respected) targetToForeign
