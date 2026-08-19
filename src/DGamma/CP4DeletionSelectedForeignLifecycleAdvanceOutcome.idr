module DGamma.CP4DeletionSelectedForeignLifecycleAdvanceOutcome

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionSelectedEffectCore
import DGamma.CP4RecoveryAccumulator
import DGamma.CP4RecoveryEffectRespect
import DGamma.CP4RecoveryForeignCommute
import DGamma.CP4RecoveryTrace
import DGamma.Unified
import Decidable.Equality

%default total

||| Generated selected transformation point corresponding to one accumulator
||| replay boundary.  The selected accumulator's trailing normalization is
||| observational identity on its confined generated table, so the independently
||| constructed survivor is related directly to the generated point consumed by
||| Equation 55.
public export
record SelectedBoundaryGeneratedOrigin
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (selected : name)
  {wholeFirst, wholeLast : SystemState name key value world error}
  (whole : Transitions wholeFirst wholeLast)
  (original, survivor : SystemState name key value world error)
  (boundary : SelectedEffectReplayBoundary name key world error value nameEq
    keyEq selected whole original survivor) where
  constructor MkSelectedBoundaryGeneratedOrigin
  boundaryGenerated : EffectState name key value world
  0 boundaryGeneratedRuns : runTraceEffectTransformation
    (modelTransformation (selectedBoundaryModel boundary))
    (projectEffectState @{nameEq} original) = Just boundaryGenerated
  0 boundarySurvivorToGenerated : EffectStateRelated keyEq
    (projectEffectState @{nameEq} survivor) boundaryGenerated

public export
0 selectedBoundaryGeneratedOrigin :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (whole : Transitions wholeFirst wholeLast) ->
  {original, survivor : SystemState name key value world error} ->
  (boundary : SelectedEffectReplayBoundary name key world error value nameEq
    keyEq selected whole original survivor) ->
  SelectedBoundaryGeneratedOrigin name key world error value nameEq keyEq
    selected whole original survivor boundary
selectedBoundaryGeneratedOrigin {name} {key} {world} {error} {value}
  nameEq keyEq selected whole
  boundary@(MkSelectedEffectReplayBoundary
    model@(MkAccumulatorModel
      fiber@(MkFiber component parent retiredFlag table lifecycle) found
      accumulator installed transformation factorization confinement)
    recovered boundaryRuns survivorToRecovered) =
      let point = buildAccumulatorFactorPoint nameEq keyEq selected
            (componentProvisions component) accumulator transformation
            factorization (projectEffectState @{nameEq} original)
          0 recoveredSame : (recovered =
            DGamma.CP4RecoveryForeignCommute.AccumulatorFactorPoint.recovered
              point)
          recoveredSame = justInjective (trans (sym boundaryRuns)
            (accumulatorRuns point))
          0 survivorToPointRecovered : EffectStateRelated keyEq
            (projectEffectState @{nameEq} survivor)
            (DGamma.CP4RecoveryForeignCommute.AccumulatorFactorPoint.recovered
              point)
          survivorToPointRecovered = replace
            {p = \observed => EffectStateRelated keyEq
              (projectEffectState @{nameEq} survivor) observed}
            recoveredSame survivorToRecovered
          0 sourceConfined : ActorEffectTableConfined selected
            (componentProvisions component)
            (projectEffectState @{nameEq} original)
          sourceConfined = projectedModelTableConfined nameEq selected original
            fiber found
          0 generatedConfined : ActorEffectTableConfined selected
            (componentProvisions component) (generated point)
          generatedConfined = confinement
            (projectEffectState @{nameEq} original) (generated point)
            sourceConfined (generatedRuns point)
          0 normalizedToGenerated : EffectStateRelated keyEq
            (normalized point) (generated point)
          normalizedToGenerated = factorPointNormalizationIdentity nameEq keyEq
            selected (componentProvisions component) accumulator transformation
            (projectEffectState @{nameEq} original) point generatedConfined
          0 survivorToGenerated : EffectStateRelated keyEq
            (projectEffectState @{nameEq} survivor) (generated point)
          survivorToGenerated = transitive (EffectStateEquivalence keyEq)
            survivorToPointRecovered
            (transitive (EffectStateEquivalence keyEq)
              (recoveredToNormalized point) normalizedToGenerated)
      in MkSelectedBoundaryGeneratedOrigin (generated point)
        (generatedRuns point) survivorToGenerated

0 partialMapsEquivalentTransitive :
  (eq : Equivalence state) ->
  PartialMapsEquivalent eq first middle ->
  PartialMapsEquivalent eq middle finalMap ->
  PartialMapsEquivalent eq first finalMap
partialMapsEquivalentTransitive eq firstToMiddle middleToFinal input =
  partialTransitive eq (firstToMiddle input) (middleToFinal input)

0 outcomeStableAtDefined :
  (stage : IteratorStage name key world error value actor trace) ->
  (foreign : PartialEffectMap name key value world) ->
  (origin, moved : EffectState name key value world) ->
  foreign origin = Just moved ->
  IteratorOutcomeStableUnder keyEq stage foreign origin ->
  IteratorOutcomeAgreement name key value world error keyEq
    (iteratorStageOutcome stage moved) (iteratorStageOutcome stage origin)
outcomeStableAtDefined stage foreign origin moved defined stable
  with (foreign origin) proof observed
  outcomeStableAtDefined stage foreign origin moved defined stable | Nothing =
    void (nothingIsNotJust defined)
  outcomeStableAtDefined stage foreign origin moved defined stable |
    Just actual =
      let 0 actualIsMoved : (actual = moved)
          actualIsMoved = justInjective defined
      in replace
        {p = \candidate => IteratorOutcomeAgreement name key value world error
          keyEq (iteratorStageOutcome stage candidate)
          (iteratorStageOutcome stage origin)}
        actualIsMoved stable

||| Outcome agreement composes without weakening either observable failures or
||| successful inverse/continuation clauses.
public export
0 iteratorOutcomeAgreementTransitive :
  IteratorOutcomeAgreement name key value world error keyEq first middle ->
  IteratorOutcomeAgreement name key value world error keyEq middle finalOutcome ->
  IteratorOutcomeAgreement name key value world error keyEq first finalOutcome
iteratorOutcomeAgreementTransitive IteratorOutcomesUndefined
  IteratorOutcomesUndefined = IteratorOutcomesUndefined
iteratorOutcomeAgreementTransitive
  (IteratorFailuresAgree firstError)
  (IteratorFailuresAgree secondError) =
    IteratorFailuresAgree (trans firstError secondError)
iteratorOutcomeAgreementTransitive
  (IteratorSuccessfulYieldsAgree firstContinuation firstUndo)
  (IteratorSuccessfulYieldsAgree secondContinuation secondUndo) =
    IteratorSuccessfulYieldsAgree
      (trans firstContinuation secondContinuation)
      (partialMapsEquivalentTransitive (EffectStateEquivalence keyEq)
        firstUndo secondUndo)

localEffectInput :
  (nameEq : DecEq name) -> (actor : name) ->
  LocalState key value world provision -> EffectState name key value world
localEffectInput nameEq actor input = MkEffectState (localWorld input)
  (\candidate => case decEq @{nameEq} candidate actor of
    Yes Refl => ownedValues (localTable input)
    No _ => emptyContext)

0 localEffectInputTableSelf :
  (nameEq : DecEq name) -> (actor : name) ->
  (input : LocalState key value world provision) ->
  effectTables (localEffectInput nameEq actor input) actor =
    ownedValues (localTable input)
localEffectInputTableSelf nameEq actor input
  with (decEq @{nameEq} actor actor)
  localEffectInputTableSelf nameEq actor input | Yes Refl = Refl
  localEffectInputTableSelf nameEq actor input | No contra = void (contra Refl)

0 partialRelatedAtEqualResults :
  leftBefore = leftAfter -> rightBefore = rightAfter ->
  PartialRelated state relation leftBefore rightBefore ->
  PartialRelated state relation leftAfter rightAfter
partialRelatedAtEqualResults Refl Refl related = related

0 setTableAmbientAdvance :
  {name, key, world : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (actor : name) ->
  (table : CoeffectContext key value) ->
  (state : EffectState name key value world) ->
  effectAmbient (setEffectTable @{nameEq} actor table state) =
    effectAmbient state
setTableAmbientAdvance nameEq actor table (MkEffectState ambient tables) = Refl

0 setTableSelfAdvance :
  {name, key, world : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (actor : name) ->
  (table : CoeffectContext key value) ->
  (state : EffectState name key value world) ->
  effectTables (setEffectTable @{nameEq} actor table state) actor = table
setTableSelfAdvance nameEq actor table state
  with (decEq @{nameEq} actor actor)
  setTableSelfAdvance nameEq actor table state | Yes Refl = Refl
  setTableSelfAdvance nameEq actor table state | No contra = void (contra Refl)

||| Equation-55 equivalence of two yielded full-state inverse maps projects
||| back to the exact runtime local-state relation required by the lifecycle
||| accumulator control.  Both maps receive the corrected Definition-60
||| normalized actor table.
public export
0 yieldedMapsGiveLocalUndoRuntimeRelated :
  {name, key, world : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (provision : CoeffectSpec key) ->
  (leftUndo, rightUndo : LocalState key value world provision ->
    LocalState key value world provision) ->
  PartialMapsEquivalent (EffectStateEquivalence keyEq)
    (yieldedInverseEffectMap nameEq keyEq actor provision leftUndo)
    (yieldedInverseEffectMap nameEq keyEq actor provision rightUndo) ->
  (input : LocalState key value world provision) ->
  LocalStateRuntimeRelated
    (leftUndo (normalizeLocal @{keyEq} provision input))
    (rightUndo (normalizeLocal @{keyEq} provision input))
yieldedMapsGiveLocalUndoRuntimeRelated {name} {key} {value} {world}
  nameEq keyEq actor provision leftUndo rightUndo maps input with (decEq @{nameEq} actor actor) proof actorDecision
  yieldedMapsGiveLocalUndoRuntimeRelated {name} {key} {value} {world}
    nameEq keyEq actor provision leftUndo rightUndo maps input | No contra = void (contra Refl)
  yieldedMapsGiveLocalUndoRuntimeRelated {name} {key} {value} {world}
    nameEq keyEq actor provision leftUndo rightUndo maps input | Yes Refl =
      let effectInput : EffectState name key value world
          effectInput = localEffectInput nameEq actor input
          leftRestored : LocalState key value world provision
          leftRestored = leftUndo (normalizeLocal @{keyEq} provision input)
          rightRestored : LocalState key value world provision
          rightRestored = rightUndo (normalizeLocal @{keyEq} provision input)
          leftOutput : EffectState name key value world
          leftOutput = setEffectTable @{nameEq} actor
            (ownedValues (localTable leftRestored))
            (setEffectAmbient (localWorld leftRestored) effectInput)
          rightOutput : EffectState name key value world
          rightOutput = setEffectTable @{nameEq} actor
            (ownedValues (localTable rightRestored))
            (setEffectAmbient (localWorld rightRestored) effectInput)
          0 normalizedInput :
            (MkLocalState (effectAmbient effectInput)
                (restrictOwnedPreservingOrder @{keyEq} provision
                  (effectTables effectInput actor)) =
             normalizeLocal @{keyEq} provision input)
          normalizedInput = rewrite localEffectInputTableSelf nameEq actor input
            in sym (normalizeLocalExact keyEq provision input)
          0 leftRuns : yieldedInverseEffectMap nameEq keyEq actor provision
            leftUndo effectInput = Just leftOutput
          leftRuns = rewrite normalizedInput in Refl
          0 rightRuns : yieldedInverseEffectMap nameEq keyEq actor provision
            rightUndo effectInput = Just rightOutput
          rightRuns = rewrite normalizedInput in Refl
          0 atInput : PartialRelated (EffectState name key value world)
            (EffectStateRelated keyEq) (Just leftOutput) (Just rightOutput)
          atInput = partialRelatedAtEqualResults leftRuns rightRuns
            (maps effectInput)
          0 outputs : EffectStateRelated keyEq leftOutput rightOutput
          outputs = case atInput of PartialDefined related => related
          0 leftAmbient : effectAmbient leftOutput = localWorld leftRestored
          leftAmbient = setTableAmbientAdvance nameEq actor
            (ownedValues (localTable leftRestored))
            (setEffectAmbient (localWorld leftRestored) effectInput)
          0 rightAmbient : effectAmbient rightOutput = localWorld rightRestored
          rightAmbient = setTableAmbientAdvance nameEq actor
            (ownedValues (localTable rightRestored))
            (setEffectAmbient (localWorld rightRestored) effectInput)
          0 localAmbient : localWorld leftRestored = localWorld rightRestored
          localAmbient = trans (sym leftAmbient)
            (trans (ambientExact outputs) rightAmbient)
          0 leftTable : effectTables leftOutput actor =
            ownedValues (localTable leftRestored)
          leftTable = setTableSelfAdvance nameEq actor
            (ownedValues (localTable leftRestored))
            (setEffectAmbient (localWorld leftRestored) effectInput)
          0 rightTable : effectTables rightOutput actor =
            ownedValues (localTable rightRestored)
          rightTable = setTableSelfAdvance nameEq actor
            (ownedValues (localTable rightRestored))
            (setEffectAmbient (localWorld rightRestored) effectInput)
          0 localTables : bindings (ownedValues (localTable leftRestored)) =
            bindings (ownedValues (localTable rightRestored))
          localTables = trans (cong bindings (sym leftTable))
            (trans (tablesExact outputs actor) (cong bindings rightTable))
      in MkLocalStateRuntimeRelated localAmbient localTables

||| Instantiate repaired Equation 55 at a retained foreign L-Advance boundary.
||| The first leg transports the stage from the runtime-related survivor to the
||| selected generated point; the second is the public cross-actor independence
||| witness from that point back to the actual original state.
public export
0 foreignAdvanceOutcomeAgreement :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected, actor : name) -> Not (actor = selected) ->
  (whole : Transitions wholeFirst wholeLast) ->
  TraceIndependent name key world error value keyEq whole ->
  {original, survivor : SystemState name key value world error} ->
  (boundary : SelectedEffectReplayBoundary name key world error value nameEq
    keyEq selected whole original survivor) ->
  (stage : IteratorStage name key world error value actor whole) ->
  IteratorOutcomeAgreement name key value world error keyEq
    (iteratorStageOutcome stage (projectEffectState @{nameEq} survivor))
    (iteratorStageOutcome stage (projectEffectState @{nameEq} original))
foreignAdvanceOutcomeAgreement nameEq keyEq selected actor actorDistinct whole
  independent {original} {survivor} boundary stage =
    case selectedBoundaryGeneratedOrigin nameEq keyEq selected whole boundary of
      MkSelectedBoundaryGeneratedOrigin generated generatedRuns
        survivorToGenerated =>
          let 0 survivorToPoint = iteratorStageOutcomeRelated keyEq stage
                (projectEffectState @{nameEq} survivor) generated
                survivorToGenerated
              0 pointToOriginal : IteratorOutcomeAgreement name key value world
                error keyEq (iteratorStageOutcome stage generated)
                (iteratorStageOutcome stage
                  (projectEffectState @{nameEq} original))
              pointToOriginal = outcomeStableAtDefined stage
                (runTraceEffectTransformation
                  (modelTransformation (selectedBoundaryModel boundary)))
                (projectEffectState @{nameEq} original) generated generatedRuns
                (iteratorYieldsStable independent actor selected actorDistinct
                  stage (modelTransformation (selectedBoundaryModel boundary))
                  (projectEffectState @{nameEq} original))
          in iteratorOutcomeAgreementTransitive survivorToPoint pointToOriginal
