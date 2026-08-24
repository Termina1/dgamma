module DGamma.R16EndpointControlsImpossibilityPositive

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionRelationalBoundary
import DGamma.CP4DeletionBoundaryRetained
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import Decidable.Equality
import Data.Nat

%default total

||| Extract the exact adjacent pair from an arbitrary prefix/pair/suffix
||| decomposition of a replay bundle. This is not restricted to a head pair.
0 exactPairAlignedFromBundle :
  (original : Transitions initial originalFinal) ->
  (prefixTrace : Transitions initial pairFirst) ->
  (left : Transition pairFirst pairMiddle) ->
  (right : Transition pairMiddle pairFinal) ->
  (suffix : Transitions pairFinal originalFinal) ->
  appendTransitions prefixTrace
    (MoreTransitions left (MoreTransitions right suffix)) = original ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq original ->
  AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions left (MoreTransitions right NoTransitions))
exactPairAlignedFromBundle original prefixTrace left right suffix exact premises =
  case exact of
    Refl =>
      let 0 alignedPairSuffix : AlignedTransitions name key world error value
            nameEq keyEq (MoreTransitions left (MoreTransitions right suffix))
          alignedPairSuffix = snd (alignedAppendSplit prefixTrace
            (MoreTransitions left (MoreTransitions right suffix))
            (replayAligned premises))
      in fst (alignedAppendSplit
        (MoreTransitions left (MoreTransitions right NoTransitions)) suffix
        alignedPairSuffix)

||| O/O orientation at the arbitrary current boundary selected by O6/O17.
0 exactOrchestrationPairAligned :
  (original : Transitions initial originalFinal) ->
  (prefixTrace : Transitions initial pairFirst) ->
  (left : Transition pairFirst pairMiddle) ->
  (right : Transition pairMiddle pairFinal) ->
  (suffix : Transitions pairFinal originalFinal) ->
  appendTransitions prefixTrace
    (MoreTransitions left (MoreTransitions right suffix)) = original ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq original ->
  PaperOrchestrationStep left -> PaperOrchestrationStep right ->
  AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions left (MoreTransitions right NoTransitions))
exactOrchestrationPairAligned original prefixTrace left right suffix exact premises
  leftPaper rightPaper = exactPairAlignedFromBundle original prefixTrace left right
    suffix exact premises

||| O6's whole-block producer owns the exact replay bundle used for its selected
||| crossing, so O/O source capital is extractable at any exact crossing.
0 o6OrchestrationPairCapital :
  (sourceTrace : Transitions initial sourceFinal) ->
  (prefixTrace : Transitions initial pairFirst) ->
  (left : Transition pairFirst pairMiddle) ->
  (right : Transition pairMiddle pairFinal) ->
  (suffix : Transitions pairFinal sourceFinal) ->
  appendTransitions prefixTrace
    (MoreTransitions left (MoreTransitions right suffix)) = sourceTrace ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq sourceTrace ->
  PaperOrchestrationStep left -> PaperOrchestrationStep right ->
  AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions left (MoreTransitions right NoTransitions))
o6OrchestrationPairCapital = exactOrchestrationPairAligned

||| O17 recursion retains the exact outer dictionaries in swappedPremises.
0 o17RecursiveOrchestrationPairCapital :
  (result : AdjacentSwapResult name key world error value protocol nameEq keyEq
    original oldPrefix oldLeft oldRight oldSuffix oldDiamond) ->
  (prefixTrace : Transitions initial pairFirst) ->
  (left : Transition pairFirst pairMiddle) ->
  (right : Transition pairMiddle pairFinal) ->
  (suffix : Transitions pairFinal (replayedFinal result)) ->
  appendTransitions prefixTrace
    (MoreTransitions left (MoreTransitions right suffix)) = swappedTrace result ->
  PaperOrchestrationStep left -> PaperOrchestrationStep right ->
  AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions left (MoreTransitions right NoTransitions))
o17RecursiveOrchestrationPairCapital result prefixTrace left right suffix exact
  leftPaper rightPaper = exactOrchestrationPairAligned (swappedTrace result)
    prefixTrace left right suffix exact (swappedPremises result) leftPaper
    rightPaper

||| O19 current OperationalAdjacentBlockSwap boundary owns sourcePremises.
0 o19CurrentOrchestrationPairCapital :
  {sourceOrder, targetOrder : List name} ->
  {orderSwap : AdjacentActorOrderSwap name sourceOrder targetOrder} ->
  {initial, sourceFinal : SystemState name key value world error} ->
  {sourceTrace : Transitions initial sourceFinal} ->
  {sourceBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
    sourceOrder sourceTrace} ->
  {sourcePremises : ReplayInvariantBundle name key world error value protocol
    nameEq keyEq sourceTrace} ->
  {safety : AdjacentActorSwapSafety name key world error value protocol nameEq
    keyEq orderSwap sourceTrace sourceBlocks sourcePremises} ->
  OperationalAdjacentBlockSwap name key world error value protocol nameEq keyEq
    orderSwap sourceTrace sourceBlocks sourcePremises safety ->
  (prefixTrace : Transitions initial pairFirst) ->
  (left : Transition pairFirst pairMiddle) ->
  (right : Transition pairMiddle pairFinal) ->
  (suffix : Transitions pairFinal sourceFinal) ->
  appendTransitions prefixTrace
    (MoreTransitions left (MoreTransitions right suffix)) = sourceTrace ->
  PaperOrchestrationStep left -> PaperOrchestrationStep right ->
  AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions left (MoreTransitions right NoTransitions))
o19CurrentOrchestrationPairCapital {sourceTrace} {sourcePremises} step prefixTrace
  left right suffix exact leftPaper rightPaper = exactOrchestrationPairAligned
    sourceTrace prefixTrace left right suffix exact sourcePremises leftPaper
    rightPaper

||| O19 recursion receives the exact bundle produced by the block swap.
0 o19RecursiveOrchestrationPairCapital :
  {sourceOrder, targetOrder : List name} ->
  {orderSwap : AdjacentActorOrderSwap name sourceOrder targetOrder} ->
  {initial, sourceFinal : SystemState name key value world error} ->
  {sourceTrace : Transitions initial sourceFinal} ->
  {sourceBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
    sourceOrder sourceTrace} ->
  {sourcePremises : ReplayInvariantBundle name key world error value protocol
    nameEq keyEq sourceTrace} ->
  {safety : AdjacentActorSwapSafety name key world error value protocol nameEq
    keyEq orderSwap sourceTrace sourceBlocks sourcePremises} ->
  (step : OperationalAdjacentBlockSwap name key world error value protocol nameEq
    keyEq orderSwap sourceTrace sourceBlocks sourcePremises safety) ->
  (prefixTrace : Transitions initial pairFirst) ->
  (left : Transition pairFirst pairMiddle) ->
  (right : Transition pairMiddle pairFinal) ->
  (suffix : Transitions pairFinal (blockSwapFinal step)) ->
  appendTransitions prefixTrace
    (MoreTransitions left (MoreTransitions right suffix)) = blockSwapTrace step ->
  PaperOrchestrationStep left -> PaperOrchestrationStep right ->
  AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions left (MoreTransitions right NoTransitions))
o19RecursiveOrchestrationPairCapital step prefixTrace left right suffix exact
  leftPaper rightPaper = exactOrchestrationPairAligned (blockSwapTrace step)
    prefixTrace left right suffix exact (blockSwapPremises step) leftPaper
    rightPaper

||| O19's initial sealed canonical realization retains the theorem dictionaries.
0 o19InitialOrchestrationPairCapital :
  (capital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq original) ->
  (prefixTrace : Transitions initial pairFirst) ->
  (left : Transition pairFirst pairMiddle) ->
  (right : Transition pairMiddle pairFinal) ->
  (suffix : Transitions pairFinal
    (canonicalFinal (canonicalSchedule capital))) ->
  appendTransitions prefixTrace
    (MoreTransitions left (MoreTransitions right suffix)) =
      canonicalTrace (canonicalSchedule capital) ->
  PaperOrchestrationStep left -> PaperOrchestrationStep right ->
  AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions left (MoreTransitions right NoTransitions))
o19InitialOrchestrationPairCapital capital prefixTrace left right suffix exact
  leftPaper rightPaper = exactOrchestrationPairAligned
    (canonicalTrace (canonicalSchedule capital)) prefixTrace left right suffix
    exact (canonicalReplayPremises capital) leftPaper rightPaper

||| O19's selected target is sealed with the same exact replay dictionaries.
0 o19TargetOrchestrationPairCapital :
  (selected : CertifiedOperationalCanonicalPermutation name key world error value
    protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital
    matching) ->
  (prefixTrace : Transitions initial pairFirst) ->
  (left : Transition pairFirst pairMiddle) ->
  (right : Transition pairMiddle pairFinal) ->
  (suffix : Transitions pairFinal (operationalTargetFinal selected)) ->
  appendTransitions prefixTrace
    (MoreTransitions left (MoreTransitions right suffix)) =
      operationalTargetTrace selected ->
  PaperOrchestrationStep left -> PaperOrchestrationStep right ->
  AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions left (MoreTransitions right NoTransitions))
o19TargetOrchestrationPairCapital selected prefixTrace left right suffix exact
  leftPaper rightPaper = exactOrchestrationPairAligned
    (operationalTargetTrace selected) prefixTrace left right suffix exact
    (operationalTargetPremises selected) leftPaper rightPaper

||| Full genuine producer: the old OrchestrationSwapSafety is constructed with
||| an early transition evaluated under the outer dictionaries, and the new
||| dependent singleton is built for exactly earlyRight safety. No equality of
||| executable DecEq dictionaries is assumed.
0 outerProducerCallsO5 :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {first, middle, originalFinal, earlyFinal :
    SystemState name key value world error} ->
  (left : Transition first middle) ->
  (right : Transition middle originalFinal) ->
  (0 sourceAligned : AlignedTransitions name key world error value nameEq keyEq
    (MoreTransitions left (MoreTransitions right NoTransitions))) ->
  PaperOrchestrationStep left -> PaperOrchestrationStep right ->
  Not (transitionActor left = transitionActor right) ->
  (earlyChecked : checkedApplyAction @{nameEq} @{keyEq}
    (transitionAction right) first =
      Just (transitionTag right, earlyFinal)) ->
  (sourceDiscipline : RegistrationDiscipline protocol nameEq
    (MoreTransitions left (MoreTransitions right NoTransitions))) ->
  (startOrdinal : Nat) -> (startLive : GenerationEnvironment name) ->
  (endOrdinal : Nat) -> (endLive : GenerationEnvironment name) ->
  GenerationTraceScan nameEq startOrdinal startLive
    (MoreTransitions left (MoreTransitions right NoTransitions))
    endOrdinal endLive ->
  ((leftChild, rightChild : name) ->
    (leftParent, rightParent : Parent name) ->
    (leftComponent, rightComponent : Component key value world error) ->
    transitionAction left = OInsert leftChild leftParent leftComponent ->
    transitionAction right = OInsert rightChild rightParent rightComponent ->
    Not (leftChild = rightChild)) ->
  ((leftChild, leftParent, rightChild, rightParent : name) ->
    (leftComponent, rightComponent : Component key value world error) ->
    transitionAction left =
      OInsert leftChild (ChildOf leftParent) leftComponent ->
    transitionAction right =
      OInsert rightChild (ChildOf rightParent) rightComponent ->
    (Not (leftChild = rightParent), Not (rightChild = leftParent))) ->
  LocalRelationalDiamond name key world error value nameEq keyEq left right
outerProducerCallsO5 nameEq keyEq protocol left right sourceAligned leftPaper
  rightPaper distinct earlyChecked sourceDiscipline startOrdinal startLive
  endOrdinal endLive scan insertedDistinct licenses =
    let early : Transition first earlyFinal
        early = Fired nameEq keyEq (transitionAction right)
          (transitionTag right) earlyChecked
        safety : OrchestrationSwapSafety name key world error value protocol
          nameEq keyEq left right
        safety = MkOrchestrationSwapSafety earlyFinal early Refl Refl
          sourceDiscipline startOrdinal startLive endOrdinal endLive scan
          insertedDistinct licenses
        0 earlyAligned : AlignedTransitions name key world error value nameEq
          keyEq (MoreTransitions (earlyRight safety) NoTransitions)
        earlyAligned = AlignedStep (transitionAction right) (transitionTag right)
          earlyChecked NoTransitions AlignedEnd
    in orchestrationOrchestrationDiamondSpike nameEq keyEq protocol left right
      sourceAligned leftPaper rightPaper distinct safety earlyAligned

||| Historical pin of revision 16's retired endpoint. Keeping the ordered field
||| local preserves the constructive Void evidence without re-exporting it into
||| the repaired research interface.
record RetiredOrderedReplayEndpoint
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (sourceFinal, replayedFinal : SystemState name key value world error) where
  constructor MkRetiredOrderedReplayEndpoint
  0 retiredReplayedEffects : EffectStateRelated keyEq
    (projectEffectState @{nameEq} sourceFinal)
    (projectEffectState @{nameEq} replayedFinal)
  0 retiredReplayedControls : OrderedRegistryControlsRelated name key world
    error value (bindings (registry sourceFinal))
      (bindings (registry replayedFinal))
  0 retiredReplayedWellFormed :
    registryWellFormed @{nameEq} @{keyEq} replayedFinal = True

||| Structural inversion of OrderedRegistryControlsRelated: two lists whose
||| distinct actors are transposed at their heads cannot be related.
0 transposedDistinctHeadsCannotRelate :
  (leftActor, rightActor : name) -> Not (leftActor = rightActor) ->
  (leftFiber, rightFiber : Fiber name key value world error) ->
  (leftRest, rightRest : List (Binding name
    (FiberAt name key value world error))) ->
  OrderedRegistryControlsRelated name key world error value
    (Bind rightActor rightFiber :: leftRest)
    (Bind leftActor leftFiber :: rightRest) -> Void
transposedDistinctHeadsCannotRelate actor actor distinct leftFiber rightFiber
  leftRest rightRest (OrderedControlsCons actor relation rest) = distinct Refl

||| A successful checked insertion exposes a prepended binding head.
0 checkedInsertBindings :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor : name) -> (parent : Parent name) ->
  (component : Component key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq}
    (OInsert actor parent component) before = Just (tag, afterState)) ->
  bindings (registry afterState) =
    Bind actor (freshFiber component parent) :: bindings (registry before)
checkedInsertBindings nameEq keyEq actor parent component
  before@(MkSystemState ambient source) afterState checked =
    insertObservedBindings (insertRuntimeObservation nameEq keyEq actor parent
      component ambient source tag afterState
      (checkedActionProjects nameEq keyEq (OInsert actor parent component)
        before afterState tag checked))

||| Re-derivation against the actual checked evaluator: left-then-right has
||| right::left heads, while right-then-left has left::right heads, so the
||| retired ordered relation is uninhabitable for distinct actors.
0 checkedInsertSwapEndpointControlsImpossible :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, middle, originalFinal, earlyFinal, swappedFinal :
    SystemState name key value world error} ->
  (leftActor, rightActor : name) -> Not (leftActor = rightActor) ->
  (leftParent, rightParent : Parent name) ->
  (leftComponent, rightComponent : Component key value world error) ->
  (leftChecked : checkedApplyAction @{nameEq} @{keyEq}
    (OInsert leftActor leftParent leftComponent) first =
      Just (leftTag, middle)) ->
  (rightChecked : checkedApplyAction @{nameEq} @{keyEq}
    (OInsert rightActor rightParent rightComponent) middle =
      Just (rightTag, originalFinal)) ->
  (earlyChecked : checkedApplyAction @{nameEq} @{keyEq}
    (OInsert rightActor rightParent rightComponent) first =
      Just (earlyTag, earlyFinal)) ->
  (movedChecked : checkedApplyAction @{nameEq} @{keyEq}
    (OInsert leftActor leftParent leftComponent) earlyFinal =
      Just (movedTag, swappedFinal)) ->
  OrderedRegistryControlsRelated name key world error value
    (bindings (registry originalFinal))
    (bindings (registry swappedFinal)) -> Void
checkedInsertSwapEndpointControlsImpossible nameEq keyEq
  {first} {middle} {originalFinal} {earlyFinal} {swappedFinal}
  leftActor rightActor distinct leftParent rightParent leftComponent
  rightComponent leftChecked rightChecked earlyChecked movedChecked related =
    let 0 leftShape : Equal (bindings (registry middle))
          (Bind leftActor (freshFiber leftComponent leftParent) ::
            bindings (registry first))
        leftShape = checkedInsertBindings nameEq keyEq leftActor leftParent
          leftComponent first middle leftChecked
        0 originalHead : Equal (bindings (registry originalFinal))
          (Bind rightActor (freshFiber rightComponent rightParent) ::
            Bind leftActor (freshFiber leftComponent leftParent) ::
              bindings (registry first))
        originalHead = trans
          (checkedInsertBindings nameEq keyEq rightActor rightParent
            rightComponent middle originalFinal rightChecked)
          (cong (Bind rightActor (freshFiber rightComponent rightParent) ::)
            leftShape)
        0 earlyShape : Equal (bindings (registry earlyFinal))
          (Bind rightActor (freshFiber rightComponent rightParent) ::
            bindings (registry first))
        earlyShape = checkedInsertBindings nameEq keyEq rightActor rightParent
          rightComponent first earlyFinal earlyChecked
        0 swappedHead : Equal (bindings (registry swappedFinal))
          (Bind leftActor (freshFiber leftComponent leftParent) ::
            Bind rightActor (freshFiber rightComponent rightParent) ::
              bindings (registry first))
        swappedHead = trans
          (checkedInsertBindings nameEq keyEq leftActor leftParent leftComponent
            earlyFinal swappedFinal movedChecked)
          (cong (Bind leftActor (freshFiber leftComponent leftParent) ::)
            earlyShape)
    in replace
      {p = \leftEntries => OrderedRegistryControlsRelated name key world error
        value leftEntries (bindings (registry swappedFinal)) -> Void}
      (sym originalHead)
      (replace
        {p = \rightEntries => OrderedRegistryControlsRelated name key world error
          value
          (Bind rightActor (freshFiber rightComponent rightParent) ::
            Bind leftActor (freshFiber leftComponent leftParent) ::
              bindings (registry first)) rightEntries -> Void}
        (sym swappedHead)
        (transposedDistinctHeadsCannotRelate leftActor rightActor distinct
          (freshFiber leftComponent leftParent)
          (freshFiber rightComponent rightParent)
          (Bind leftActor (freshFiber leftComponent leftParent) ::
            bindings (registry first))
          (Bind rightActor (freshFiber rightComponent rightParent) ::
            bindings (registry first)))) related

||| The unchanged suffix-replay endpoint still asks for the same impossible
||| ordered relation when no suffix changes the local swapped endpoint.
0 emptySuffixReplayEndpointImpossible :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {first, middle, originalFinal, earlyFinal, swappedFinal :
    SystemState name key value world error} ->
  (leftActor, rightActor : name) -> Not (leftActor = rightActor) ->
  (leftParent, rightParent : Parent name) ->
  (leftComponent, rightComponent : Component key value world error) ->
  (leftChecked : checkedApplyAction @{nameEq} @{keyEq}
    (OInsert leftActor leftParent leftComponent) first =
      Just (leftTag, middle)) ->
  (rightChecked : checkedApplyAction @{nameEq} @{keyEq}
    (OInsert rightActor rightParent rightComponent) middle =
      Just (rightTag, originalFinal)) ->
  (earlyChecked : checkedApplyAction @{nameEq} @{keyEq}
    (OInsert rightActor rightParent rightComponent) first =
      Just (earlyTag, earlyFinal)) ->
  (movedChecked : checkedApplyAction @{nameEq} @{keyEq}
    (OInsert leftActor leftParent leftComponent) earlyFinal =
      Just (movedTag, swappedFinal)) ->
  RetiredOrderedReplayEndpoint name key world error value nameEq keyEq
    originalFinal swappedFinal -> Void
emptySuffixReplayEndpointImpossible nameEq keyEq leftActor rightActor distinct
  leftParent rightParent leftComponent rightComponent leftChecked rightChecked
  earlyChecked movedChecked endpoint =
    checkedInsertSwapEndpointControlsImpossible nameEq keyEq leftActor rightActor
      distinct leftParent rightParent leftComponent rightComponent leftChecked
      rightChecked earlyChecked movedChecked (retiredReplayedControls endpoint)

||| A two-node source trace has no located occurrence at ordinal two.
0 twoNodeTraceHasNoOrdinalTwo :
  (occurrence : LocatedActionOccurrence action
    (MoreTransitions firstStep (MoreTransitions secondStep NoTransitions))) ->
  locatedActionOrdinal occurrence = 2 -> Void
twoNodeTraceHasNoOrdinalTwo
  (MkLocatedActionOccurrence before after NoTransitions located suffix same
    decomposition) Refl impossible
twoNodeTraceHasNoOrdinalTwo
  (MkLocatedActionOccurrence before after
    (MoreTransitions prefixStep NoTransitions) located suffix same decomposition)
  Refl impossible
twoNodeTraceHasNoOrdinalTwo
  (MkLocatedActionOccurrence before after
    (MoreTransitions prefixStep (MoreTransitions secondPrefix NoTransitions))
    located suffix same Refl) ordinal impossible
twoNodeTraceHasNoOrdinalTwo
  (MkLocatedActionOccurrence before after
    (MoreTransitions prefixStep
      (MoreTransitions secondPrefix (MoreTransitions thirdPrefix prefixRest)))
    located suffix same Refl) ordinal impossible

0 zeroTwoRelationHasSourceTwo :
  AdjacentSwapOrdinalRelation Z (S (S Z)) sourceOrdinal ->
  sourceOrdinal = S (S Z)
zeroTwoRelationHasSourceTwo (AdjacentPrefixOrdinal LTEZero) impossible
zeroTwoRelationHasSourceTwo AdjacentMovedRightOrdinal impossible
zeroTwoRelationHasSourceTwo AdjacentMovedLeftOrdinal impossible
zeroTwoRelationHasSourceTwo (AdjacentSuffixOrdinal after) = Refl

data ReviewTraceEmpty : Transitions first finalState -> Type where
  ReviewNoTransitions : ReviewTraceEmpty NoTransitions

0 reviewTraceEmptyFinalSame :
  (trace : Transitions first finalState) -> ReviewTraceEmpty trace ->
  finalState = first
reviewTraceEmptyFinalSame NoTransitions ReviewNoTransitions = Refl

||| The accepted operational ordinal contract prevents an implementation from
||| hiding extra steps after a swapped pair when the source suffix is empty.
0 pairFoldForcesEmptyReplayedSuffix :
  (left : Transition first middle) ->
  (right : Transition middle originalFinal) ->
  (movedRight : Transition first swappedMiddle) ->
  (movedLeft : Transition swappedMiddle swappedFinal) ->
  (replayedSuffix : Transitions swappedFinal replayedFinal) ->
  (swappedTrace : Transitions first replayedFinal) ->
  (fold : AdjacentSwapOperationalOccurrenceFold name key world error value
    (MoreTransitions left (MoreTransitions right NoTransitions)) NoTransitions
    left right NoTransitions movedRight movedLeft replayedSuffix swappedTrace) ->
  ReviewTraceEmpty replayedSuffix
pairFoldForcesEmptyReplayedSuffix left right movedRight movedLeft NoTransitions
  swappedTrace fold = ReviewNoTransitions
pairFoldForcesEmptyReplayedSuffix left right movedRight movedLeft
  (MoreTransitions extra rest) swappedTrace fold =
    let explicit : Transitions first replayedFinal
        explicit = MoreTransitions movedRight
          (MoreTransitions movedLeft (MoreTransitions extra rest))
        atThirdExplicit : LocatedActionOccurrence (transitionAction extra) explicit
        atThirdExplicit = MkLocatedActionOccurrence _ _
          (MoreTransitions movedRight (MoreTransitions movedLeft NoTransitions))
          extra rest Refl Refl
    in case operationalSwappedDecomposition fold of
      Refl =>
        let relation = operationalOrdinalRelation fold atThirdExplicit
            0 sourceAtTwo : Equal
              (locatedActionOrdinal
                (replayActionOrigin (operationalOccurrenceCorrespondence fold)
                  atThirdExplicit)) (S (S Z))
            sourceAtTwo = zeroTwoRelationHasSourceTwo relation
        in void (twoNodeTraceHasNoOrdinalTwo
          (replayActionOrigin (operationalOccurrenceCorrespondence fold)
            atThirdExplicit) sourceAtTwo)

||| Historical revision-16 statement, now self-contained: adding the retired
||| ordered endpoint to a genuine suffix-free distinct OInsert/OInsert result is
||| impossible. The current result itself carries only ControlEquivalent.
0 suffixFreeInsertSwapResultImpossible :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {first, middle, originalFinal : SystemState name key value world error} ->
  (leftActor, rightActor : name) -> Not (leftActor = rightActor) ->
  (leftParent, rightParent : Parent name) ->
  (leftComponent, rightComponent : Component key value world error) ->
  (leftChecked : checkedApplyAction @{nameEq} @{keyEq}
    (OInsert leftActor leftParent leftComponent) first =
      Just (leftTag, middle)) ->
  (rightChecked : checkedApplyAction @{nameEq} @{keyEq}
    (OInsert rightActor rightParent rightComponent) middle =
      Just (rightTag, originalFinal)) ->
  {left : Transition first middle} ->
  {right : Transition middle originalFinal} ->
  (leftShape : left = Fired nameEq keyEq
    (OInsert leftActor leftParent leftComponent) leftTag leftChecked) ->
  (rightShape : right = Fired nameEq keyEq
    (OInsert rightActor rightParent rightComponent) rightTag rightChecked) ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq
    left right) ->
  (earlyChecked : checkedApplyAction @{nameEq} @{keyEq}
    (OInsert rightActor rightParent rightComponent) first =
      Just (earlyTag, swappedMiddle diamond)) ->
  (movedChecked : checkedApplyAction @{nameEq} @{keyEq}
    (OInsert leftActor leftParent leftComponent) (swappedMiddle diamond) =
      Just (movedTag, swappedFinal diamond)) ->
  (result : AdjacentSwapResult name key world error value protocol nameEq keyEq
    (MoreTransitions left (MoreTransitions right NoTransitions)) NoTransitions
    left right NoTransitions diamond) ->
  (retiredEndpoint : RetiredOrderedReplayEndpoint name key world error value
    nameEq keyEq originalFinal (replayedFinal result)) -> Void
suffixFreeInsertSwapResultImpossible nameEq keyEq protocol leftActor rightActor
  distinct leftParent rightParent leftComponent rightComponent leftChecked
  rightChecked {left} {right} leftShape rightShape diamond earlyChecked
  movedChecked result retiredEndpoint = case leftShape of
    Refl => case rightShape of
      Refl =>
        let fold = swappedOccurrenceFold result
            empty = pairFoldForcesEmptyReplayedSuffix
              (Fired nameEq keyEq (OInsert leftActor leftParent leftComponent)
                leftTag leftChecked)
              (Fired nameEq keyEq (OInsert rightActor rightParent rightComponent)
                rightTag rightChecked)
              (movedRight diamond) (movedLeft diamond) (replayedSuffix result)
              (swappedTrace result) fold
            0 finalSame : Equal (replayedFinal result) (swappedFinal diamond)
            finalSame = reviewTraceEmptyFinalSame (replayedSuffix result) empty
            0 endpointAtSwap : RetiredOrderedReplayEndpoint name key world error
              value nameEq keyEq originalFinal (swappedFinal diamond)
            endpointAtSwap = replace
              {p = \target => RetiredOrderedReplayEndpoint name key world error
                value nameEq keyEq originalFinal target}
              finalSame retiredEndpoint
        in emptySuffixReplayEndpointImpossible nameEq keyEq leftActor rightActor
          distinct leftParent rightParent leftComponent rightComponent leftChecked
          rightChecked earlyChecked movedChecked endpointAtSwap
