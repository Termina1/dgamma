module DGamma.CP5ConfluenceCrossTraceSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import Data.List
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total

||| Pure finite-list transposition.  This remains useful matching capital, but
||| revision 6 deliberately prevents a value of this type from flowing directly
||| into O20: actor distinctness alone cannot justify a local diamond.
public export
record AdjacentActorOrderSwap (name : Type)
  (before, after : List name) where
  constructor MkAdjacentActorOrderSwap
  actorPrefix : List name
  actorLeft : name
  actorRight : name
  actorSuffix : List name
  0 actorBeforeExact : before = actorPrefix ++
    (actorLeft :: actorRight :: actorSuffix)
  0 actorAfterExact : after = actorPrefix ++
    (actorRight :: actorLeft :: actorSuffix)
  0 actorDistinct : Not (actorLeft = actorRight)

public export
data CertifiedActorPermutation :
  (name : Type) -> List name -> List name -> Type where
  ActorPermutationDone : CertifiedActorPermutation name order order
  ActorPermutationStep :
    AdjacentActorOrderSwap name before middle ->
    CertifiedActorPermutation name middle after ->
    CertifiedActorPermutation name before after

||| Exact contiguous-block structure carried at every operational replay state.
public export
record ActorBlockDecomposition
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (order : List name)
  {initial, finalState : SystemState name key value world error}
  (trace : Transitions initial finalState) where
  constructor MkActorBlockDecomposition
  decomposedBlock : (n : name) -> Elem n order ->
    LocatedOpenEpisodeBlock name key world error value nameEq keyEq n trace
  decomposedBlocksFollowOrder : (earlier, later : name) ->
    (earlierIn : Elem earlier order) ->
    (laterIn : Elem later order) ->
    BeforeIn earlier later order ->
    BlockBefore name key world error value nameEq keyEq trace earlier later
      (decomposedBlock earlier earlierIn) (decomposedBlock later laterIn)
  0 decomposedOrderedBlockRangesDisjoint : (earlier, later : name) ->
    (earlierIn : Elem earlier order) ->
    (laterIn : Elem later order) ->
    BeforeIn earlier later order ->
    (earlierPosition, laterPosition : Nat) ->
    LTE (S earlierPosition)
      (S (transitionCount (blockBody (decomposedBlock earlier earlierIn)))) ->
    LTE (S laterPosition)
      (S (transitionCount (blockBody (decomposedBlock later laterIn)))) ->
    Not (transitionCount (traceBeforeBlock (decomposedBlock earlier earlierIn)) +
      earlierPosition =
      transitionCount (traceBeforeBlock (decomposedBlock later laterIn)) +
      laterPosition)
  decomposedLifecycleCoverage : LifecycleActorsCovered order trace

||| Executable negative evidence used at a whole-block boundary.  In particular,
||| if the left actor yields a registration of the right actor, O/A cannot move
||| that right lifecycle block before its own licensing O-Insert.
public export
data NoGeneratedChild :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (forbidden : name) ->
  {first, finalState : SystemState name key value world error} ->
  Transitions first finalState -> Type where
  NoGeneratedChildEnd : NoGeneratedChild forbidden NoTransitions
  NoGeneratedChildStep :
    (transition : Transition first middle) ->
    (rest : Transitions middle finalState) ->
    ((parent : name) -> (component : Component key value world error) ->
      transitionAction transition =
        OInsert forbidden (ChildOf parent) component -> Void) ->
    NoGeneratedChild forbidden rest ->
    NoGeneratedChild forbidden (MoreTransitions transition rest)

||| The parent/child licensing mutation is rejected at the one-step safety
||| boundary, before the recursive O20 theorem is available.
public export
0 generatedChildAtHeadContradictsSafety :
  (transition : Transition first middle) ->
  (rest : Transitions middle finalState) ->
  {forbidden, parent : name} ->
  {component : Component key value world error} ->
  transitionAction transition =
    OInsert forbidden (ChildOf parent) component ->
  NoGeneratedChild forbidden (MoreTransitions transition rest) -> Void
generatedChildAtHeadContradictsSafety transition rest action
  (NoGeneratedChildStep transition rest rejected safeRest) =
    rejected parent component action

||| Exact safety reconstructed for one adjacent actor pair at its current replay
||| state.  It owns the actual two blocks, their order, the full bundle, and both
||| generated-child licensing exclusions.  These fields are intentionally not
||| reducible to `actorDistinct`.
public export
record AdjacentActorSwapSafety
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {sourceOrder, targetOrder : List name}
  (orderSwap : AdjacentActorOrderSwap name sourceOrder targetOrder)
  {initial, sourceFinal : SystemState name key value world error}
  (sourceTrace : Transitions initial sourceFinal)
  (sourceBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
    sourceOrder sourceTrace)
  (sourcePremises : ReplayInvariantBundle name key world error value protocol
    nameEq keyEq sourceTrace) where
  constructor MkAdjacentActorSwapSafety
  safetyLeftInOrder : Elem (actorLeft orderSwap) sourceOrder
  safetyRightInOrder : Elem (actorRight orderSwap) sourceOrder
  safetyLeftBeforeRight : BeforeIn (actorLeft orderSwap) (actorRight orderSwap)
    sourceOrder
  safetyBlocksOrdered : BlockBefore name key world error value nameEq keyEq
    sourceTrace (actorLeft orderSwap) (actorRight orderSwap)
    (decomposedBlock sourceBlocks (actorLeft orderSwap) safetyLeftInOrder)
    (decomposedBlock sourceBlocks (actorRight orderSwap) safetyRightInOrder)
  0 safetyLeftDoesNotGenerateRight : NoGeneratedChild (actorRight orderSwap)
    (blockBody (decomposedBlock sourceBlocks (actorLeft orderSwap)
      safetyLeftInOrder))
  0 safetyRightDoesNotGenerateLeft : NoGeneratedChild (actorLeft orderSwap)
    (blockBody (decomposedBlock sourceBlocks (actorRight orderSwap)
      safetyRightInOrder))

public export
0 actorBlockTrace :
  (block : LocatedOpenEpisodeBlock name key world error value nameEq keyEq actor
    global) ->
  Transitions (blockPreStart block) (blockEnd block)
actorBlockTrace block =
  MoreTransitions (beginTransition (blockOpening block)) (blockBody block)

public export
actorBlockTransitionCount :
  LocatedOpenEpisodeBlock name key world error value nameEq keyEq actor global ->
  Nat
actorBlockTransitionCount block = S (transitionCount (blockBody block))

public export
0 successorEqualityInjective : S left = S right -> left = right
successorEqualityInjective Refl = Refl

public export
0 addLeftInjective : (start, left, right : Nat) ->
  start + left = start + right -> left = right
addLeftInjective Z left right exact = exact
addLeftInjective (S start) left right exact =
  addLeftInjective start left right (successorEqualityInjective exact)

||| Complete coordinate-injectivity package for the two exact blocks selected by
||| one safety witness.  Cross-block disjointness is producer capital of the
||| authoritative `ActorBlockDecomposition`; same-block injectivity is proved by
||| cancellation.  Together these cover all `(block,position)` combinations.
public export
record SelectedBlockCoordinateInjectivity
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {sourceOrder, targetOrder : List name}
  (orderSwap : AdjacentActorOrderSwap name sourceOrder targetOrder)
  {initial, sourceFinal : SystemState name key value world error}
  (sourceTrace : Transitions initial sourceFinal)
  (sourceBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
    sourceOrder sourceTrace)
  (sourcePremises : ReplayInvariantBundle name key world error value protocol
    nameEq keyEq sourceTrace)
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq
    keyEq orderSwap sourceTrace sourceBlocks sourcePremises) where
  constructor MkSelectedBlockCoordinateInjectivity
  0 selectedLeftPositionsInjective : (first, second : Nat) ->
    transitionCount (traceBeforeBlock (decomposedBlock sourceBlocks
      (actorLeft orderSwap) (safetyLeftInOrder safety))) + first =
    transitionCount (traceBeforeBlock (decomposedBlock sourceBlocks
      (actorLeft orderSwap) (safetyLeftInOrder safety))) + second ->
    first = second
  0 selectedRightPositionsInjective : (first, second : Nat) ->
    transitionCount (traceBeforeBlock (decomposedBlock sourceBlocks
      (actorRight orderSwap) (safetyRightInOrder safety))) + first =
    transitionCount (traceBeforeBlock (decomposedBlock sourceBlocks
      (actorRight orderSwap) (safetyRightInOrder safety))) + second ->
    first = second
  0 selectedLeftRightRangesDisjoint : (leftPosition, rightPosition : Nat) ->
    LTE (S leftPosition) (actorBlockTransitionCount (decomposedBlock sourceBlocks
      (actorLeft orderSwap) (safetyLeftInOrder safety))) ->
    LTE (S rightPosition) (actorBlockTransitionCount (decomposedBlock sourceBlocks
      (actorRight orderSwap) (safetyRightInOrder safety))) ->
    Not (transitionCount (traceBeforeBlock (decomposedBlock sourceBlocks
      (actorLeft orderSwap) (safetyLeftInOrder safety))) + leftPosition =
      transitionCount (traceBeforeBlock (decomposedBlock sourceBlocks
        (actorRight orderSwap) (safetyRightInOrder safety))) + rightPosition)
  0 selectedRightLeftRangesDisjoint : (rightPosition, leftPosition : Nat) ->
    LTE (S rightPosition) (actorBlockTransitionCount (decomposedBlock sourceBlocks
      (actorRight orderSwap) (safetyRightInOrder safety))) ->
    LTE (S leftPosition) (actorBlockTransitionCount (decomposedBlock sourceBlocks
      (actorLeft orderSwap) (safetyLeftInOrder safety))) ->
    Not (transitionCount (traceBeforeBlock (decomposedBlock sourceBlocks
      (actorRight orderSwap) (safetyRightInOrder safety))) + rightPosition =
      transitionCount (traceBeforeBlock (decomposedBlock sourceBlocks
        (actorLeft orderSwap) (safetyLeftInOrder safety))) + leftPosition)

public export
0 selectedBlockCoordinateInjectivity :
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq
    keyEq orderSwap sourceTrace sourceBlocks sourcePremises) ->
  SelectedBlockCoordinateInjectivity name key world error value protocol nameEq
    keyEq orderSwap sourceTrace sourceBlocks sourcePremises safety
selectedBlockCoordinateInjectivity {sourceBlocks} {orderSwap} safety =
  MkSelectedBlockCoordinateInjectivity
    (\first, second, exact => addLeftInjective _ first second exact)
    (\first, second, exact => addLeftInjective _ first second exact)
    (decomposedOrderedBlockRangesDisjoint sourceBlocks
      (actorLeft orderSwap) (actorRight orderSwap)
      (safetyLeftInOrder safety) (safetyRightInOrder safety)
      (safetyLeftBeforeRight safety))
    (\rightPosition, leftPosition, rightBound, leftBound, exact =>
      decomposedOrderedBlockRangesDisjoint sourceBlocks
        (actorLeft orderSwap) (actorRight orderSwap)
        (safetyLeftInOrder safety) (safetyRightInOrder safety)
        (safetyLeftBeforeRight safety) leftPosition rightPosition leftBound
        rightBound (sym exact))

||| Occurrence-authenticated label for one current adjacent node.  The current
||| occurrence is pinned to the node's exact ordinal, then mapped through the
||| composed prefix replay correspondence to the original source trace.  Its
||| source ordinal must equal the selected block's global start plus the claimed
||| block-local position.  Repeated transitions with identical actions/tags
||| therefore remain distinct.
public export
record NodeCrossesSourceBlockPosition
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {sourceInitial, sourceFinal, currentInitial, currentFinal :
    SystemState name key value world error}
  (sourceTrace : Transitions sourceInitial sourceFinal)
  (currentTrace : Transitions currentInitial currentFinal)
  (prefixOccurrences : ActionRegistrationReplayCorrespondence name key world
    error value sourceTrace currentTrace)
  {actor : name}
  (sourceBlock : LocatedOpenEpisodeBlock name key world error value nameEq keyEq
    actor sourceTrace)
  (position : Nat)
  (action : Action name key value world error)
  (currentNodeOrdinal : Nat) where
  constructor MkNodeCrossesSourceBlockPosition
  currentNodeOccurrence : LocatedActionOccurrence action currentTrace
  0 currentNodeIsExactOccurrence :
    locatedActionOrdinal currentNodeOccurrence = currentNodeOrdinal
  0 sourceNodeIsExactBlockPosition :
    locatedActionOrdinal
      (replayActionOrigin prefixOccurrences currentNodeOccurrence) =
    transitionCount (traceBeforeBlock sourceBlock) + position

public export
transitionPrefixLength : (earlierTrace : Transitions initial before) ->
  (step : Transition before after) ->
  transitionCount (appendTransitions earlierTrace
    (MoreTransitions step NoTransitions)) = S (transitionCount earlierTrace)
transitionPrefixLength NoTransitions step = Refl
transitionPrefixLength (MoreTransitions earlier rest) step =
  cong S (transitionPrefixLength rest step)

||| The current left node is located constructively from the exact decomposition
||| already stored by its `AdjacentSwapResult`.
public export
0 adjacentLeftNodeOccurrence :
  {initial, pairFirst, pairMiddle, pairFinal, originalFinal :
    SystemState name key value world error} ->
  {original : Transitions initial originalFinal} ->
  {prefixTrace : Transitions initial pairFirst} ->
  {left : Transition pairFirst pairMiddle} ->
  {right : Transition pairMiddle pairFinal} ->
  {suffix : Transitions pairFinal originalFinal} ->
  {diamond : LocalRelationalDiamond name key world error value nameEq keyEq
    left right} ->
  (result : AdjacentSwapResult name key world error value protocol nameEq keyEq
    original prefixTrace left right suffix diamond) ->
  LocatedActionOccurrence (transitionAction left) original
adjacentLeftNodeOccurrence {prefixTrace} {left} {right} {suffix} result =
  MkLocatedActionOccurrence _ _ prefixTrace left
    (MoreTransitions right suffix) Refl (originalDecomposition result)

||| The current right node is likewise located with no caller-supplied
||| occurrence.  Associativity and the checked source decomposition determine
||| its exact prefix.
public export
0 adjacentRightNodeOccurrence :
  {initial, pairFirst, pairMiddle, pairFinal, originalFinal :
    SystemState name key value world error} ->
  {original : Transitions initial originalFinal} ->
  {prefixTrace : Transitions initial pairFirst} ->
  {left : Transition pairFirst pairMiddle} ->
  {right : Transition pairMiddle pairFinal} ->
  {suffix : Transitions pairFinal originalFinal} ->
  {diamond : LocalRelationalDiamond name key world error value nameEq keyEq
    left right} ->
  (result : AdjacentSwapResult name key world error value protocol nameEq keyEq
    original prefixTrace left right suffix diamond) ->
  LocatedActionOccurrence (transitionAction right) original
adjacentRightNodeOccurrence {prefixTrace} {left} {right} {suffix} result =
  MkLocatedActionOccurrence _ _
    (appendTransitions prefixTrace (MoreTransitions left NoTransitions)) right
    suffix Refl
    (trans (appendTransitionsAssociative prefixTrace
      (MoreTransitions left NoTransitions) (MoreTransitions right suffix))
      (originalDecomposition result))

||| Build an authenticated label using only the exact intermediate replay fold
||| output plus the remaining source-block ordinal equation.
public export
0 leftNodeSourceBlockLabel :
  {initial, pairFirst, pairMiddle, pairFinal, originalFinal, sourceInitial,
    sourceFinal : SystemState name key value world error} ->
  {sourceTrace : Transitions sourceInitial sourceFinal} ->
  {original : Transitions initial originalFinal} ->
  {prefixTrace : Transitions initial pairFirst} ->
  {left : Transition pairFirst pairMiddle} ->
  {right : Transition pairMiddle pairFinal} ->
  {suffix : Transitions pairFinal originalFinal} ->
  {diamond : LocalRelationalDiamond name key world error value nameEq keyEq
    left right} ->
  (prefixOccurrences : ActionRegistrationReplayCorrespondence name key world
    error value sourceTrace original) ->
  (sourceBlock : LocatedOpenEpisodeBlock name key world error value nameEq keyEq
    actor sourceTrace) ->
  (position : Nat) ->
  (result : AdjacentSwapResult name key world error value protocol nameEq keyEq
    original prefixTrace left right suffix diamond) ->
  locatedActionOrdinal (replayActionOrigin prefixOccurrences
    (adjacentLeftNodeOccurrence result)) =
      transitionCount (traceBeforeBlock sourceBlock) + position ->
  NodeCrossesSourceBlockPosition name key world error value nameEq keyEq
    sourceTrace original prefixOccurrences sourceBlock position
    (transitionAction left) (transitionCount prefixTrace)
leftNodeSourceBlockLabel prefixOccurrences sourceBlock position result origin =
  MkNodeCrossesSourceBlockPosition (adjacentLeftNodeOccurrence result) Refl origin

public export
0 rightNodeSourceBlockLabel :
  {initial, pairFirst, pairMiddle, pairFinal, originalFinal, sourceInitial,
    sourceFinal : SystemState name key value world error} ->
  {sourceTrace : Transitions sourceInitial sourceFinal} ->
  {original : Transitions initial originalFinal} ->
  {prefixTrace : Transitions initial pairFirst} ->
  {left : Transition pairFirst pairMiddle} ->
  {right : Transition pairMiddle pairFinal} ->
  {suffix : Transitions pairFinal originalFinal} ->
  {diamond : LocalRelationalDiamond name key world error value nameEq keyEq
    left right} ->
  (prefixOccurrences : ActionRegistrationReplayCorrespondence name key world
    error value sourceTrace original) ->
  (sourceBlock : LocatedOpenEpisodeBlock name key world error value nameEq keyEq
    actor sourceTrace) ->
  (position : Nat) ->
  (result : AdjacentSwapResult name key world error value protocol nameEq keyEq
    original prefixTrace left right suffix diamond) ->
  locatedActionOrdinal (replayActionOrigin prefixOccurrences
    (adjacentRightNodeOccurrence result)) =
      transitionCount (traceBeforeBlock sourceBlock) + position ->
  NodeCrossesSourceBlockPosition name key world error value nameEq keyEq
    sourceTrace original prefixOccurrences sourceBlock position
    (transitionAction right) (S (transitionCount prefixTrace))
rightNodeSourceBlockLabel {prefixTrace} {left} prefixOccurrences sourceBlock
  position result origin =
    MkNodeCrossesSourceBlockPosition (adjacentRightNodeOccurrence result)
      (transitionPrefixLength prefixTrace left) origin

||| Labels every concrete adjacent node by occurrence origins in the original
||| source blocks.  The prefix correspondence is not caller-selected at each
||| node: it starts at identity and is definitionally extended by each actual
||| `AdjacentSwapResult` before the recursive tail.
public export
data DerivationCrossesBlockPositions :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {sourceInitial, sourceFinal : SystemState name key value world error} ->
  (sourceTrace : Transitions sourceInitial sourceFinal) ->
  {leftActor, rightActor : name} ->
  (leftBlock : LocatedOpenEpisodeBlock name key world error value nameEq keyEq
    leftActor sourceTrace) ->
  (rightBlock : LocatedOpenEpisodeBlock name key world error value nameEq keyEq
    rightActor sourceTrace) ->
  {currentInitial, currentFinal, targetFinal :
    SystemState name key value world error} ->
  {current : Transitions currentInitial currentFinal} ->
  (prefixOccurrences : ActionRegistrationReplayCorrespondence name key world
    error value sourceTrace current) ->
  {target : Transitions currentInitial targetFinal} ->
  FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq
    current target -> List (Nat, Nat) -> Type where
  BlockCrossingsDone :
    DerivationCrossesBlockPositions name key world error value protocol nameEq
      keyEq sourceTrace leftBlock rightBlock prefixOccurrences
      FiniteAdjacentSwapDone []
  BlockCrossingsStep :
    {initial, pairFirst, pairMiddle, pairFinal, originalFinal, targetFinal :
      SystemState name key value world error} ->
    {leftPosition, rightPosition : Nat} ->
    (original : Transitions initial originalFinal) ->
    (prefixTrace : Transitions initial pairFirst) ->
    (left : Transition pairFirst pairMiddle) ->
    (right : Transition pairMiddle pairFinal) ->
    (suffix : Transitions pairFinal originalFinal) ->
    (orientation : AdjacentSwapOrientationEvidence left right) ->
    (diamond : LocalRelationalDiamond name key world error value nameEq keyEq
      left right) ->
    (result : AdjacentSwapResult name key world error value protocol nameEq keyEq
      original prefixTrace left right suffix diamond) ->
    (target : Transitions initial targetFinal) ->
    (rest : FiniteAdjacentSwapDerivation name key world error value protocol
      nameEq keyEq (swappedTrace result) target) ->
    (prefixOccurrences : ActionRegistrationReplayCorrespondence name key world
      error value sourceTrace original) ->
    NodeCrossesSourceBlockPosition name key world error value nameEq keyEq
      sourceTrace original prefixOccurrences leftBlock leftPosition (transitionAction left)
      (transitionCount prefixTrace) ->
    NodeCrossesSourceBlockPosition name key world error value nameEq keyEq
      sourceTrace original prefixOccurrences rightBlock rightPosition (transitionAction right)
      (S (transitionCount prefixTrace)) ->
    (restPositions : List (Nat, Nat)) ->
    DerivationCrossesBlockPositions name key world error value protocol nameEq
      keyEq sourceTrace leftBlock rightBlock
      (composeActionRegistrationReplayCorrespondence prefixOccurrences
        (swappedOccurrenceCorrespondence result)) rest restPositions ->
    DerivationCrossesBlockPositions name key world error value protocol nameEq
      keyEq sourceTrace leftBlock rightBlock prefixOccurrences
      (FiniteAdjacentSwapStep original prefixTrace left right suffix orientation
        diamond result target rest)
      ((leftPosition, rightPosition) :: restPositions)

||| Producer-side recursive plan.  It contains only the two source-origin
||| equations available at each actual intermediate replay node; it does not
||| assume a prebuilt `DerivationCrossesBlockPositions` value.
public export
data BlockCrossingOriginPlan :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {sourceInitial, sourceFinal : SystemState name key value world error} ->
  (sourceTrace : Transitions sourceInitial sourceFinal) ->
  {leftActor, rightActor : name} ->
  (leftBlock : LocatedOpenEpisodeBlock name key world error value nameEq keyEq
    leftActor sourceTrace) ->
  (rightBlock : LocatedOpenEpisodeBlock name key world error value nameEq keyEq
    rightActor sourceTrace) ->
  {currentInitial, currentFinal, targetFinal :
    SystemState name key value world error} ->
  {current : Transitions currentInitial currentFinal} ->
  (prefixOccurrences : ActionRegistrationReplayCorrespondence name key world
    error value sourceTrace current) ->
  {target : Transitions currentInitial targetFinal} ->
  FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq
    current target -> List (Nat, Nat) -> Type where
  CrossingOriginPlanDone :
    BlockCrossingOriginPlan name key world error value protocol nameEq keyEq
      sourceTrace leftBlock rightBlock prefixOccurrences FiniteAdjacentSwapDone []
  CrossingOriginPlanStep :
    {initial, pairFirst, pairMiddle, pairFinal, originalFinal, targetFinal :
      SystemState name key value world error} ->
    {leftPosition, rightPosition : Nat} ->
    (original : Transitions initial originalFinal) ->
    (prefixTrace : Transitions initial pairFirst) ->
    (left : Transition pairFirst pairMiddle) ->
    (right : Transition pairMiddle pairFinal) ->
    (suffix : Transitions pairFinal originalFinal) ->
    (orientation : AdjacentSwapOrientationEvidence left right) ->
    (diamond : LocalRelationalDiamond name key world error value nameEq keyEq
      left right) ->
    (result : AdjacentSwapResult name key world error value protocol nameEq keyEq
      original prefixTrace left right suffix diamond) ->
    (target : Transitions initial targetFinal) ->
    (rest : FiniteAdjacentSwapDerivation name key world error value protocol
      nameEq keyEq (swappedTrace result) target) ->
    (prefixOccurrences : ActionRegistrationReplayCorrespondence name key world
      error value sourceTrace original) ->
    {leftActor, rightActor : name} ->
    (leftBlock : LocatedOpenEpisodeBlock name key world error value nameEq keyEq
      leftActor sourceTrace) ->
    (rightBlock : LocatedOpenEpisodeBlock name key world error value nameEq keyEq
      rightActor sourceTrace) ->
    locatedActionOrdinal (replayActionOrigin prefixOccurrences
      (adjacentLeftNodeOccurrence result)) =
      transitionCount (traceBeforeBlock leftBlock) + leftPosition ->
    locatedActionOrdinal (replayActionOrigin prefixOccurrences
      (adjacentRightNodeOccurrence result)) =
      transitionCount (traceBeforeBlock rightBlock) + rightPosition ->
    (restPositions : List (Nat, Nat)) ->
    BlockCrossingOriginPlan name key world error value protocol nameEq keyEq
      sourceTrace leftBlock rightBlock
      (composeActionRegistrationReplayCorrespondence prefixOccurrences
        (swappedOccurrenceCorrespondence result)) rest restPositions ->
    BlockCrossingOriginPlan name key world error value protocol nameEq keyEq
      sourceTrace leftBlock rightBlock prefixOccurrences
      (FiniteAdjacentSwapStep original prefixTrace left right suffix orientation
        diamond result target rest)
      ((leftPosition, rightPosition) :: restPositions)

||| The actual recursive label fold.  Current node occurrences are constructed
||| from each `AdjacentSwapResult`; the prefix map is threaded definitionally.
public export
0 foldBlockCrossingOriginPlan :
  BlockCrossingOriginPlan name key world error value protocol nameEq keyEq
    sourceTrace leftBlock rightBlock prefixOccurrences derivation positions ->
  DerivationCrossesBlockPositions name key world error value protocol nameEq keyEq
    sourceTrace leftBlock rightBlock prefixOccurrences derivation positions
foldBlockCrossingOriginPlan CrossingOriginPlanDone = BlockCrossingsDone
foldBlockCrossingOriginPlan
  (CrossingOriginPlanStep original prefixTrace left right suffix orientation
    diamond result target rest prefixOccurrences leftBlock rightBlock leftOrigin
    rightOrigin restPositions restPlan) =
      BlockCrossingsStep original prefixTrace left right suffix orientation diamond
        result target rest prefixOccurrences
        (leftNodeSourceBlockLabel prefixOccurrences leftBlock _ result leftOrigin)
        (rightNodeSourceBlockLabel prefixOccurrences rightBlock _ result rightOrigin)
        restPositions (foldBlockCrossingOriginPlan restPlan)

||| A genuine whole-block swap is nonempty and covers the exact Cartesian set
||| of source transition positions once.  Completeness, sound bounds, uniqueness,
||| and node count make the selected-block indices semantically non-phantom.
public export
record WholeBlockSwapDerivation
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {sourceOrder, targetOrder : List name}
  (orderSwap : AdjacentActorOrderSwap name sourceOrder targetOrder)
  {initial, sourceFinal, targetFinal : SystemState name key value world error}
  (sourceTrace : Transitions initial sourceFinal)
  (sourceBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
    sourceOrder sourceTrace)
  (sourcePremises : ReplayInvariantBundle name key world error value protocol
    nameEq keyEq sourceTrace)
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq
    keyEq orderSwap sourceTrace sourceBlocks sourcePremises)
  (targetTrace : Transitions initial targetFinal) where
  constructor MkWholeBlockSwapDerivation
  nonEmptyBlockDerivation : NonEmptyFiniteAdjacentSwapDerivation name key world
    error value protocol nameEq keyEq sourceTrace targetTrace
  crossedSourcePositions : List (Nat, Nat)
  0 blockCrossingPlan : BlockCrossingOriginPlan name key world error value
    protocol nameEq keyEq sourceTrace
    (decomposedBlock sourceBlocks (actorLeft orderSwap)
      (safetyLeftInOrder safety))
    (decomposedBlock sourceBlocks (actorRight orderSwap)
      (safetyRightInOrder safety))
    (identityActionRegistrationReplayCorrespondence sourceTrace)
    (nonEmptyToFiniteAdjacentSwapDerivation nonEmptyBlockDerivation)
    crossedSourcePositions
  0 everyBlockPairCrossed : (leftPosition, rightPosition : Nat) ->
    LTE (S leftPosition)
      (actorBlockTransitionCount (decomposedBlock sourceBlocks
        (actorLeft orderSwap) (safetyLeftInOrder safety))) ->
    LTE (S rightPosition)
      (actorBlockTransitionCount (decomposedBlock sourceBlocks
        (actorRight orderSwap) (safetyRightInOrder safety))) ->
    Elem (leftPosition, rightPosition) crossedSourcePositions
  0 everyCrossingUsesSelectedBlocks : (leftPosition, rightPosition : Nat) ->
    Elem (leftPosition, rightPosition) crossedSourcePositions ->
    ( LTE (S leftPosition)
        (actorBlockTransitionCount (decomposedBlock sourceBlocks
          (actorLeft orderSwap) (safetyLeftInOrder safety)))
    , LTE (S rightPosition)
        (actorBlockTransitionCount (decomposedBlock sourceBlocks
          (actorRight orderSwap) (safetyRightInOrder safety)))
    )
  0 blockCrossingPositionsUnique : UniqueKeys crossedSourcePositions
  0 blockCrossingNodeCountExact :
    nonEmptyAdjacentSwapNodeCount nonEmptyBlockDerivation =
      actorBlockTransitionCount (decomposedBlock sourceBlocks
        (actorLeft orderSwap) (safetyLeftInOrder safety)) *
      actorBlockTransitionCount (decomposedBlock sourceBlocks
        (actorRight orderSwap) (safetyRightInOrder safety))

public export
0 blockCrossingLabels :
  (whole : WholeBlockSwapDerivation name key world error value protocol nameEq
    keyEq orderSwap sourceTrace sourceBlocks sourcePremises safety targetTrace) ->
  DerivationCrossesBlockPositions name key world error value protocol nameEq keyEq
    sourceTrace
    (decomposedBlock sourceBlocks (actorLeft orderSwap)
      (safetyLeftInOrder safety))
    (decomposedBlock sourceBlocks (actorRight orderSwap)
      (safetyRightInOrder safety))
    (identityActionRegistrationReplayCorrespondence sourceTrace)
    (nonEmptyToFiniteAdjacentSwapDerivation (nonEmptyBlockDerivation whole))
    (crossedSourcePositions whole)
blockCrossingLabels whole = foldBlockCrossingOriginPlan (blockCrossingPlan whole)

||| A shifted block-start/compensating-position alias is impossible at the
||| authoritative whole-block boundary, even though isolated caller blocks can
||| be arithmetically aliased.
public export
0 wholeSelectedCoordinateAliasImpossible :
  (whole : WholeBlockSwapDerivation name key world error value protocol nameEq
    keyEq orderSwap sourceTrace sourceBlocks sourcePremises safety targetTrace) ->
  (leftPosition, rightPosition : Nat) ->
  LTE (S leftPosition) (actorBlockTransitionCount (decomposedBlock sourceBlocks
    (actorLeft orderSwap) (safetyLeftInOrder safety))) ->
  LTE (S rightPosition) (actorBlockTransitionCount (decomposedBlock sourceBlocks
    (actorRight orderSwap) (safetyRightInOrder safety))) ->
  transitionCount (traceBeforeBlock (decomposedBlock sourceBlocks
    (actorLeft orderSwap) (safetyLeftInOrder safety))) + leftPosition =
  transitionCount (traceBeforeBlock (decomposedBlock sourceBlocks
    (actorRight orderSwap) (safetyRightInOrder safety))) + rightPosition ->
  Void
wholeSelectedCoordinateAliasImpossible {safety} whole leftPosition rightPosition
  leftBound rightBound exact =
    selectedLeftRightRangesDisjoint
      (selectedBlockCoordinateInjectivity safety)
      leftPosition rightPosition leftBound rightBound exact

public export
wholeBlockFiniteDerivation :
  WholeBlockSwapDerivation name key world error value protocol nameEq keyEq
    orderSwap sourceTrace sourceBlocks sourcePremises safety targetTrace ->
  FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq
    sourceTrace targetTrace
wholeBlockFiniteDerivation whole =
  nonEmptyToFiniteAdjacentSwapDerivation (nonEmptyBlockDerivation whole)

||| One actual whole-block transposition.  The finite derivation is mandatory:
||| every transition crossing is classified A/A, A/O, O/A, or O/O and carries
||| its concrete `AdjacentSwapResult`, including action/registration occurrence
||| correspondence.  Endpoint assertions alone cannot construct this record.
public export
record OperationalAdjacentBlockSwap
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {sourceOrder, targetOrder : List name}
  (orderSwap : AdjacentActorOrderSwap name sourceOrder targetOrder)
  {initial, sourceFinal : SystemState name key value world error}
  (sourceTrace : Transitions initial sourceFinal)
  (sourceBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
    sourceOrder sourceTrace)
  (sourcePremises : ReplayInvariantBundle name key world error value protocol
    nameEq keyEq sourceTrace)
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq
    keyEq orderSwap sourceTrace sourceBlocks sourcePremises) where
  constructor MkOperationalAdjacentBlockSwap
  blockSwapFinal : SystemState name key value world error
  blockSwapTrace : Transitions initial blockSwapFinal
  blockSwapWholeDerivation : WholeBlockSwapDerivation name key world error value
    protocol nameEq keyEq orderSwap sourceTrace sourceBlocks sourcePremises safety
      blockSwapTrace
  blockSwapBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
    targetOrder blockSwapTrace
  blockSwapEndpoint : RelationalReplayEndpoint name key world error value nameEq
    keyEq sourceFinal blockSwapFinal
  blockSwapPremises : ReplayInvariantBundle name key world error value protocol
    nameEq keyEq blockSwapTrace
  blockSwapSameExternalInputs : SameExternalOrchestration nameEq sourceTrace
    blockSwapTrace

public export
0 blockSwapReplayCorrespondence :
  (step : OperationalAdjacentBlockSwap name key world error value protocol nameEq
    keyEq orderSwap sourceTrace sourceBlocks sourcePremises safety) ->
  RelationalReplayCorrespondence name key world error value sourceTrace
    (blockSwapTrace step)
blockSwapReplayCorrespondence step =
  finiteDerivationReplayCorrespondence
    (wholeBlockFiniteDerivation (blockSwapWholeDerivation step))

public export
0 blockSwapOccurrenceCorrespondence :
  (step : OperationalAdjacentBlockSwap name key world error value protocol nameEq
    keyEq orderSwap sourceTrace sourceBlocks sourcePremises safety) ->
  ActionRegistrationReplayCorrespondence name key world error value sourceTrace
    (blockSwapTrace step)
blockSwapOccurrenceCorrespondence step =
  finiteDerivationOccurrenceCorrespondence
    (wholeBlockFiniteDerivation (blockSwapWholeDerivation step))

||| Exact one-step operational producer.  Its proof must enumerate the finite
||| Cartesian crossing of the two located blocks, derive early applicability and
||| orientation-specific premises from the current bundle/safety, invoke the
||| four local diamonds, and splice every `AdjacentSwapResult`.
public export
0 operationalAdjacentBlockSwapSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} ->
  (orderSwap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal : SystemState name key value world error} ->
  (sourceTrace : Transitions initial sourceFinal) ->
  (sourceBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
    sourceOrder sourceTrace) ->
  (sourcePremises : ReplayInvariantBundle name key world error value protocol
    nameEq keyEq sourceTrace) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq
    keyEq orderSwap sourceTrace sourceBlocks sourcePremises) ->
  OperationalAdjacentBlockSwap name key world error value protocol nameEq keyEq
    orderSwap sourceTrace sourceBlocks sourcePremises safety
operationalAdjacentBlockSwapSpike = ?operationalAdjacentBlockSwapSpike_rhs

||| Every selected list step is now indexed by exact operational safety and its
||| realized block replay.  A caller cannot prepend a pure swap/inverse loop
||| without also constructing both intermediate safety proofs and finite local
||| diamond derivations.
public export
data OperationalActorPermutation :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {sourceOrder, targetOrder : List name} ->
  (certificate : CertifiedActorPermutation name sourceOrder targetOrder) ->
  {initial, sourceFinal, targetFinal : SystemState name key value world error} ->
  (sourceTrace : Transitions initial sourceFinal) ->
  (sourceBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
    sourceOrder sourceTrace) ->
  (sourcePremises : ReplayInvariantBundle name key world error value protocol
    nameEq keyEq sourceTrace) ->
  (targetTrace : Transitions initial targetFinal) -> Type where
  OperationalActorDone :
    (blocks : ActorBlockDecomposition name key world error value nameEq keyEq
      order trace) ->
    (premises : ReplayInvariantBundle name key world error value protocol nameEq
      keyEq trace) ->
    OperationalActorPermutation name key world error value protocol nameEq keyEq
      ActorPermutationDone trace blocks premises trace
  OperationalActorStep :
    (orderSwap : AdjacentActorOrderSwap name before middle) ->
    (restCertificate : CertifiedActorPermutation name middle after) ->
    (sourceBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
      before sourceTrace) ->
    (sourcePremises : ReplayInvariantBundle name key world error value protocol
      nameEq keyEq sourceTrace) ->
    (safety : AdjacentActorSwapSafety name key world error value protocol nameEq
      keyEq orderSwap sourceTrace sourceBlocks sourcePremises) ->
    (step : OperationalAdjacentBlockSwap name key world error value protocol
      nameEq keyEq orderSwap sourceTrace sourceBlocks sourcePremises safety) ->
    (rest : OperationalActorPermutation name key world error value protocol
      nameEq keyEq restCertificate (blockSwapTrace step) (blockSwapBlocks step)
        (blockSwapPremises step) targetTrace) ->
    OperationalActorPermutation name key world error value protocol nameEq keyEq
      (ActorPermutationStep orderSwap restCertificate) sourceTrace sourceBlocks
        sourcePremises targetTrace

public export
0 operationalPermutationReplayCorrespondence :
  OperationalActorPermutation name key world error value protocol nameEq keyEq
    certificate sourceTrace sourceBlocks sourcePremises targetTrace ->
  RelationalReplayCorrespondence name key world error value sourceTrace targetTrace
operationalPermutationReplayCorrespondence
  (OperationalActorDone blocks premises) =
    MkRelationalReplayCorrespondence (\actor, generator => generator)
      (\observedKeyEq, actor, generator =>
        replayTraceGeneratorMapRespects observedKeyEq generator)
      (\actor, stage => stage)
      (\actor, stage, state => Refl)
operationalPermutationReplayCorrespondence
  (OperationalActorStep orderSwap restCertificate sourceBlocks sourcePremises
    safety step rest) =
      composeRelationalReplayCorrespondence (blockSwapReplayCorrespondence step)
        (operationalPermutationReplayCorrespondence rest)

public export
0 operationalPermutationOccurrenceCorrespondence :
  {sourceOrder, targetOrder : List name} ->
  {certificate : CertifiedActorPermutation name sourceOrder targetOrder} ->
  {initial, sourceFinal, targetFinal : SystemState name key value world error} ->
  {sourceTrace : Transitions initial sourceFinal} ->
  {sourceBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
    sourceOrder sourceTrace} ->
  {sourcePremises : ReplayInvariantBundle name key world error value protocol
    nameEq keyEq sourceTrace} ->
  {targetTrace : Transitions initial targetFinal} ->
  (replay : OperationalActorPermutation name key world error value protocol nameEq
    keyEq certificate sourceTrace sourceBlocks sourcePremises targetTrace) ->
  ActionRegistrationReplayCorrespondence name key world error value sourceTrace
    targetTrace
operationalPermutationOccurrenceCorrespondence {sourceTrace}
  (OperationalActorDone blocks premises) =
    identityActionRegistrationReplayCorrespondence sourceTrace
operationalPermutationOccurrenceCorrespondence
  (OperationalActorStep orderSwap restCertificate sourceBlocks sourcePremises
    safety step rest) =
      composeActionRegistrationReplayCorrespondence
        (blockSwapOccurrenceCorrespondence step)
        (operationalPermutationOccurrenceCorrespondence rest)

||| Endpoint quotients compose along the sealed operational permutation fold.
||| This is the O20-independent projection needed to package a replayed left
||| execution from O19 capital.
public export
0 operationalPermutationEndpoint :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {sourceOrder, targetOrder : List name} ->
  {certificate : CertifiedActorPermutation name sourceOrder targetOrder} ->
  {initial, sourceFinal, targetFinal : SystemState name key value world error} ->
  {sourceTrace : Transitions initial sourceFinal} ->
  {sourceBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
    sourceOrder sourceTrace} ->
  {sourcePremises : ReplayInvariantBundle name key world error value protocol
    nameEq keyEq sourceTrace} ->
  {targetTrace : Transitions initial targetFinal} ->
  OperationalActorPermutation name key world error value protocol nameEq keyEq
    certificate sourceTrace sourceBlocks sourcePremises targetTrace ->
  RelationalReplayEndpoint name key world error value nameEq keyEq sourceFinal
    targetFinal
operationalPermutationEndpoint nameEq keyEq
  (OperationalActorDone blocks premises) =
    relationalReplayEndpointReflexiveSpike nameEq keyEq _
      (replayFinalWellFormed premises)
operationalPermutationEndpoint nameEq keyEq
  (OperationalActorStep orderSwap restCertificate sourceBlocks sourcePremises
    safety step rest) =
      relationalReplayEndpointTransitiveSpike nameEq keyEq _ _ _
        (blockSwapEndpoint step)
        (operationalPermutationEndpoint nameEq keyEq rest)

||| Cross-trace support matching now contains no certificate at all.  It is
||| publicly constructible without risk because O20 never consumes it as an
||| operational schedule; it records only renamed set equality.
public export
record MappedCanonicalSupportOrders
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, leftFinal, rightFinal : SystemState name key value world error}
  (leftTrace : Transitions initial leftFinal)
  (rightTrace : Transitions initial rightFinal)
  (renaming : NameBijection name)
  (leftSchedule : CanonicalSchedule name key world error value protocol nameEq
    keyEq leftTrace)
  (rightSchedule : CanonicalSchedule name key world error value protocol nameEq
    keyEq rightTrace) where
  constructor MkMappedCanonicalSupportOrders
  0 leftSupportMapped : (n : name) -> Elem n (supportOrder leftSchedule) ->
    Elem (renameForward renaming n) (supportOrder rightSchedule)
  0 rightSupportMapped : (n : name) -> Elem n (supportOrder rightSchedule) ->
    Elem (renameBackward renaming n) (supportOrder leftSchedule)

||| Turn pointwise forward support preservation into membership in the right
||| canonical enumeration.  Uniqueness/order concerns remain owned by each
||| schedule's `LinearizesSupport`; this helper performs only one membership
||| elimination.
0 canonicalSupportOrderForwardFromTruth :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {leftInitial, rightInitial, leftFinal, rightFinal :
    SystemState name key value world error} ->
  {leftTrace : Transitions leftInitial leftFinal} ->
  {rightTrace : Transitions rightInitial rightFinal} ->
  (renaming : NameBijection name) ->
  (leftSchedule : CanonicalSchedule name key world error value protocol nameEq
    keyEq leftTrace) ->
  (rightSchedule : CanonicalSchedule name key world error value protocol nameEq
    keyEq rightTrace) ->
  ((selected : name) ->
    (isSupported @{nameEq} @{keyEq} selected leftFinal = True) ->
    (isSupported @{nameEq} @{keyEq} (renameForward renaming selected)
      rightFinal = True)) ->
  (selected : name) -> Elem selected (supportOrder leftSchedule) ->
  Elem (renameForward renaming selected) (supportOrder rightSchedule)
canonicalSupportOrderForwardFromTruth nameEq keyEq protocol renaming
  leftSchedule rightSchedule supportForward selected selectedIn =
    orderComplete (supportLinearization rightSchedule)
      (renameForward renaming selected)
      (supportForward selected
        (orderSound (supportLinearization leftSchedule) selected selectedIn))

||| Symmetric membership lift for the inverse name map.
0 canonicalSupportOrderBackwardFromTruth :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {leftInitial, rightInitial, leftFinal, rightFinal :
    SystemState name key value world error} ->
  {leftTrace : Transitions leftInitial leftFinal} ->
  {rightTrace : Transitions rightInitial rightFinal} ->
  (renaming : NameBijection name) ->
  (leftSchedule : CanonicalSchedule name key world error value protocol nameEq
    keyEq leftTrace) ->
  (rightSchedule : CanonicalSchedule name key world error value protocol nameEq
    keyEq rightTrace) ->
  ((selected : name) ->
    (isSupported @{nameEq} @{keyEq} selected rightFinal = True) ->
    (isSupported @{nameEq} @{keyEq} (renameBackward renaming selected)
      leftFinal = True)) ->
  (selected : name) -> Elem selected (supportOrder rightSchedule) ->
  Elem (renameBackward renaming selected) (supportOrder leftSchedule)
canonicalSupportOrderBackwardFromTruth nameEq keyEq protocol renaming
  leftSchedule rightSchedule supportBackward selected selectedIn =
    orderComplete (supportLinearization leftSchedule)
      (renameBackward renaming selected)
      (supportBackward selected
        (orderSound (supportLinearization rightSchedule) selected selectedIn))

||| Exact O19 set-matching assembly once both semantic support directions have
||| been obtained from the generation/current-endpoint correspondence.
0 canonicalSupportOrdersFromTruth :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (leftTrace : Transitions initial leftFinal) ->
  (rightTrace : Transitions initial rightFinal) ->
  (renaming : NameBijection name) ->
  (leftSchedule : CanonicalSchedule name key world error value protocol nameEq
    keyEq leftTrace) ->
  (rightSchedule : CanonicalSchedule name key world error value protocol nameEq
    keyEq rightTrace) ->
  ((selected : name) ->
    (isSupported @{nameEq} @{keyEq} selected leftFinal = True) ->
    (isSupported @{nameEq} @{keyEq} (renameForward renaming selected)
      rightFinal = True)) ->
  ((selected : name) ->
    (isSupported @{nameEq} @{keyEq} selected rightFinal = True) ->
    (isSupported @{nameEq} @{keyEq} (renameBackward renaming selected)
      leftFinal = True)) ->
  MappedCanonicalSupportOrders name key world error value protocol nameEq keyEq
    leftTrace rightTrace renaming leftSchedule rightSchedule
canonicalSupportOrdersFromTruth nameEq keyEq protocol leftTrace rightTrace
  renaming leftSchedule rightSchedule supportForward supportBackward =
    MkMappedCanonicalSupportOrders
      (canonicalSupportOrderForwardFromTruth nameEq keyEq protocol renaming
        leftSchedule rightSchedule supportForward)
      (canonicalSupportOrderBackwardFromTruth nameEq keyEq protocol renaming
        leftSchedule rightSchedule supportBackward)

public export
0 canonicalSupportOrdersMatchSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (leftTrace : Transitions initial leftFinal) ->
  (rightTrace : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace
    rightTrace) ->
  (leftCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq leftTrace) ->
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq rightTrace) ->
  MappedCanonicalSupportOrders name key world error value protocol nameEq keyEq
    leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)
canonicalSupportOrdersMatchSpike = ?canonicalSupportOrdersMatchSpike_rhs

||| The bridge-facing capital exposes the exact first-state blocks consumed by
||| O19 together with the producer's disjoint-range invariant.
public export
canonicalActorBlockDecomposition :
  (capital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq original) ->
  ActorBlockDecomposition name key world error value nameEq keyEq
    (supportOrder (canonicalSchedule capital))
    (canonicalTrace (canonicalSchedule capital))
canonicalActorBlockDecomposition
  (MkIndependentCanonicalSchedule premises reduction ordering sorted
    supportTransport accounting _ Refl classified) =
      MkActorBlockDecomposition (sortedBlock sorted)
        (sortedBlocksFollowOrder sorted) (sortedBlockRangesDisjoint sorted)
        (sortedLifecycleCoverage sorted)

||| Sealed-by-evidence O19 output.  The pure certificate and every exact
||| intermediate trace are existential fields of the same package as the
||| operational realization; there is no function from a public pure
||| certificate to O20.
public export
record CertifiedOperationalCanonicalPermutation
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, leftFinal, rightFinal : SystemState name key value world error}
  (leftTrace : Transitions initial leftFinal)
  (rightTrace : Transitions initial rightFinal)
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace rightTrace)
  (leftCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq leftTrace)
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq rightTrace)
  (matching : MappedCanonicalSupportOrders name key world error value protocol
    nameEq keyEq leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)) where
  constructor MkCertifiedOperationalCanonicalPermutation
  selectedActorPermutation : CertifiedActorPermutation name
    (supportOrder (canonicalSchedule leftCapital))
    (map (renameBackward (currentNameBijection (endpointRenaming sameInputs)))
      (supportOrder (canonicalSchedule rightCapital)))
  operationalTargetFinal : SystemState name key value world error
  operationalTargetTrace : Transitions initial operationalTargetFinal
  operationalTargetBlocks : ActorBlockDecomposition name key world error value
    nameEq keyEq
    (map (renameBackward (currentNameBijection (endpointRenaming sameInputs)))
      (supportOrder (canonicalSchedule rightCapital))) operationalTargetTrace
  operationalTargetPremises : ReplayInvariantBundle name key world error value
    protocol nameEq keyEq operationalTargetTrace
  selectedPermutationRealized : OperationalActorPermutation name key world error
    value protocol nameEq keyEq selectedActorPermutation
    (canonicalTrace (canonicalSchedule leftCapital))
    (canonicalActorBlockDecomposition leftCapital)
    (canonicalReplayPremises leftCapital) operationalTargetTrace

||| O19 must choose a permutation and realize it simultaneously.  This is the
||| remaining existence risk when accepted support relations differ through
||| withdrawn intermediates; the type no longer hides that risk in O20.
public export
0 selectOperationalCanonicalPermutationSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (leftTrace : Transitions initial leftFinal) ->
  (rightTrace : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace
    rightTrace) ->
  (leftCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq leftTrace) ->
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq rightTrace) ->
  (matching : MappedCanonicalSupportOrders name key world error value protocol
    nameEq keyEq leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)) ->
  CertifiedOperationalCanonicalPermutation name key world error value protocol
    nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital matching
selectOperationalCanonicalPermutationSpike =
  ?selectOperationalCanonicalPermutationSpike_rhs

||| Honest revision-6 label: this is a static accepted-index interface test, not
||| a concrete reachable O19/O20 run.  It proves that the old full-path field is
||| absent while preserving the exact scanner-deleted birth and real path.
public export
record IntermediateVestigialStaticInterfaceRegression
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, leftFinal, rightFinal : SystemState name key value world error}
  (leftTrace : Transitions initial leftFinal)
  (rightTrace : Transitions initial rightFinal)
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace rightTrace)
  (leftCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq leftTrace)
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq rightTrace)
  (matching : MappedCanonicalSupportOrders name key world error value protocol
    nameEq keyEq leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital))
  (lower, withdrawnMiddle, upper : name) where
  constructor MkIntermediateVestigialStaticInterfaceRegression
  pathThroughWithdrawnIntermediate : SupportPath nameEq leftFinal lower upper
  preciseWithdrawnBirth : RegistrationGeneration name
  0 preciseWithdrawnBirthCurrent : lookupCurrentGeneration @{nameEq}
    withdrawnMiddle (leftFinalGenerations (generatedRegistrationTree sameInputs)) =
      Just preciseWithdrawnBirth
  0 preciseWithdrawnBirthDeleted : Elem preciseWithdrawnBirth
    (leftDeletedGenerations (generatedRegistrationTree sameInputs))
  0 withdrawnIntermediateAbsentRight :
    lookupFiber @{nameEq} {key = key} {value = value} {world = world}
      {error = error}
      (renameForward (currentNameBijection (endpointRenaming sameInputs))
        withdrawnMiddle) (registry rightFinal) = Nothing
  0 withdrawnIntermediateNotAnActor :
    Elem withdrawnMiddle (supportOrder (canonicalSchedule leftCapital)) -> Void

public export
intermediateVestigialStaticInterfaceRegression :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  {leftTrace : Transitions initial leftFinal} ->
  {rightTrace : Transitions initial rightFinal} ->
  {sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace
    rightTrace} ->
  {leftCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq leftTrace} ->
  {rightCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq rightTrace} ->
  (matching : MappedCanonicalSupportOrders name key world error value protocol
    nameEq keyEq leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)) ->
  (lower, withdrawnMiddle, upper : name) ->
  SupportEdge nameEq leftFinal lower withdrawnMiddle ->
  SupportPath nameEq leftFinal withdrawnMiddle upper ->
  (leftVestigial : VestigialEndpointGeneration name key world error value nameEq
    keyEq (leftFinalGenerations (generatedRegistrationTree sameInputs))
      (leftDeletedGenerations (generatedRegistrationTree sameInputs))
      withdrawnMiddle leftFinal) ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world}
    {error = error}
    (renameForward (currentNameBijection (endpointRenaming sameInputs))
      withdrawnMiddle) (registry rightFinal) = Nothing ->
  IntermediateVestigialStaticInterfaceRegression name key world error value
    protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital
      matching lower withdrawnMiddle upper
intermediateVestigialStaticInterfaceRegression matching lower withdrawnMiddle
  upper pathFirst pathRest leftVestigial rightAbsent =
    MkIntermediateVestigialStaticInterfaceRegression
      (SupportPathMore pathFirst pathRest)
      (vestigialGeneration leftVestigial)
      (vestigialGenerationCurrent leftVestigial)
      (vestigialBirthDiscarded leftVestigial)
      rightAbsent
      (\middleIn => case trans
        (sym (orderSound
          (supportLinearization (canonicalSchedule leftCapital))
          withdrawnMiddle middleIn))
        (vestigialUnsupported leftVestigial) of Refl impossible)

||| O20 packages the exact already-safe operational target with its endpoint
||| quotient and bridge.  Occurrence correspondence is derived structurally from
||| the sealed operational fold, not asserted from effect-generator capital.
public export
record PermutedCanonicalExecution
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, leftFinal, rightFinal : SystemState name key value world error}
  (leftTrace : Transitions initial leftFinal)
  (rightTrace : Transitions initial rightFinal)
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace rightTrace)
  (leftCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq leftTrace)
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq rightTrace)
  {matching : MappedCanonicalSupportOrders name key world error value protocol
    nameEq keyEq leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)}
  (operational : CertifiedOperationalCanonicalPermutation name key world error
    value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital
      rightCapital matching) where
  constructor MkPermutedCanonicalExecution
  composedPermutationEndpoint : RelationalReplayEndpoint name key world error
    value nameEq keyEq (canonicalFinal (canonicalSchedule leftCapital))
      (operationalTargetFinal operational)
  permutationSameExternalInputs : SameExternalOrchestration nameEq
    (canonicalTrace (canonicalSchedule leftCapital))
      (operationalTargetTrace operational)

public export
0 permutationReplayCorrespondence :
  {operational : CertifiedOperationalCanonicalPermutation name key world error
    value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital
      rightCapital matching} ->
  PermutedCanonicalExecution name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs leftCapital rightCapital operational ->
  RelationalReplayCorrespondence name key world error value
    (canonicalTrace (canonicalSchedule leftCapital))
    (operationalTargetTrace operational)
permutationReplayCorrespondence {operational} execution =
  operationalPermutationReplayCorrespondence
    (selectedPermutationRealized operational)

public export
0 permutationOccurrenceCorrespondence :
  {operational : CertifiedOperationalCanonicalPermutation name key world error
    value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital
      rightCapital matching} ->
  PermutedCanonicalExecution name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs leftCapital rightCapital operational ->
  ActionRegistrationReplayCorrespondence name key world error value
    (canonicalTrace (canonicalSchedule leftCapital))
    (operationalTargetTrace operational)
permutationOccurrenceCorrespondence {operational} execution =
  operationalPermutationOccurrenceCorrespondence
    (selectedPermutationRealized operational)

public export
record CanonicalConvergenceResult
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, leftFinal, rightFinal : SystemState name key value world error}
  (leftTrace : Transitions initial leftFinal)
  (rightTrace : Transitions initial rightFinal)
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace rightTrace)
  (leftCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq leftTrace)
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq rightTrace)
  {matching : MappedCanonicalSupportOrders name key world error value protocol
    nameEq keyEq leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)}
  (operational : CertifiedOperationalCanonicalPermutation name key world error
    value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital
      rightCapital matching) where
  constructor MkCanonicalConvergenceResult
  permutedLeftExecution : PermutedCanonicalExecution name key world error value
    protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital
      operational
  convergenceBridge : ReplayedCanonicalEndpointBridge name key world error value
    protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital
      (operationalTargetTrace operational)
      (permutationOccurrenceCorrespondence permutedLeftExecution) rightCapital

||| O20 no longer quantifies over a public pure certificate.  It accepts only
||| O19's package containing exact safety and finite local derivations.
public export
0 canonicalSchedulesConvergeSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (leftTrace : Transitions initial leftFinal) ->
  (rightTrace : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace
    rightTrace) ->
  (leftCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq leftTrace) ->
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq rightTrace) ->
  {matching : MappedCanonicalSupportOrders name key world error value protocol
    nameEq keyEq leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)} ->
  (operational : CertifiedOperationalCanonicalPermutation name key world error
    value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital
      rightCapital matching) ->
  CanonicalConvergenceResult name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs leftCapital rightCapital operational
canonicalSchedulesConvergeSpike = ?canonicalSchedulesConvergeSpike_rhs

public export
0 originalEndpointsConvergeSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (leftTrace : Transitions initial leftFinal) ->
  (rightTrace : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace
    rightTrace) ->
  (leftCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq leftTrace) ->
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq rightTrace) ->
  {matching : MappedCanonicalSupportOrders name key world error value protocol
    nameEq keyEq leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)} ->
  {operational : CertifiedOperationalCanonicalPermutation name key world error
    value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital
      rightCapital matching} ->
  CanonicalConvergenceResult name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs leftCapital rightCapital operational ->
  SystemEquivalentByRenamingModuloVestigial name key world error value nameEq
    keyEq (generatedRegistrationTree sameInputs)
    (currentNameBijection (endpointRenaming sameInputs))
originalEndpointsConvergeSpike nameEq keyEq protocol leftTrace rightTrace
  sameInputs leftCapital rightCapital convergence =
    replayedCanonicalToOriginalEndpointSpike nameEq keyEq protocol leftTrace
      rightTrace sameInputs leftCapital rightCapital
      (acceptedDeletionScannerCapitalSpike nameEq keyEq protocol leftTrace
        rightTrace sameInputs leftCapital rightCapital)
      (operationalTargetTrace operational)
      (permutationReplayCorrespondence (permutedLeftExecution convergence))
      (composedPermutationEndpoint (permutedLeftExecution convergence))
      (permutationOccurrenceCorrespondence (permutedLeftExecution convergence))
      (convergenceBridge convergence)

||| Once the two schedules and exact original endpoint bridge are available,
||| the accepted result is direct constructor assembly.
public export
0 confluenceResultFromCanonicalCapital :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (leftTrace : Transitions initial leftFinal) ->
  (rightTrace : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace
    rightTrace) ->
  (leftSchedule : CanonicalSchedule name key world error value protocol nameEq
    keyEq leftTrace) ->
  (rightSchedule : CanonicalSchedule name key world error value protocol nameEq
    keyEq rightTrace) ->
  (equivalent : SystemEquivalentByRenamingModuloVestigial name key world error
    value nameEq keyEq (generatedRegistrationTree sameInputs)
      (currentNameBijection (endpointRenaming sameInputs))) ->
  ConfluenceResult name key world error value protocol nameEq keyEq leftTrace
    rightTrace (generatedGenerationBijection sameInputs)
    (currentNameBijection (endpointRenaming sameInputs))
confluenceResultFromCanonicalCapital nameEq keyEq protocol leftTrace rightTrace
  sameInputs leftSchedule rightSchedule equivalent =
    MkConfluenceResult leftSchedule rightSchedule
      (generatedRegistrationTree sameInputs)
      (endpointRenaming sameInputs) equivalent
