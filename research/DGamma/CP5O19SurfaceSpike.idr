module DGamma.CP5O19SurfaceSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5GeneratedOrchestrationMatched
import DGamma.CP5AcceptedSupportTruthSpike
import DGamma.CP5RankedEarlyApplicabilitySpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
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
||| generated-child licensing exclusions. R182 additionally certifies right-first
||| opening at the pre-left cut; left-first is already owned by blockOpening.
||| This is first-step applicability, NOT an assumed swapped trace or diamond.
||| These fields are intentionally not reducible to `actorDistinct`.
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
  0 safetyRightOpeningEarly : CheckedEarlyApplication name key world error value
    nameEq keyEq
    (blockPreStart (decomposedBlock sourceBlocks (actorLeft orderSwap)
      safetyLeftInOrder))
    (LBegin (actorRight orderSwap)) LBeginTag
  0 safetyBlocksAdjacent : (transitionCount (betweenBlocks safetyBlocksOrdered) = 0)

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

