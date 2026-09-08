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

