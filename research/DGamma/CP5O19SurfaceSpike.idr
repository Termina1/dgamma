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

