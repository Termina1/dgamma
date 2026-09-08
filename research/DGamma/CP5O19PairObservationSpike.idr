module DGamma.CP5O19PairObservationSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5O19CartesianCursorSpike
import DGamma.CP5O19AdjacentReplayProducerSpike
import DGamma.CP5O19MixedActivationRowSpike
import DGamma.CP5O19ResolvedOpeningRowSpike
import DGamma.CP5O19ActivationInsertionRowSpike
import DGamma.CP5O19CartesianInsertionSpike
import Data.List
import Decidable.Equality

%default total
%unbound_implicits off

||| Supervisor-authorized D4 representation cure. Four typed ACTUAL pair
||| observations, with source values/equations only. The orientation index
||| allows each producer helper to eliminate exactly ONE constructor. No guard,
||| diamond, replay, row, target state or caller result is stored here.
public export
data O19PairObservation :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (leftParent, rightParent : name) ->
  {first, middle, last : SystemState name key value world error} ->
  (left : Transition first middle) -> (right : Transition middle last) ->
  AdjacentSwapOrientationEvidence left right -> Type where
  ObservedAA :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {leftParent, rightParent : name} ->
    {first, middle, last : SystemState name key value world error} ->
    {left : Transition first middle} -> {right : Transition middle last} ->
    (0 leftActivation : PaperActivationStep left) -> (0 rightActivation : PaperActivationStep right) ->
    (0 leftOwner : transitionActor left = leftParent) -> (0 rightOwner : transitionActor right = rightParent) ->
    O19PairObservation name key world error value leftParent rightParent left right
      (AdjacentActivationActivation left right leftActivation rightActivation)
  ObservedOA :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {leftParent, rightParent : name} ->
    {first, middle, last : SystemState name key value world error} ->
    {left : Transition first middle} -> {right : Transition middle last} ->
    (child : name) -> (component : Component key value world error) ->
    (0 inserted : transitionAction left = OInsert child (ChildOf leftParent) component) ->
    (0 rightActivation : PaperActivationStep right) -> (0 rightOwner : transitionActor right = rightParent) ->
    (0 childSafe : Not (rightParent = child)) ->
    O19PairObservation name key world error value leftParent rightParent left right
      (AdjacentOrchestrationActivation left right (PaperInsertStep inserted) rightActivation)
  ObservedAO :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {leftParent, rightParent : name} ->
    {first, middle, last : SystemState name key value world error} ->
    {left : Transition first middle} -> {right : Transition middle last} ->
    (child : name) -> (component : Component key value world error) ->
    (0 inserted : transitionAction right = OInsert child (ChildOf rightParent) component) ->
    (0 leftActivation : PaperActivationStep left) -> (0 distinct : Not (child = transitionActor left)) ->
    (0 licensing : (licensor : name) -> (ChildOf rightParent = ChildOf licensor) -> Not (transitionActor left = licensor)) ->
    O19PairObservation name key world error value leftParent rightParent left right
      (AdjacentActivationOrchestration left right leftActivation (PaperInsertStep inserted))
  ObservedOO :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {leftParent, rightParent : name} ->
    {first, middle, last : SystemState name key value world error} ->
    {left : Transition first middle} -> {right : Transition middle last} ->
    (leftChild, rightChild : name) -> (leftComponent, rightComponent : Component key value world error) ->
    (0 leftInsert : transitionAction left = OInsert leftChild (ChildOf leftParent) leftComponent) ->
    (0 rightInsert : transitionAction right = OInsert rightChild (ChildOf rightParent) rightComponent) ->
    (0 distinct : Not (rightChild = leftChild)) ->
    (0 leftLicense : (licensor : name) -> (ChildOf leftParent = ChildOf licensor) -> Not (rightChild = licensor)) ->
    (0 rightLicense : (licensor : name) -> (ChildOf rightParent = ChildOf licensor) -> Not (leftChild = licensor)) ->
    (0 tag : transitionTag right = OInsertTag) ->
    O19PairObservation name key world error value leftParent rightParent left right
      (AdjacentOrchestrationOrchestration left right (PaperInsertStep leftInsert) (PaperInsertStep rightInsert))

||| Single-observation A/A producer: only ObservedAA can inhabit this index.
||| Original sanctioned safety and the actual current full bundle derive the
||| backwards guard, then the real diamond/sealed suffix replay is built.
export
0 o19ObservedAAReplay :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, originalFinal, first, middle, last : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder original) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq original) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap original blocks premises) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq original ->
  (cursor : O19ReachedCursor name key world error value protocol nameEq keyEq original) ->
  (earlier : Transitions initial first) -> (left : Transition first middle) -> (right : Transition middle last) ->
  (later : Transitions last (cursorFinal cursor)) ->
  (appendTransitions earlier (MoreTransitions left (MoreTransitions right later)) = cursorTrace cursor) ->
  {leftActivation : PaperActivationStep left} -> {rightActivation : PaperActivationStep right} ->
  O19PairObservation name key world error value (actorLeft swap) (actorRight swap) left right
    (AdjacentActivationActivation left right leftActivation rightActivation) ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq left right **
    AdjacentSwapResult name key world error value protocol nameEq keyEq (cursorTrace cursor) earlier left right later diamond)
o19ObservedAAReplay nameEq keyEq protocol swap original blocks premises safety unique cursor earlier left right later decomposition
  (ObservedAA leftActivation rightActivation leftOwner rightOwner) =
    o19ActivationPairReplay nameEq keyEq protocol (cursorTrace cursor) earlier left right later decomposition (cursorBundle cursor)
      leftActivation rightActivation (\same => actorDistinct swap (trans (sym leftOwner) (trans same rightOwner)))
      (o19ReplayedActivationAligned nameEq keyEq protocol swap original blocks premises safety unique cursor earlier later left right
        decomposition leftOwner rightOwner leftActivation rightActivation
        (fst (o19SourcePairFacts nameEq keyEq protocol (cursorTrace cursor) earlier left right later decomposition (cursorBundle cursor))))
