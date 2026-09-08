module DGamma.CP5O19MixedRowDispatcherSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5O19CartesianCursorSpike
import DGamma.CP5O19ActivationRowSpike
import DGamma.CP5O19ActivationInsertionRowSpike
import DGamma.CP5O19CartesianInsertionSpike
import DGamma.CP5O19MixedActivationRowSpike
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Unified ACTUAL row output for all four A/A, O/A, A/O, O/O orientations.
||| The same output owns its whole bundle, uniqueness, finite derivation,
||| moved labels, exact decomposition and structurally established row count.
public export
record O19MixedRow
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, sourceFinal, before, rightBefore, rightAfter : SystemState name key value world error}
  (source : Transitions initial sourceFinal)
  (earlier : Transitions initial before)
  (sourceRight : Transition rightBefore rightAfter)
  (crossings : Nat) where
  constructor MkO19MixedRow
  mixedRowCursor : O19ReachedCursor name key world error value protocol nameEq keyEq source
  mixedRowMiddle : SystemState name key value world error
  mixedRowRight : Transition before mixedRowMiddle
  mixedRowRest : Transitions mixedRowMiddle (cursorFinal mixedRowCursor)
  0 mixedRowDecomposition : appendTransitions earlier (MoreTransitions mixedRowRight mixedRowRest) = cursorTrace mixedRowCursor
  0 mixedRowAction : transitionAction mixedRowRight = transitionAction sourceRight
  0 mixedRowTag : transitionTag mixedRowRight = transitionTag sourceRight
  0 mixedRowActor : transitionActor mixedRowRight = transitionActor sourceRight
  0 mixedRowClass : Either (PaperActivationStep mixedRowRight) (PaperOrchestrationStep mixedRowRight)
  0 mixedRowNodeCount : finiteAdjacentSwapNodeCount (cursorDerivation mixedRowCursor) = crossings

||| Consume the EXPLICIT activation-row result once, retaining every actual
||| field and its own count proof; no separately evaluated row is observed.
export
0 o19MixedRowFromActivation :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {protocol : RegistrationProtocol key value world error} ->
  {initial, sourceFinal, before, rightBefore, rightAfter : SystemState name key value world error} ->
  {source : Transitions initial sourceFinal} -> {earlier : Transitions initial before} ->
  {right : Transition rightBefore rightAfter} -> {crossings : Nat} ->
  O19ActivationRow name key world error value protocol nameEq keyEq source earlier right crossings ->
  O19MixedRow name key world error value protocol nameEq keyEq source earlier right crossings
o19MixedRowFromActivation (MkO19ActivationRow cursor middle right rest decomposition action tag actor activation count) =
  MkO19MixedRow cursor middle right rest decomposition action tag actor (Left activation) count

||| Same explicit-result boundary for the generated-insertion row producer.
export
0 o19MixedRowFromInsertion :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {protocol : RegistrationProtocol key value world error} ->
  {initial, sourceFinal, before, rightBefore, rightAfter : SystemState name key value world error} ->
  {source : Transitions initial sourceFinal} -> {earlier : Transitions initial before} ->
  {right : Transition rightBefore rightAfter} -> {crossings : Nat} ->
  O19OrchestrationRow name key world error value protocol nameEq keyEq source earlier right crossings ->
  O19MixedRow name key world error value protocol nameEq keyEq source earlier right crossings
o19MixedRowFromInsertion (MkO19OrchestrationRow cursor middle right rest decomposition action tag actor activation count) =
  MkO19MixedRow cursor middle right rest decomposition action tag actor (Right activation) count

||| TOTAL four-orientation row dispatcher, including arbitrary mixed
||| right Begin/Iter/Finish rows and generated-insertion rows. The observed
||| classification contains only source actions/owners/licensing, never guards,
||| diamonds, suffix replays, rows or target traces. Each branch constructs its
||| actual simultaneous bundle/uniqueness/derivation/decomposition/node count.
export
0 o19BubbleMixedRow :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} ->
  (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, originalFinal, sourceFinal, before, rightBefore, rightAfter : SystemState name key value world error} ->
  (original : Transitions initial originalFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder original) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq original) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap original blocks premises) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq original ->
  (source : Transitions initial sourceFinal) ->
  FiniteAdjacentSwapDerivation name key world error value protocol nameEq keyEq original source ->
  (earlier : Transitions initial before) -> (spine : Transitions before rightBefore) ->
  (right : Transition rightBefore rightAfter) -> (later : Transitions rightAfter sourceFinal) ->
  (appendTransitions earlier (appendTransitions spine (MoreTransitions right later)) = source) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq source ->
  UniqueRawNameInsertions name key world error value nameEq keyEq source ->
  (observed : Either
    (PaperActivationStep right, (transitionActor right = actorRight swap),
      ({first, last : SystemState name key value world error} ->
       (step : Transition first last) -> OccursIn step spine ->
       Either (PaperActivationStep step, transitionActor step = actorLeft swap)
         (child : name ** (component : Component key value world error **
           ((transitionAction step = OInsert child (ChildOf (actorLeft swap)) component), Not (actorRight swap = child))))))
    (rightChild : name ** (rightComponent : Component key value world error **
      ((transitionAction right = OInsert rightChild (ChildOf (actorRight swap)) rightComponent), (transitionTag right = OInsertTag),
       ({first, last : SystemState name key value world error} ->
        (step : Transition first last) -> OccursIn step spine ->
        Either
          (PaperActivationStep step, Not (rightChild = transitionActor step),
            ((licensor : name) -> (ChildOf (actorRight swap) = ChildOf licensor) -> Not (transitionActor step = licensor)))
          (leftChild : name ** (leftComponent : Component key value world error **
            ((transitionAction step = OInsert leftChild (ChildOf (actorLeft swap)) leftComponent), Not (rightChild = leftChild),
             ((licensor : name) -> (ChildOf (actorLeft swap) = ChildOf licensor) -> Not (rightChild = licensor)),
             ((licensor : name) -> (ChildOf (actorRight swap) = ChildOf licensor) -> Not (leftChild = licensor)))))))))) ->
  O19MixedRow name key world error value protocol nameEq keyEq source earlier right (transitionCount spine)
o19BubbleMixedRow nameEq keyEq protocol swap original blocks premises safety unique source prior earlier spine right later
  decomposition currentPremises currentUnique (Left (activation, rightOwner, classes)) =
    o19MixedRowFromActivation
      (o19BubbleMixedActivationRow nameEq keyEq protocol swap original blocks premises safety unique source prior earlier spine right later
        decomposition currentPremises currentUnique activation rightOwner classes)
o19BubbleMixedRow nameEq keyEq protocol swap original blocks premises safety unique source prior earlier spine right later
  decomposition currentPremises currentUnique (Right (rightChild ** (rightComponent ** (inserted, tag, classes)))) =
    o19MixedRowFromInsertion
      (o19BubbleMixedInsertionRow nameEq keyEq protocol rightChild (actorLeft swap) (actorRight swap) rightComponent source earlier spine right later
        decomposition currentPremises currentUnique inserted tag classes)
