module DGamma.CP5O20SafeBlockSelectionSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5GeneratedOrchestrationMatched
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5RankedEarlyApplicabilitySpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Exact finite-list location of the two neighboring actors, including the
||| source BeforeIn witness. This does not infer whole-trace block adjacency.
export
0 o20AdjacentListFacts :
  {name : Type} -> (earlier : List name) -> (left, right : name) -> (later : List name) ->
  (Elem left (earlier ++ (left :: right :: later)),
   Elem right (earlier ++ (left :: right :: later)),
   BeforeIn left right (earlier ++ (left :: right :: later)))
o20AdjacentListFacts [] left right later = (Here, There Here, BeforeHere Here)
o20AdjacentListFacts (head :: rest) left right later =
  (There (Builtin.fst (o20AdjacentListFacts rest left right later)),
   There (Builtin.fst (Builtin.snd (o20AdjacentListFacts rest left right later))),
   BeforeThere (Builtin.snd (Builtin.snd (o20AdjacentListFacts rest left right later))))

||| Reindex B1 by the exact source-word equation owned by a chosen pure swap.
||| Only list facts are produced here; B6/B8 check the actual block gap/cut.
export
0 o20ChosenActorFacts :
  {name : Type} -> {sourceOrder, targetOrder : List name} ->
  (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  (Elem (actorLeft swap) sourceOrder, Elem (actorRight swap) sourceOrder,
   BeforeIn (actorLeft swap) (actorRight swap) sourceOrder)
o20ChosenActorFacts {sourceOrder} swap =
  replace {p = \order => (Elem (actorLeft swap) order, Elem (actorRight swap) order,
    BeforeIn (actorLeft swap) (actorRight swap) order)} (sym (actorBeforeExact swap))
      (o20AdjacentListFacts (actorPrefix swap) (actorLeft swap) (actorRight swap) (actorSuffix swap))

||| Executable single-action observation; root insertions are not children.
||| Public computation is required by the next certified negative checker.
public export
o20GeneratedChildName :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  Action name key value world error -> Maybe name
o20GeneratedChildName (OInsert child (ChildOf parent) component) = Just child
o20GeneratedChildName _ = Nothing

||| Certify a negative child observation without deciding component equality.
||| The finite name check is sufficient: an alleged generated insertion must
||| project to the forbidden name under B3.
export
0 o20CheckNoGeneratedAction :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (forbidden : name) ->
  (action : Action name key value world error) ->
  Maybe ((parent : name) -> (component : Component key value world error) ->
    (action = OInsert forbidden (ChildOf parent) component) -> Void)
o20CheckNoGeneratedAction nameEq forbidden action =
  case decEq (o20GeneratedChildName action) (Just forbidden) of
    Yes same => Nothing
    No different => Just (\parent, component, sameAction =>
      different (cong o20GeneratedChildName sameAction))
