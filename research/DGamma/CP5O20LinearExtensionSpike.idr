module DGamma.CP5O20LinearExtensionSpike

import DGamma.Core
import DGamma.Coeffects
import DGamma.Calculus
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5O19SurfaceSpike
import DGamma.CP5O20SafeBlockSelectionSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Both exact finite-list members are produced by actual order evidence.
export
0 o20BeforeMembers :
  {name : Type} -> {left, right : name} -> {order : List name} ->
  BeforeIn left right order -> (Elem left order, Elem right order)
o20BeforeMembers (BeforeHere later) = (Here, There later)
o20BeforeMembers (BeforeThere later) =
  (There (fst (o20BeforeMembers later)), There (snd (o20BeforeMembers later)))

||| Strict finite order is asymmetric on the ACTUAL unique enumeration.
||| The proof inspects only list/order constructors, not a swap/effect builder.
export
0 o20BeforeAsymmetric :
  {name : Type} -> {left, right : name} -> {order : List name} ->
  UniqueKeys order -> BeforeIn left right order -> Not (BeforeIn right left order)
o20BeforeAsymmetric (UniqueCons absent unique) (BeforeHere later) (BeforeHere earlier) = absent later
o20BeforeAsymmetric (UniqueCons absent unique) (BeforeHere later) (BeforeThere earlier) =
  absent (snd (o20BeforeMembers earlier))
o20BeforeAsymmetric (UniqueCons absent unique) (BeforeThere later) (BeforeHere earlier) =
  absent (snd (o20BeforeMembers later))
o20BeforeAsymmetric (UniqueCons absent unique) (BeforeThere later) (BeforeThere earlier) =
  o20BeforeAsymmetric unique later earlier

||| Finite positive order checker against the fixed target extension. It
||| returns an actual BeforeIn constructor proof, not Boolean orientation.
export
0 o20CheckBefore :
  {name : Type} -> (nameEq : DecEq name) -> (left, right : name) -> (order : List name) ->
  Maybe (BeforeIn left right order)
o20CheckBefore nameEq left right [] = Nothing
o20CheckBefore nameEq left right (head :: rest) =
  case decEq @{nameEq} left head of
    Yes same => case same of
      Refl => case isElem @{nameEq} right rest of
        Yes member => Just (BeforeHere member)
        No absent => Nothing
    No different => map BeforeThere (o20CheckBefore nameEq left right rest)

||| A genuinely safe actual block swap oriented TOWARD one fixed accepted
||| support extension. Exact target uniqueness and reverse target-order
||| evidence are retained, but no operational replay/descent is fabricated.
public export
record O20OrientedSafeSwap
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key) (sourceOrder, goalOrder : List name)
  {initial, finalState : SystemState name key value world error}
  (trace : Transitions initial finalState)
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder trace)
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq trace) where
  constructor MkO20OrientedSafeSwap
  orientedChoice : O20ChosenSafeSwap name key world error value protocol nameEq keyEq sourceOrder trace blocks premises
  0 orientedGoalUnique : UniqueKeys goalOrder
  0 orientedGoalReverse : BeforeIn (actorRight (chosenOrderSwap orientedChoice)) (actorLeft (chosenOrderSwap orientedChoice)) goalOrder

||| Orient ONE explicitly produced safe choice, never a separately guessed
||| swap. A rejected orientation does not prevent later candidates.
export
0 o20OrientChosenSafeSwap :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} ->
  (nameEq : DecEq name) -> {keyEq : DecEq key} ->
  {sourceOrder : List name} -> (goalOrder : List name) ->
  UniqueKeys goalOrder ->
  {initial, finalState : SystemState name key value world error} -> {trace : Transitions initial finalState} ->
  {blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder trace} ->
  {premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq trace} ->
  O20ChosenSafeSwap name key world error value protocol nameEq keyEq sourceOrder trace blocks premises ->
  Maybe (O20OrientedSafeSwap name key world error value protocol nameEq keyEq sourceOrder goalOrder trace blocks premises)
o20OrientChosenSafeSwap nameEq goalOrder goalUnique choice =
  map (\reverseOrder => MkO20OrientedSafeSwap choice goalUnique reverseOrder)
    (o20CheckBefore nameEq (actorRight (chosenOrderSwap choice)) (actorLeft (chosenOrderSwap choice)) goalOrder)

||| Finite positive selection among ALL actual neighboring candidates,
||| filtering both real safety and inversion toward a FIXED accepted target
||| extension. Nothing is NOT canonicality/completeness. The actual search
||| separately carries the fixed supported reference through reached traces.
export
0 o20SelectOrientedSafeBlocks :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) -> (sourceOrder, goalOrder : List name) ->
  UniqueKeys goalOrder ->
  {initial, finalState : SystemState name key value world error} -> (trace : Transitions initial finalState) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder trace) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq trace) ->
  (0 unique : UniqueRawNameInsertions name key world error value nameEq keyEq trace) ->
  Maybe (O20OrientedSafeSwap name key world error value protocol nameEq keyEq sourceOrder goalOrder trace blocks premises)
o20SelectOrientedSafeBlocks nameEq keyEq protocol sourceOrder goalOrder goalUnique trace blocks premises unique =
  head' (mapMaybe
    (\candidate => o20CheckCandidate nameEq keyEq protocol sourceOrder trace blocks premises unique candidate >>=
      o20OrientChosenSafeSwap nameEq goalOrder goalUnique)
    (o20AdjacentCandidates nameEq sourceOrder [] sourceOrder Refl))

||| The same pair cannot also be oriented the opposite way in this fixed
||| accepted unique target order. This rules out the immediate inverse
||| orientation, not an arbitrary operational cycle or a global descent.
export
0 o20OrientedCannotReverse :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} -> {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {sourceOrder, goalOrder : List name} ->
  {initial, finalState : SystemState name key value world error} -> {trace : Transitions initial finalState} ->
  {blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder trace} ->
  {premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq trace} ->
  (choice : O20OrientedSafeSwap name key world error value protocol nameEq keyEq sourceOrder goalOrder trace blocks premises) ->
  Not (BeforeIn (actorLeft (chosenOrderSwap (orientedChoice choice))) (actorRight (chosenOrderSwap (orientedChoice choice))) goalOrder)
o20OrientedCannotReverse choice =
  o20BeforeAsymmetric (orientedGoalUnique choice) (orientedGoalReverse choice)

||| Matched-head branch of the ACTUAL target-order checker. Both primitive
||| decisions are authenticated separately; only membership is eliminated.
export
0 o20BeforeMatchedMemberObserved :
  {name : Type} -> (nameEq : DecEq name) -> (left, right : name) -> (rest : List name) ->
  (decEq @{nameEq} left left = Yes Refl) ->
  (observed : Dec (Elem right rest)) -> (isElem @{nameEq} right rest = observed) ->
  Elem right rest -> (isJust (o20CheckBefore nameEq left right (left :: rest)) = True)
o20BeforeMatchedMemberObserved nameEq left right rest same (Yes member) exact present =
  rewrite same in rewrite exact in Refl
o20BeforeMatchedMemberObserved nameEq left right rest same (No absent) exact present =
  void (absent present)

||| Producer-owned name-decision boundary for target-order completeness.
||| The caller supplies structural membership/induction facts, not a success
||| assertion for this head. No visibility change to the native checker.
export
0 o20BeforeOwnerDecisionObserved :
  {name : Type} -> (nameEq : DecEq name) -> (left, right, head : name) -> (rest : List name) ->
  (observed : Dec (left = head)) -> (decEq @{nameEq} left head = observed) ->
  Elem right rest ->
  (Not (left = head) -> (isJust (map (BeforeThere {other = head}) (o20CheckBefore nameEq left right rest)) = True)) ->
  (isJust (o20CheckBefore nameEq left right (head :: rest)) = True)
o20BeforeOwnerDecisionObserved nameEq left right _ rest (Yes Refl) exact member smaller =
  o20BeforeMatchedMemberObserved nameEq left right rest exact (isElem @{nameEq} right rest) Refl member
o20BeforeOwnerDecisionObserved nameEq left right head rest (No different) exact member smaller =
  rewrite exact in smaller different

||| Exact observed target-order success is preserved by the native orientation
||| producer. This equation is proved at its defining module, not by exposing
||| or changing an imported declaration's visibility.
export
0 o20OrientChoiceObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} ->
  (nameEq : DecEq name) -> {keyEq : DecEq key} ->
  {sourceOrder : List name} -> (goalOrder : List name) ->
  (goalUnique : UniqueKeys goalOrder) ->
  {initial, finalState : SystemState name key value world error} -> {trace : Transitions initial finalState} ->
  {blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder trace} ->
  {premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq trace} ->
  (choice : O20ChosenSafeSwap name key world error value protocol nameEq keyEq sourceOrder trace blocks premises) ->
  (observed : Maybe (BeforeIn (actorRight (chosenOrderSwap choice)) (actorLeft (chosenOrderSwap choice)) goalOrder)) ->
  (o20CheckBefore nameEq (actorRight (chosenOrderSwap choice)) (actorLeft (chosenOrderSwap choice)) goalOrder = observed) ->
  (isJust observed = True) -> (isJust (o20OrientChosenSafeSwap nameEq goalOrder goalUnique choice) = True)
o20OrientChoiceObserved nameEq goalOrder goalUnique choice Nothing exact Refl impossible
o20OrientChoiceObserved nameEq goalOrder goalUnique choice (Just reverseOrder) exact present =
  rewrite exact in Refl

||| Exact native selector expression, exposed at its owning module without
||| changing visibility or selecting a second, independently computed packet.
export
0 o20OrientedSelectorOwnedEquation :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) -> (sourceOrder, goalOrder : List name) ->
  (goalUnique : UniqueKeys goalOrder) ->
  {initial, finalState : SystemState name key value world error} -> (trace : Transitions initial finalState) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder trace) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq trace) ->
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq trace) ->
  (o20SelectOrientedSafeBlocks nameEq keyEq protocol sourceOrder goalOrder goalUnique trace blocks premises unique =
   head' (mapMaybe
    (\candidate => o20CheckCandidate nameEq keyEq protocol sourceOrder trace blocks premises unique candidate >>=
      o20OrientChosenSafeSwap nameEq goalOrder goalUnique)
    (o20AdjacentCandidates nameEq sourceOrder [] sourceOrder Refl)))
o20OrientedSelectorOwnedEquation nameEq keyEq protocol sourceOrder goalOrder goalUnique trace blocks premises unique = Refl
