module DGamma.CP5O20LinearExtensionSpike

import DGamma.Core
import DGamma.Coeffects
import DGamma.Calculus
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5ConfluenceCrossTraceSpike
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
||| support extension. The target linearization and reverse target-order
||| evidence are retained, but no operational replay/descent is fabricated.
public export
record O20OrientedSafeSwap
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key) (sourceOrder, goalOrder : List name)
  (goalState : SystemState name key value world error)
  {initial, finalState : SystemState name key value world error}
  (trace : Transitions initial finalState)
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder trace)
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq trace) where
  constructor MkO20OrientedSafeSwap
  orientedChoice : O20ChosenSafeSwap name key world error value protocol nameEq keyEq sourceOrder trace blocks premises
  0 orientedGoalLinearization : LinearizesSupport name key world error value nameEq keyEq goalState goalOrder
  0 orientedGoalReverse : BeforeIn (actorRight (chosenOrderSwap orientedChoice)) (actorLeft (chosenOrderSwap orientedChoice)) goalOrder

||| Orient ONE explicitly produced safe choice, never a separately guessed
||| swap. A rejected orientation does not prevent later candidates.
export
0 o20OrientChosenSafeSwap :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} ->
  (nameEq : DecEq name) -> {keyEq : DecEq key} ->
  {sourceOrder : List name} -> (goalOrder : List name) ->
  (goalState : SystemState name key value world error) ->
  LinearizesSupport name key world error value nameEq keyEq goalState goalOrder ->
  {initial, finalState : SystemState name key value world error} -> {trace : Transitions initial finalState} ->
  {blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder trace} ->
  {premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq trace} ->
  O20ChosenSafeSwap name key world error value protocol nameEq keyEq sourceOrder trace blocks premises ->
  Maybe (O20OrientedSafeSwap name key world error value protocol nameEq keyEq sourceOrder goalOrder goalState trace blocks premises)
o20OrientChosenSafeSwap nameEq goalOrder goalState linearization choice =
  map (\reverseOrder => MkO20OrientedSafeSwap choice linearization reverseOrder)
    (o20CheckBefore nameEq (actorRight (chosenOrderSwap choice)) (actorLeft (chosenOrderSwap choice)) goalOrder)

||| Finite positive selection among ALL actual neighboring candidates,
||| filtering both real safety and inversion toward a FIXED accepted target
||| extension. Nothing is NOT canonicality/completeness; operational replay,
||| reached target linearization, reselection and strict descent remain open.
export
0 o20SelectOrientedSafeBlocks :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) -> (sourceOrder, goalOrder : List name) ->
  (goalState : SystemState name key value world error) ->
  LinearizesSupport name key world error value nameEq keyEq goalState goalOrder ->
  {initial, finalState : SystemState name key value world error} -> (trace : Transitions initial finalState) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder trace) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq trace) ->
  (0 unique : UniqueRawNameInsertions name key world error value nameEq keyEq trace) ->
  Maybe (O20OrientedSafeSwap name key world error value protocol nameEq keyEq sourceOrder goalOrder goalState trace blocks premises)
o20SelectOrientedSafeBlocks nameEq keyEq protocol sourceOrder goalOrder goalState linearization trace blocks premises unique =
  head' (mapMaybe
    (\candidate => o20CheckCandidate nameEq keyEq protocol sourceOrder trace blocks premises unique candidate >>=
      o20OrientChosenSafeSwap nameEq goalOrder goalState linearization)
    (o20AdjacentCandidates nameEq sourceOrder [] sourceOrder Refl))
