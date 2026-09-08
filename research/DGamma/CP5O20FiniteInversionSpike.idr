module DGamma.CP5O20FiniteInversionSpike

import DGamma.Coeffects
import DGamma.Calculus
import DGamma.CP3
import DGamma.CP5O19SurfaceSpike
import DGamma.CP5O20LinearExtensionSpike
import DGamma.CP5O20SupportedReferenceSpike
import DGamma.CP5O20ReferenceDescentSpike
import DGamma.CP5O20OperationalDescentSpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import Data.List
import Data.List.Elem
import Decidable.Equality

%default total
%unbound_implicits off

||| Pure finite inversion availability capital. It owns the precise adjacent
||| swap and reverse goal order, but does NOT assert actual block safety.
public export
record O20FiniteInversion (name : Type) (sourceOrder, goalOrder : List name) where
  constructor MkO20FiniteInversion
  0 invertedOrder : List name
  0 invertedSwap : AdjacentActorOrderSwap name sourceOrder invertedOrder
  0 invertedGoalBefore : BeforeIn (actorRight invertedSwap) (actorLeft invertedSwap) goalOrder

||| A later inversion remains the SAME selected pair under a source head.
export
0 o20InversionUnderSourceHead :
  {name : Type} -> {sourceOrder, goalOrder : List name} -> (head : name) ->
  O20FiniteInversion name sourceOrder goalOrder -> O20FiniteInversion name (head :: sourceOrder) goalOrder
o20InversionUnderSourceHead head
  (MkO20FiniteInversion target (MkAdjacentActorOrderSwap leading left right trailing beforeExact afterExact distinct) reverseOrder) =
    MkO20FiniteInversion (head :: target)
      (MkAdjacentActorOrderSwap (head :: leading) left right trailing
        (cong (head ::) beforeExact) (cong (head ::) afterExact) distinct) reverseOrder

||| Goal-head extension changes only the reverse-order evidence.
export
0 o20InversionUnderGoalHead :
  {name : Type} -> {sourceOrder, goalOrder : List name} -> (head : name) ->
  O20FiniteInversion name sourceOrder goalOrder -> O20FiniteInversion name sourceOrder (head :: goalOrder)
o20InversionUnderGoalHead head (MkO20FiniteInversion target swap reverseOrder) =
  MkO20FiniteInversion target swap (BeforeThere reverseOrder)

||| Remove a provably different head from membership, constructively.
export
0 o20DifferentHeadMember :
  {name : Type} -> {selected, head : name} -> {rest : List name} ->
  Not (selected = head) -> Elem selected (head :: rest) -> Elem selected rest
o20DifferentHeadMember different Here = absurd (different Refl)
o20DifferentHeadMember different (There inside) = inside

||| Common-head cancellation for a finite enumeration map. The source head
||| absence prevents incorrectly mapping a tail element to the target head.
export
0 o20CancelHeadMembership :
  {name : Type} -> {head, selected : name} -> {sourceTail, goalTail : List name} ->
  Not (Elem head sourceTail) -> Elem selected sourceTail -> Elem selected (head :: goalTail) -> Elem selected goalTail
o20CancelHeadMembership absent selectedIn Here = absurd (absent selectedIn)
o20CancelHeadMembership absent selectedIn (There targetIn) = targetIn

||| If the goal minimum is later in the source, its IMMEDIATE predecessor
||| forms a precise adjacent inversion. Recursion follows that actual member.
export
0 o20InversionBeforeGoalMinimum :
  {name : Type} -> (head, minimum : name) -> (rest, goalRest : List name) ->
  UniqueKeys (head :: rest) ->
  ((selected : name) -> Elem selected (head :: rest) -> Elem selected (minimum :: goalRest)) ->
  Elem minimum rest -> O20FiniteInversion name (head :: rest) (minimum :: goalRest)
o20InversionBeforeGoalMinimum head minimum [] goalRest unique members found impossible
o20InversionBeforeGoalMinimum head minimum (minimum :: rest) goalRest (UniqueCons absent uniqueRest) members Here =
  MkO20FiniteInversion (minimum :: head :: rest)
    (MkAdjacentActorOrderSwap [] head minimum rest Refl Refl (\Refl => absent Here))
    (BeforeHere (o20DifferentHeadMember (\Refl => absent Here) (members head Here)))
o20InversionBeforeGoalMinimum head minimum (next :: rest) goalRest (UniqueCons absent uniqueRest) members (There found) =
  o20InversionUnderSourceHead head
    (o20InversionBeforeGoalMinimum next minimum rest goalRest uniqueRest
      (\selected, inside => members selected (There inside)) found)

||| Finite inversion availability, NOT a sorting oracle: unique orders of
||| exactly the same names are equal or own an adjacent goal inversion.
||| The unequal-head branch finds the goal minimum's actual predecessor;
||| the equal-head branch recurses on the strictly shorter two tails.
export
0 o20FiniteInversionAvailable :
  {name : Type} -> (nameEq : DecEq name) -> (sourceOrder, goalOrder : List name) ->
  UniqueKeys sourceOrder -> UniqueKeys goalOrder ->
  ((selected : name) -> Elem selected sourceOrder -> Elem selected goalOrder) ->
  ((selected : name) -> Elem selected goalOrder -> Elem selected sourceOrder) ->
  Either (sourceOrder = goalOrder) (O20FiniteInversion name sourceOrder goalOrder)
o20FiniteInversionAvailable nameEq [] [] sourceUnique goalUnique forward backward = Left Refl
o20FiniteInversionAvailable nameEq [] (minimum :: goalRest) sourceUnique goalUnique forward backward =
  absurd (backward minimum Here)
o20FiniteInversionAvailable nameEq (head :: rest) [] sourceUnique goalUnique forward backward =
  absurd (forward head Here)
o20FiniteInversionAvailable nameEq (head :: rest) (minimum :: goalRest)
  (UniqueCons sourceAbsent sourceUnique) (UniqueCons goalAbsent goalUnique) forward backward =
    case decEq @{nameEq} head minimum of
      Yes Refl => case o20FiniteInversionAvailable nameEq rest goalRest sourceUnique goalUnique
        (\selected, inside => o20CancelHeadMembership sourceAbsent inside (forward selected (There inside)))
        (\selected, inside => o20CancelHeadMembership goalAbsent inside (backward selected (There inside))) of
          Left same => Left (cong (head ::) same)
          Right inversion => Right (o20InversionUnderSourceHead head (o20InversionUnderGoalHead head inversion))
      No different => Right (o20InversionBeforeGoalMinimum head minimum rest goalRest
        (UniqueCons sourceAbsent sourceUnique) forward
        (o20DifferentHeadMember (\same => different (sym same)) (backward minimum Here)))

||| The common supported reference already owns every enumeration premise
||| of finite inversion availability; no permutation/certificate is supplied.
export
0 o20ReferenceInversionAvailable :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> {keyEq : DecEq key} ->
  {reference : SystemState name key value world error} -> (sourceOrder, goalOrder : List name) ->
  O20SupportedReferenceOrders name key world error value nameEq keyEq reference sourceOrder goalOrder ->
  Either (sourceOrder = goalOrder) (O20FiniteInversion name sourceOrder goalOrder)
o20ReferenceInversionAvailable nameEq sourceOrder goalOrder capital =
  o20FiniteInversionAvailable nameEq sourceOrder goalOrder
    (referenceSourceUnique capital) (referenceGoalUnique capital)
    (referenceMembersForward capital) (referenceMembersBackward capital)

||| The ACTUAL stopped search is either at its goal or still owns a finite
||| adjacent inversion. This prevents confusing blocked/rejected with sorted.
export
0 o20StoppedInversionAvailable :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} ->
  (nameEq : DecEq name) -> {keyEq : DecEq key} ->
  {sourceOrder, goalOrder : List name} -> {reference : SystemState name key value world error} ->
  {goalUnique : UniqueKeys goalOrder} ->
  {initial, finalState : SystemState name key value world error} -> {trace : Transitions initial finalState} ->
  {blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder trace} ->
  {premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq trace} ->
  (result : O20ReferenceStoppedPermutation name key world error value protocol nameEq keyEq
    sourceOrder goalOrder reference goalUnique trace blocks premises) ->
  Either (stoppedOrder (referenceStopped result) = goalOrder)
    (O20FiniteInversion name (stoppedOrder (referenceStopped result)) goalOrder)
o20StoppedInversionAvailable {goalOrder} nameEq result =
  o20ReferenceInversionAvailable nameEq (stoppedOrder (referenceStopped result)) goalOrder (referenceStoppedOrders result)
