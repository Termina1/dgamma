module DGamma.CP5O20SelectionCompletenessSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5O19SurfaceSpike
import DGamma.CP5O20SafeBlockSelectionSpike
import DGamma.CP5O20LinearExtensionSpike
import DGamma.CP5O20OperationalProgressSpike
import DGamma.CP5O20OperationalDescentSpike
import DGamma.CP5O20RightOpeningTransportSpike
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5RankedEarlyApplicabilitySpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Map preserves actual Maybe success without selecting or equating payloads.
export
0 o20MapMaybePresent : {a, b : Type} -> (make : a -> b) ->
  (source : Maybe a) -> isJust source = True -> isJust (map make source) = True
o20MapMaybePresent make Nothing Refl impossible
o20MapMaybePresent make (Just value) present = Refl

||| Any strict BeforeIn on a nonempty list puts its RIGHT member in the tail.
export
0 o20BeforeRightInTail :
  {name : Type} -> {left, right, head : name} -> {rest : List name} ->
  BeforeIn left right (head :: rest) -> Elem right rest
o20BeforeRightInTail (BeforeHere member) = member
o20BeforeRightInTail (BeforeThere later) = snd (o20BeforeMembers later)

||| Distinct left/head names eliminate only the BeforeIn head constructor;
||| no flat multi-block order split or nonlinear name pattern is needed.
export
0 o20BeforeDifferentHeadTail :
  {name : Type} -> {left, right, head : name} -> {rest : List name} ->
  Not (left = head) -> BeforeIn left right (head :: rest) -> BeforeIn left right rest
o20BeforeDifferentHeadTail different (BeforeHere member) = void (different Refl)
o20BeforeDifferentHeadTail different (BeforeThere later) = later

||| COMPLETE actual target BeforeIn checker by structural order induction.
||| Distinctness and membership come from the original order witness; no
||| successful check is a caller premise and no target payload is equated.
export
0 o20CheckBeforeComplete :
  {name : Type} -> (nameEq : DecEq name) -> (left, right : name) -> (order : List name) ->
  BeforeIn left right order -> (isJust (o20CheckBefore nameEq left right order) = True)
o20CheckBeforeComplete nameEq left right [] ordered impossible
o20CheckBeforeComplete nameEq left right (head :: rest) ordered =
  o20BeforeOwnerDecisionObserved nameEq left right head rest (decEq @{nameEq} left head) Refl
    (o20BeforeRightInTail ordered)
    (\different => o20MapMaybePresent (BeforeThere {other = head}) (o20CheckBefore nameEq left right rest)
      (o20CheckBeforeComplete nameEq left right rest (o20BeforeDifferentHeadTail different ordered)))

||| COMPLETE actual orientation for any actual safe choice whose right actor
||| precedes its left in the fixed goal. Enumeration and safety completeness
||| are separate; no successful order-check result is assumed here.
export
0 o20OrientChosenSafeSwapComplete :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} ->
  (nameEq : DecEq name) -> {keyEq : DecEq key} ->
  {sourceOrder : List name} -> (goalOrder : List name) ->
  (goalUnique : UniqueKeys goalOrder) ->
  {initial, finalState : SystemState name key value world error} -> {trace : Transitions initial finalState} ->
  {blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder trace} ->
  {premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq trace} ->
  (choice : O20ChosenSafeSwap name key world error value protocol nameEq keyEq sourceOrder trace blocks premises) ->
  BeforeIn (actorRight (chosenOrderSwap choice)) (actorLeft (chosenOrderSwap choice)) goalOrder ->
  (isJust (o20OrientChosenSafeSwap nameEq goalOrder goalUnique choice) = True)
o20OrientChosenSafeSwapComplete nameEq goalOrder goalUnique choice reverseOrder =
  o20OrientChoiceObserved nameEq goalOrder goalUnique choice
    (o20CheckBefore nameEq (actorRight (chosenOrderSwap choice)) (actorLeft (chosenOrderSwap choice)) goalOrder) Refl
    (o20CheckBeforeComplete nameEq (actorRight (chosenOrderSwap choice)) (actorLeft (chosenOrderSwap choice)) goalOrder reverseOrder)

||| COMPLETE actual candidate checker from the FOUR logical clauses at its
||| OWN member-selected cuts. These clauses remain explicit obligations, not
||| claimed to follow merely from order inversion or an enumerated candidate.
export
0 o20CandidateCompleteAtOwnSlots :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) -> (sourceOrder, targetOrder : List name) ->
  (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, finalState : SystemState name key value world error} -> (trace : Transitions initial finalState) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder trace) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq trace) ->
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq trace) ->
  NoGeneratedChild (actorRight swap) (blockBody (decomposedBlock blocks (actorLeft swap) (Builtin.fst (o20ChosenActorFacts swap)))) ->
  NoGeneratedChild (actorLeft swap) (blockBody (decomposedBlock blocks (actorRight swap) (Builtin.fst (Builtin.snd (o20ChosenActorFacts swap))))) ->
  CheckedEarlyApplication name key world error value nameEq keyEq
    (blockPreStart (decomposedBlock blocks (actorLeft swap) (Builtin.fst (o20ChosenActorFacts swap)))) (LBegin (actorRight swap)) LBeginTag ->
  (transitionCount (betweenBlocks (decomposedBlocksFollowOrder blocks (actorLeft swap) (actorRight swap)
    (Builtin.fst (o20ChosenActorFacts swap)) (Builtin.fst (Builtin.snd (o20ChosenActorFacts swap))) (Builtin.snd (Builtin.snd (o20ChosenActorFacts swap))))) = 0) ->
  (isJust (o20CheckCandidate nameEq keyEq protocol sourceOrder trace blocks premises unique (targetOrder ** swap)) = True)
o20CandidateCompleteAtOwnSlots nameEq keyEq protocol sourceOrder targetOrder swap trace blocks premises unique leftSafe rightSafe early adjacent =
  rewrite o20CandidateOwnedEquation nameEq keyEq protocol sourceOrder trace blocks premises unique targetOrder swap in
    o20MapMaybePresent (\safety => MkO20ChosenSafeSwap targetOrder swap safety unique)
      (o20CheckSafetyAtMembers nameEq keyEq protocol swap trace blocks premises (Builtin.fst (o20ChosenActorFacts swap)) (Builtin.fst (Builtin.snd (o20ChosenActorFacts swap))) (Builtin.snd (Builtin.snd (o20ChosenActorFacts swap))))
      (o20CheckSafetyAtMembersComplete nameEq keyEq protocol swap trace blocks premises
        (Builtin.fst (o20ChosenActorFacts swap)) (Builtin.fst (Builtin.snd (o20ChosenActorFacts swap))) (Builtin.snd (Builtin.snd (o20ChosenActorFacts swap))) leftSafe rightSafe early adjacent)

||| Single Maybe elimination retains the actual constructed payload across
||| the selector's map/bind seam. No computed existential payload is equated.
export
0 o20MappedBindPresent : {a, b, c : Type} -> (make : a -> b) -> (next : b -> Maybe c) ->
  (source : Maybe a) -> (isJust (map make source) = True) ->
  ((payload : a) -> (isJust (next (make payload)) = True)) ->
  (isJust (map make source >>= next) = True)
o20MappedBindPresent make next Nothing Refl each impossible
o20MappedBindPresent make next (Just payload) present each = each payload

||| Native candidate and orientation are BOTH complete for the same safety
||| payload and the same fixed target order. Four actual safety clauses remain
||| explicit; no successful orientation or swapped endpoint is a premise.
export
0 o20OrientedCandidateCompleteAtOwnSlots :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) -> (sourceOrder, targetOrder, goalOrder : List name) ->
  (goalUnique : UniqueKeys goalOrder) ->
  (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, finalState : SystemState name key value world error} -> (trace : Transitions initial finalState) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder trace) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq trace) ->
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq trace) ->
  BeforeIn (actorRight swap) (actorLeft swap) goalOrder ->
  NoGeneratedChild (actorRight swap) (blockBody (decomposedBlock blocks (actorLeft swap) (Builtin.fst (o20ChosenActorFacts swap)))) ->
  NoGeneratedChild (actorLeft swap) (blockBody (decomposedBlock blocks (actorRight swap) (Builtin.fst (Builtin.snd (o20ChosenActorFacts swap))))) ->
  CheckedEarlyApplication name key world error value nameEq keyEq
    (blockPreStart (decomposedBlock blocks (actorLeft swap) (Builtin.fst (o20ChosenActorFacts swap)))) (LBegin (actorRight swap)) LBeginTag ->
  (transitionCount (betweenBlocks (decomposedBlocksFollowOrder blocks (actorLeft swap) (actorRight swap)
    (Builtin.fst (o20ChosenActorFacts swap)) (Builtin.fst (Builtin.snd (o20ChosenActorFacts swap))) (Builtin.snd (Builtin.snd (o20ChosenActorFacts swap))))) = 0) ->
  (isJust (o20CheckCandidate nameEq keyEq protocol sourceOrder trace blocks premises unique (targetOrder ** swap) >>=
    o20OrientChosenSafeSwap nameEq goalOrder goalUnique) = True)
o20OrientedCandidateCompleteAtOwnSlots nameEq keyEq protocol sourceOrder targetOrder goalOrder goalUnique swap trace blocks premises unique reverseOrder leftSafe rightSafe early adjacent =
  rewrite o20CandidateOwnedEquation nameEq keyEq protocol sourceOrder trace blocks premises unique targetOrder swap in
    o20MappedBindPresent (\safety => MkO20ChosenSafeSwap targetOrder swap safety unique)
      (o20OrientChosenSafeSwap nameEq goalOrder goalUnique)
      (o20CheckSafetyAtMembers nameEq keyEq protocol swap trace blocks premises (Builtin.fst (o20ChosenActorFacts swap)) (Builtin.fst (Builtin.snd (o20ChosenActorFacts swap))) (Builtin.snd (Builtin.snd (o20ChosenActorFacts swap))))
      (trans (cong isJust (sym (o20CandidateOwnedEquation nameEq keyEq protocol sourceOrder trace blocks premises unique targetOrder swap)))
        (o20CandidateCompleteAtOwnSlots nameEq keyEq protocol sourceOrder targetOrder swap trace blocks premises unique leftSafe rightSafe early adjacent))
      (\safety => o20OrientChosenSafeSwapComplete nameEq goalOrder goalUnique
        (MkO20ChosenSafeSwap targetOrder swap safety unique) reverseOrder)

||| WHOLE native finite selector cannot miss an enumerated candidate whose
||| OWN four logical safety clauses and target orientation hold. Enumeration
||| is producer-owned by E28/E31; semantic safety production and stopped-order
||| equality remain separate, openly stated debts.
export
0 o20SelectEnumeratedComplete :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) -> (sourceOrder, goalOrder : List name) ->
  (goalUnique : UniqueKeys goalOrder) ->
  {initial, finalState : SystemState name key value world error} -> (trace : Transitions initial finalState) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder trace) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq trace) ->
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq trace) ->
  {left, right : name} ->
  (packet : O20EnumeratedPair name sourceOrder
    (o20AdjacentCandidates nameEq sourceOrder [] sourceOrder Refl) left right) ->
  BeforeIn (actorRight (enumeratedSwap packet)) (actorLeft (enumeratedSwap packet)) goalOrder ->
  NoGeneratedChild (actorRight (enumeratedSwap packet)) (blockBody (decomposedBlock blocks (actorLeft (enumeratedSwap packet)) (Builtin.fst (o20ChosenActorFacts (enumeratedSwap packet))))) ->
  NoGeneratedChild (actorLeft (enumeratedSwap packet)) (blockBody (decomposedBlock blocks (actorRight (enumeratedSwap packet)) (Builtin.fst (Builtin.snd (o20ChosenActorFacts (enumeratedSwap packet)))))) ->
  CheckedEarlyApplication name key world error value nameEq keyEq
    (blockPreStart (decomposedBlock blocks (actorLeft (enumeratedSwap packet)) (Builtin.fst (o20ChosenActorFacts (enumeratedSwap packet))))) (LBegin (actorRight (enumeratedSwap packet))) LBeginTag ->
  (transitionCount (betweenBlocks (decomposedBlocksFollowOrder blocks (actorLeft (enumeratedSwap packet)) (actorRight (enumeratedSwap packet))
    (Builtin.fst (o20ChosenActorFacts (enumeratedSwap packet))) (Builtin.fst (Builtin.snd (o20ChosenActorFacts (enumeratedSwap packet)))) (Builtin.snd (Builtin.snd (o20ChosenActorFacts (enumeratedSwap packet)))))) = 0) ->
  (isJust (o20SelectOrientedSafeBlocks nameEq keyEq protocol sourceOrder goalOrder goalUnique trace blocks premises unique) = True)
o20SelectEnumeratedComplete nameEq keyEq protocol sourceOrder goalOrder goalUnique trace blocks premises unique packet reverseOrder leftSafe rightSafe early adjacent =
  rewrite o20OrientedSelectorOwnedEquation nameEq keyEq protocol sourceOrder goalOrder goalUnique trace blocks premises unique in
    o20MapMaybeSelectionComplete
      (\candidate => o20CheckCandidate nameEq keyEq protocol sourceOrder trace blocks premises unique candidate >>=
        o20OrientChosenSafeSwap nameEq goalOrder goalUnique)
      (o20AdjacentCandidates nameEq sourceOrder [] sourceOrder Refl)
      (enumeratedTarget packet ** enumeratedSwap packet) (enumeratedMember packet)
      (o20OrientedCandidateCompleteAtOwnSlots nameEq keyEq protocol sourceOrder (enumeratedTarget packet)
        goalOrder goalUnique (enumeratedSwap packet) trace blocks premises unique reverseOrder leftSafe rightSafe early adjacent)
