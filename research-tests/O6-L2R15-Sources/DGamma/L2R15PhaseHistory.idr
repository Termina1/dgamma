module DGamma.L2R15PhaseHistory

import Builtin
import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import Prelude.EqOrd
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R7Classifier
import DGamma.L2R10PhaseScan
import DGamma.L2R13ForcedAnchor
import Data.Bool
import Data.List
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Structural contiguous-history certificate, indexed by the EXACT event
||| word and release distance. Release needs history established BEFORE it;
||| an owned event carries history, whereas a reset must establish new life
||| entirely in its tail. False initial history therefore cannot count the
||| release's own flag as earlier life. Native interval localization remains
||| separate from this event-word datatype and its later decoder.
public export
data PhaseHistoryPath : {name : Type} -> (actor : name) -> Bool -> Nat -> List (Maybe name, Bool) -> Type where
  HistoryRelease : {name : Type} -> {actor : name} -> {owner : Maybe name} ->
    {flag : Bool} -> {rest : List (Maybe name, Bool)} ->
    (0 owned : owner = Just actor) -> PhaseHistoryPath actor True 0 ((owner, flag) :: rest)
  HistoryOwned : {name : Type} -> {actor : name} -> {owner : Maybe name} ->
    {seen, flag : Bool} -> {distance : Nat} -> {rest : List (Maybe name, Bool)} ->
    (0 owned : owner = Just actor) -> PhaseHistoryPath actor (seen || flag) distance rest ->
    PhaseHistoryPath actor seen (S distance) ((owner, flag) :: rest)
  HistoryReset : {name : Type} -> {actor : name} -> {event : (Maybe name, Bool)} ->
    {seen : Bool} -> {distance : Nat} -> {rest : List (Maybe name, Bool)} ->
    PhaseHistoryPath actor False distance rest -> PhaseHistoryPath actor seen (S distance) (event :: rest)

||| Reflect the actual library owner decision. Its observed equation is
||| supplied at the native call site; no reconstructed equality test is used.
export
0 phaseOwnerAtDecision : {name : Type} -> (nameEq : DecEq name) ->
  (actor, owner : name) -> (decision : Dec (actor = owner)) ->
  (0 equation : decEq @{nameEq} actor owner = decision) ->
  (0 accepted : isYes (decEq @{nameEq} actor owner) = True) -> owner = actor
phaseOwnerAtDecision nameEq actor owner (Yes equal) equation accepted = sym equal
phaseOwnerAtDecision nameEq actor owner (No different) equation accepted =
  absurd (trans (sym (cong isYes equation)) accepted)

||| An accepted Maybe-owner test produces actual actor identity. Absence
||| rejects, and the present case observes decEq through its own equation.
export
0 phaseMaybeOwnerDecoded : {name : Type} -> (nameEq : DecEq name) ->
  (actor : name) -> (owner : Maybe name) ->
  (0 accepted : maybe False (\selected => isYes (decEq @{nameEq} actor selected)) owner = True) ->
  owner = Just actor
phaseMaybeOwnerDecoded nameEq actor Nothing accepted = absurd accepted
phaseMaybeOwnerDecoded nameEq actor (Just owner) accepted =
  cong Just (phaseOwnerAtDecision nameEq actor owner (decEq @{nameEq} actor owner) Refl accepted)

||| Eliminate the OBSERVED owner Bool before constructing a history path.
||| A foreign/missing event resets prior life; an owned event preserves the
||| native seenLife-or-lifecycle update, so contiguity is not postulated.
export
0 phaseHistoryPastOwner : {name : Type} -> (nameEq : DecEq name) ->
  (actor : name) -> (owner : Maybe name) -> (seen, flag : Bool) ->
  (distance : Nat) -> (rest : List (Maybe name, Bool)) -> (owned : Bool) ->
  (0 equation : maybe False (\selected => isYes (decEq @{nameEq} actor selected)) owner = owned) ->
  PhaseHistoryPath actor (owned && (seen || flag)) distance rest ->
  PhaseHistoryPath actor seen (S distance) ((owner, flag) :: rest)
phaseHistoryPastOwner nameEq actor owner seen flag distance rest True equation path =
  HistoryOwned (phaseMaybeOwnerDecoded nameEq actor owner equation) path
phaseHistoryPastOwner nameEq actor owner seen flag distance rest False equation path = HistoryReset path

||| Decode only the observed physical-position guard. The recursive tail
||| decoder is a structural induction hypothesis. Exact count arithmetic is
||| retained together with the path, not inferred from a Boolean label.
export
0 phaseHistoryAtPositionGuard : {name : Type} -> (nameEq : DecEq name) ->
  (actor : name) -> (offset, release : Nat) -> (seen : Bool) ->
  (owner : Maybe name) -> (flag : Bool) -> (rest : List (Maybe name, Bool)) ->
  (0 tailDecoder : (nextSeen : Bool) ->
    phaseReleaseCheck nameEq actor (S offset) release nextSeen rest = True ->
    (distance : Nat ** (S offset + distance = release, PhaseHistoryPath actor nextSeen distance rest))) ->
  (matched : Bool) -> (0 position : (offset == release) = matched) ->
  (0 accepted : (if matched then seen && maybe False (\selected => isYes (decEq @{nameEq} actor selected)) owner
    else phaseReleaseCheck nameEq actor (S offset) release
      (maybe False (\selected => isYes (decEq @{nameEq} actor selected)) owner && (seen || flag)) rest) = True) ->
  (distance : Nat ** (offset + distance = release, PhaseHistoryPath actor seen distance ((owner, flag) :: rest)))
phaseHistoryAtPositionGuard nameEq actor offset release seen owner flag rest tailDecoder True position accepted =
  (0 ** (trans (plusZeroRightNeutral offset) (phaseNatEqual offset release position),
    replace {p = \prior => PhaseHistoryPath actor prior 0 ((owner, flag) :: rest)}
      (sym (boolAndLeft seen (maybe False (\selected => isYes (decEq @{nameEq} actor selected)) owner) accepted))
      (HistoryRelease (phaseMaybeOwnerDecoded nameEq actor owner
        (boolAndRight seen (maybe False (\selected => isYes (decEq @{nameEq} actor selected)) owner) accepted)))))
phaseHistoryAtPositionGuard nameEq actor offset release seen owner flag rest tailDecoder False position accepted =
  (S (fst (tailDecoder (maybe False (\selected => isYes (decEq @{nameEq} actor selected)) owner && (seen || flag)) accepted)) **
    (trans (sym (plusSuccRightSucc offset (fst (tailDecoder (maybe False (\selected => isYes (decEq @{nameEq} actor selected)) owner && (seen || flag)) accepted))))
      (fst (snd (tailDecoder (maybe False (\selected => isYes (decEq @{nameEq} actor selected)) owner && (seen || flag)) accepted))),
     phaseHistoryPastOwner nameEq actor owner seen flag
       (fst (tailDecoder (maybe False (\selected => isYes (decEq @{nameEq} actor selected)) owner && (seen || flag)) accepted)) rest
       (maybe False (\selected => isYes (decEq @{nameEq} actor selected)) owner) Refl
       (snd (snd (tailDecoder (maybe False (\selected => isYes (decEq @{nameEq} actor selected)) owner && (seen || flag)) accepted)))))

||| Preserve the NATIVE scanner domain until its physical guard is observed.
||| Rewriting that domain only after Bool elimination avoids equating two
||| independently reconstructed lazy-if families under a stuck guard.
export
0 phaseHistoryAtNativePosition : {name : Type} -> (nameEq : DecEq name) ->
  (actor : name) -> (offset, release : Nat) -> (seen : Bool) ->
  (owner : Maybe name) -> (flag : Bool) -> (rest : List (Maybe name, Bool)) ->
  (0 tailDecoder : (nextSeen : Bool) ->
    phaseReleaseCheck nameEq actor (S offset) release nextSeen rest = True ->
    (distance : Nat ** (S offset + distance = release, PhaseHistoryPath actor nextSeen distance rest))) ->
  (matched : Bool) -> (0 position : (offset == release) = matched) ->
  (0 accepted : phaseReleaseCheck nameEq actor offset release seen ((owner, flag) :: rest) = True) ->
  (distance : Nat ** (offset + distance = release, PhaseHistoryPath actor seen distance ((owner, flag) :: rest)))
phaseHistoryAtNativePosition nameEq actor offset release seen owner flag rest tailDecoder True position =
  rewrite position in phaseHistoryAtPositionGuard nameEq actor offset release seen owner flag rest tailDecoder True position
phaseHistoryAtNativePosition nameEq actor offset release seen owner flag rest tailDecoder False position =
  rewrite position in phaseHistoryAtPositionGuard nameEq actor offset release seen owner flag rest tailDecoder False position

||| GENERAL decoder of the ACTUAL phaseReleaseCheck, through A13's native
||| guard bridge. Produces exact release distance and owner-contiguous
||| history. Feed phaseSeedNativeHistory for the actual release actor; the
||| physical core/lifecycle occurrence and local release still need assembly.
export
0 phaseReleaseHistoryDecoded : {name : Type} -> (nameEq : DecEq name) ->
  (actor : name) -> (events : List (Maybe name, Bool)) ->
  (offset, release : Nat) -> (seen : Bool) ->
  (0 accepted : phaseReleaseCheck nameEq actor offset release seen events = True) ->
  (distance : Nat ** (offset + distance = release, PhaseHistoryPath actor seen distance events))
phaseReleaseHistoryDecoded nameEq actor [] offset release seen accepted = absurd accepted
phaseReleaseHistoryDecoded nameEq actor ((owner, flag) :: rest) offset release seen accepted =
  phaseHistoryAtNativePosition nameEq actor offset release seen owner flag rest
    (\nextSeen, tailAccepted => phaseReleaseHistoryDecoded nameEq actor rest (S offset) release nextSeen tailAccepted)
    (offset == release) Refl accepted
