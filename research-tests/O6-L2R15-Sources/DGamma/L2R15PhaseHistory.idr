module DGamma.L2R15PhaseHistory

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
