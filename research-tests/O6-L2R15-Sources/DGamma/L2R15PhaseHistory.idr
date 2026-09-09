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
