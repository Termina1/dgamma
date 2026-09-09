module DGamma.L2R14PhaseSeed

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import Prelude.EqOrd
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R5RootCatalog
import DGamma.L2R6ForcedScan
import DGamma.L2R6Anchors
import DGamma.L2R7ObservedAny
import DGamma.L2R9OrdinalScan
import DGamma.L2R10PhaseScan
import DGamma.L2R12PhaseAccepted
import DGamma.L2R13PhaseEntry
import Data.Bool
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Extract the accepted actor from an OBSERVED event owner. This produces
||| the phase-check premise; it does not assume a physical core interval.
export
0 phaseActorAtOwner : {name : Type} -> (nameEq : DecEq name) ->
  (events : List (Maybe name, Bool)) -> (ordinal : Nat) ->
  (owner : Maybe name) ->
  (0 accepted : maybe False (\actor => phaseReleaseCheck nameEq actor 0 ordinal False events) owner = True) ->
  (actor : name ** (owner = Just actor,
    phaseReleaseCheck nameEq actor 0 ordinal False events = True))
phaseActorAtOwner nameEq events ordinal Nothing accepted = absurd accepted
phaseActorAtOwner nameEq events ordinal (Just actor) accepted = (actor ** (Refl, accepted))
