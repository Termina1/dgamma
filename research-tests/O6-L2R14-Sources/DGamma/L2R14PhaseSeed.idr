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
import DGamma.L2R7Classifier
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

||| Observe the physical release event before extracting its actor. Native
||| head/drop equality is supplied at the actual call site, never re-cased.
export
0 phaseActorAtEvent : {name : Type} -> (nameEq : DecEq name) ->
  (events : List (Maybe name, Bool)) -> (ordinal : Nat) ->
  (event : Maybe (Maybe name, Bool)) ->
  (0 equation : head' (drop ordinal events) = event) ->
  (0 accepted : maybe False (\item => maybe False
    (\actor => phaseReleaseCheck nameEq actor 0 ordinal False events) (fst item)) event = True) ->
  (actor : name ** (flag : Bool **
    (head' (drop ordinal events) = Just (Just actor, flag),
     phaseReleaseCheck nameEq actor 0 ordinal False events = True)))
phaseActorAtEvent nameEq events ordinal Nothing equation accepted = absurd accepted
phaseActorAtEvent nameEq events ordinal (Just (owner, flag)) equation accepted =
  (fst (phaseActorAtOwner nameEq events ordinal owner accepted) **
   (flag ** (trans equation (cong (\selected => Just (selected, flag))
      (fst (snd (phaseActorAtOwner nameEq events ordinal owner accepted)))),
    snd (snd (phaseActorAtOwner nameEq events ordinal owner accepted)))))

||| Split the authentic seed predicate, preserving all FOUR native tests.
||| No release identity or interval is inferred merely from scan acceptance.
export
0 phaseSeedAcceptedParts : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  {trace : Transitions first finalState} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (trail : DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace name key world error value trace) ->
  (entry, seed : RootCatalogEntry name key world error value) -> (anchor : Nat) ->
  (0 accepted : phaseAnchorSeedCheck nameEq keyEq trail entry anchor seed = True) ->
  (LTE (catalogOrdinal seed) (catalogOrdinal entry),
   keyForcedOrdinal nameEq keyEq trail (catalogOrdinal seed) = True,
   elemDec (pred anchor) (filter (\ordinal => ordinal < catalogOrdinal seed) (releaseOrdinalScan nameEq keyEq (catalogComponent seed) trail)) = True,
   maybe False (\item => maybe False (\actor => phaseReleaseCheck nameEq actor 0 (pred anchor) False (phaseEvents nameEq trail)) (fst item)) (head' (drop (pred anchor) (phaseEvents nameEq trail))) = True)
phaseSeedAcceptedParts nameEq keyEq trail entry seed anchor accepted =
  (lteReflectsLTE (catalogOrdinal seed) (catalogOrdinal entry)
    (trans (sym (leToLte (catalogOrdinal seed) (catalogOrdinal entry)))
      (boolAndLeft (catalogOrdinal seed <= catalogOrdinal entry) (keyForcedOrdinal nameEq keyEq trail (catalogOrdinal seed) && elemDec (pred anchor) (filter (\ordinal => ordinal < catalogOrdinal seed) (releaseOrdinalScan nameEq keyEq (catalogComponent seed) trail)) && maybe False (\item => maybe False (\actor => phaseReleaseCheck nameEq actor 0 (pred anchor) False (phaseEvents nameEq trail)) (fst item)) (head' (drop (pred anchor) (phaseEvents nameEq trail)))) (accepted))),
   boolAndLeft (keyForcedOrdinal nameEq keyEq trail (catalogOrdinal seed)) (elemDec (pred anchor) (filter (\ordinal => ordinal < catalogOrdinal seed) (releaseOrdinalScan nameEq keyEq (catalogComponent seed) trail)) && maybe False (\item => maybe False (\actor => phaseReleaseCheck nameEq actor 0 (pred anchor) False (phaseEvents nameEq trail)) (fst item)) (head' (drop (pred anchor) (phaseEvents nameEq trail)))) (boolAndRight (catalogOrdinal seed <= catalogOrdinal entry) (keyForcedOrdinal nameEq keyEq trail (catalogOrdinal seed) && elemDec (pred anchor) (filter (\ordinal => ordinal < catalogOrdinal seed) (releaseOrdinalScan nameEq keyEq (catalogComponent seed) trail)) && maybe False (\item => maybe False (\actor => phaseReleaseCheck nameEq actor 0 (pred anchor) False (phaseEvents nameEq trail)) (fst item)) (head' (drop (pred anchor) (phaseEvents nameEq trail)))) (accepted)),
   boolAndLeft (elemDec (pred anchor) (filter (\ordinal => ordinal < catalogOrdinal seed) (releaseOrdinalScan nameEq keyEq (catalogComponent seed) trail))) (maybe False (\item => maybe False (\actor => phaseReleaseCheck nameEq actor 0 (pred anchor) False (phaseEvents nameEq trail)) (fst item)) (head' (drop (pred anchor) (phaseEvents nameEq trail)))) (boolAndRight (keyForcedOrdinal nameEq keyEq trail (catalogOrdinal seed)) (elemDec (pred anchor) (filter (\ordinal => ordinal < catalogOrdinal seed) (releaseOrdinalScan nameEq keyEq (catalogComponent seed) trail)) && maybe False (\item => maybe False (\actor => phaseReleaseCheck nameEq actor 0 (pred anchor) False (phaseEvents nameEq trail)) (fst item)) (head' (drop (pred anchor) (phaseEvents nameEq trail)))) (boolAndRight (catalogOrdinal seed <= catalogOrdinal entry) (keyForcedOrdinal nameEq keyEq trail (catalogOrdinal seed) && elemDec (pred anchor) (filter (\ordinal => ordinal < catalogOrdinal seed) (releaseOrdinalScan nameEq keyEq (catalogComponent seed) trail)) && maybe False (\item => maybe False (\actor => phaseReleaseCheck nameEq actor 0 (pred anchor) False (phaseEvents nameEq trail)) (fst item)) (head' (drop (pred anchor) (phaseEvents nameEq trail)))) (accepted))),
   boolAndRight (elemDec (pred anchor) (filter (\ordinal => ordinal < catalogOrdinal seed) (releaseOrdinalScan nameEq keyEq (catalogComponent seed) trail))) (maybe False (\item => maybe False (\actor => phaseReleaseCheck nameEq actor 0 (pred anchor) False (phaseEvents nameEq trail)) (fst item)) (head' (drop (pred anchor) (phaseEvents nameEq trail)))) (boolAndRight (keyForcedOrdinal nameEq keyEq trail (catalogOrdinal seed)) (elemDec (pred anchor) (filter (\ordinal => ordinal < catalogOrdinal seed) (releaseOrdinalScan nameEq keyEq (catalogComponent seed) trail)) && maybe False (\item => maybe False (\actor => phaseReleaseCheck nameEq actor 0 (pred anchor) False (phaseEvents nameEq trail)) (fst item)) (head' (drop (pred anchor) (phaseEvents nameEq trail)))) (boolAndRight (catalogOrdinal seed <= catalogOrdinal entry) (keyForcedOrdinal nameEq keyEq trail (catalogOrdinal seed) && elemDec (pred anchor) (filter (\ordinal => ordinal < catalogOrdinal seed) (releaseOrdinalScan nameEq keyEq (catalogComponent seed) trail)) && maybe False (\item => maybe False (\actor => phaseReleaseCheck nameEq actor 0 (pred anchor) False (phaseEvents nameEq trail)) (fst item)) (head' (drop (pred anchor) (phaseEvents nameEq trail)))) (accepted))))

||| The actor and phase-history acceptance are PRODUCED from an authentic
||| accepted seed. The event is observed from phaseEvents at pred anchor.
export
0 phaseSeedActor : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  {trace : Transitions first finalState} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (trail : DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace name key world error value trace) ->
  (entry, seed : RootCatalogEntry name key world error value) -> (anchor : Nat) ->
  (0 accepted : phaseAnchorSeedCheck nameEq keyEq trail entry anchor seed = True) ->
  (actor : name ** (flag : Bool **
    (head' (drop (pred anchor) (phaseEvents nameEq trail)) = Just (Just actor, flag),
     phaseReleaseCheck nameEq actor 0 (pred anchor) False (phaseEvents nameEq trail) = True)))
phaseSeedActor nameEq keyEq trail entry seed anchor accepted =
  phaseActorAtEvent nameEq (phaseEvents nameEq trail) (pred anchor)
    (head' (drop (pred anchor) (phaseEvents nameEq trail))) Refl
    (snd (snd (snd (phaseSeedAcceptedParts nameEq keyEq trail entry seed anchor accepted))))
