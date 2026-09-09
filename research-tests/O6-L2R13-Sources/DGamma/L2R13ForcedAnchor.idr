module DGamma.L2R13ForcedAnchor

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
import DGamma.L2R7Classifier
import DGamma.L2R7ObservedAny
import DGamma.L2R7PlacedCoverage
import DGamma.L2R12PhaseAccepted
import Data.Bool
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Zero branch of reflection for the actual library Nat equality.
export
0 phaseNatZero : (right : Nat) -> (0 accepted : (Z == right) = True) -> Z = right
phaseNatZero Z accepted = Refl
phaseNatZero (S right) accepted = absurd accepted

||| Successor reflection consumes only the right Nat and recursive premise.
export
0 phaseNatSuccessor : (left : Nat) ->
  (0 recursive : (right : Nat) -> (left == right) = True -> left = right) ->
  (right : Nat) -> (0 accepted : (S left == right) = True) -> S left = right
phaseNatSuccessor left recursive Z accepted = absurd accepted
phaseNatSuccessor left recursive (S right) accepted = cong S (recursive right accepted)

||| Reflect the exact Nat equality used inside keyForcedOrdinal.
export
0 phaseNatEqual : (left, right : Nat) -> (0 accepted : (left == right) = True) -> left = right
phaseNatEqual Z right accepted = phaseNatZero right accepted
phaseNatEqual (S left) right accepted = phaseNatSuccessor left (\other, equal => phaseNatEqual left other equal) right accepted

||| Native append preserves the disjunction of nonempty observations.
export
0 phaseAppendNonempty : {a : Type} -> (left, right : List a) ->
  not (null (left ++ right)) = (not (null left) || not (null right))
phaseAppendNonempty [] right = Refl
phaseAppendNonempty (head :: left) right = Refl

||| Reflect the library concatMap LEFT fold through nonempty observation.
||| The accumulator remains explicit; append observation is transported.
export
0 phaseFlattenNonempty : {a, b : Type} -> (scan : a -> List b) ->
  (items : List a) -> (accumulator : List b) ->
  not (null (foldl (\acc, item => acc ++ scan item) accumulator items)) =
    foldl (\seen, item => seen || not (null (scan item))) (not (null accumulator)) items
phaseFlattenNonempty scan [] accumulator = Refl
phaseFlattenNonempty scan (head :: rest) accumulator =
  trans (phaseFlattenNonempty scan rest (accumulator ++ scan head))
    (cong (\seen => foldl (\acc, item => acc || not (null (scan item))) seen rest)
      (phaseAppendNonempty accumulator (scan head)))

||| A selected genuine nonempty release scan makes the native flatten nonempty.
export
0 phaseConcatNonempty : {a, b : Type} -> (scan : a -> List b) ->
  (item : a) -> (items : List a) -> (0 member : Elem item items) ->
  (0 present : not (null (scan item)) = True) ->
  not (null (concatMap scan items)) = True
phaseConcatNonempty scan item items member present =
  trans (phaseFlattenNonempty scan items [])
    (anyMappedMember id (\selected => not (null (scan selected))) items item
      (elemMap id member) present)

||| Decode the INNER keyForcedOrdinal hit into a member of the anchor's
||| bounded catalog. Native ordinal equality transports its cutoff bound.
export
0 phaseKeyHitNonempty : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  {trace : Transitions first finalState} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (trail : AvailabilityTrace name key world error value trace) -> (ordinal, cut : Nat) ->
  (0 bounded : (ordinal <= cut) = True) ->
  (hit : AnyHit (\seed => catalogOrdinal seed == ordinal &&
    not (null (scanReleaseOrdinals nameEq keyEq (catalogComponent seed) 0 (catalogOrdinal seed) trail)))
    (scanRootCatalog 0 trail)) ->
  not (null (concatMap
    (\seed => scanReleaseOrdinals nameEq keyEq (catalogComponent seed) 0 (catalogOrdinal seed) trail)
    (filter (\seed => catalogOrdinal seed <= cut) (scanRootCatalog 0 trail)))) = True
phaseKeyHitNonempty nameEq keyEq trail ordinal cut bounded hit =
  phaseConcatNonempty
    (\seed => scanReleaseOrdinals nameEq keyEq (catalogComponent seed) 0 (catalogOrdinal seed) trail)
    (hitItem hit) (filter (\seed => catalogOrdinal seed <= cut) (scanRootCatalog 0 trail))
    (filterMemberObserved (\seed => catalogOrdinal seed <= cut) (hitItem hit) (hitMember hit) True
      (trans (cong (\position => position <= cut)
        (phaseNatEqual (catalogOrdinal (hitItem hit)) ordinal
          (boolAndLeft (catalogOrdinal (hitItem hit) == ordinal)
            (not (null (scanReleaseOrdinals nameEq keyEq (catalogComponent (hitItem hit)) 0 (catalogOrdinal (hitItem hit)) trail)))
            (hitAccepted hit)))) bounded) Refl)
    (boolAndRight (catalogOrdinal (hitItem hit) == ordinal)
      (not (null (scanReleaseOrdinals nameEq keyEq (catalogComponent (hitItem hit)) 0 (catalogOrdinal (hitItem hit)) trail)))
      (hitAccepted hit))

||| Decode the OUTER classifier hit and observe its inner library any call.
||| Flattened releases therefore cannot be empty even for an unseeded barrier.
export
0 phaseForcedHitNonempty : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  {trace : Transitions first finalState} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (trail : AvailabilityTrace name key world error value trace) -> (cut : Nat) ->
  (hit : AnyHit (\seed => catalogOrdinal seed <= cut &&
    keyForcedOrdinal nameEq keyEq trail (catalogOrdinal seed)) (scanRootCatalog 0 trail)) ->
  not (null (concatMap
    (\seed => scanReleaseOrdinals nameEq keyEq (catalogComponent seed) 0 (catalogOrdinal seed) trail)
    (filter (\seed => catalogOrdinal seed <= cut) (scanRootCatalog 0 trail)))) = True
phaseForcedHitNonempty nameEq keyEq trail cut hit =
  phaseKeyHitNonempty nameEq keyEq trail (catalogOrdinal (hitItem hit)) cut
    (boolAndLeft (catalogOrdinal (hitItem hit) <= cut)
      (keyForcedOrdinal nameEq keyEq trail (catalogOrdinal (hitItem hit))) (hitAccepted hit))
    (anyHitObserved (\seed => catalogOrdinal seed == catalogOrdinal (hitItem hit) &&
      not (null (scanReleaseOrdinals nameEq keyEq (catalogComponent seed) 0 (catalogOrdinal seed) trail)))
      (scanRootCatalog 0 trail) (keyForcedOrdinal nameEq keyEq trail (catalogOrdinal (hitItem hit))) Refl
      (boolAndRight (catalogOrdinal (hitItem hit) <= cut)
        (keyForcedOrdinal nameEq keyEq trail (catalogOrdinal (hitItem hit))) (hitAccepted hit)))

||| Observed-value maximum decoder: a native nonempty scan produces Just.
||| The maximum ordinal is computed, never given as a successful result.
public export
phaseNonemptyAnchor : (items : List Nat) -> (seen : Bool) ->
  (0 equation : not (null items) = seen) -> (0 accepted : seen = True) ->
  (anchor : Nat ** lastReleaseCut items = Just anchor)
phaseNonemptyAnchor [] seen equation accepted = absurd (trans equation accepted)
phaseNonemptyAnchor (head :: rest) seen equation accepted = (S (foldl max head rest) ** Refl)

||| GENERAL forcing-to-Just: this is the unchanged classifyForced per-entry
||| test. No phase, seed, anchor, nonempty release list or success is supplied.
export
0 forcedAnchorJust : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  {trace : Transitions first finalState} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (trail : AvailabilityTrace name key world error value trace) -> (cut : Nat) ->
  (seen : Bool) -> (0 equation : any (\seed => catalogOrdinal seed <= cut &&
    keyForcedOrdinal nameEq keyEq trail (catalogOrdinal seed)) (scanRootCatalog 0 trail) = seen) ->
  (0 forced : seen = True) -> (anchor : Nat ** anchorOf nameEq keyEq trail cut = Just anchor)
forcedAnchorJust nameEq keyEq trail cut seen equation forced =
  phaseNonemptyAnchor
    (concatMap (\seed => scanReleaseOrdinals nameEq keyEq (catalogComponent seed) 0 (catalogOrdinal seed) trail)
      (filter (\seed => catalogOrdinal seed <= cut) (scanRootCatalog 0 trail)))
    (not (null (concatMap (\seed => scanReleaseOrdinals nameEq keyEq (catalogComponent seed) 0 (catalogOrdinal seed) trail)
      (filter (\seed => catalogOrdinal seed <= cut) (scanRootCatalog 0 trail))))) Refl
    (phaseForcedHitNonempty nameEq keyEq trail cut
      (anyHitObserved (\seed => catalogOrdinal seed <= cut &&
        keyForcedOrdinal nameEq keyEq trail (catalogOrdinal seed)) (scanRootCatalog 0 trail) seen equation forced))
