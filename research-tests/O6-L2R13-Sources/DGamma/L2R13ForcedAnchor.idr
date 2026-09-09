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
