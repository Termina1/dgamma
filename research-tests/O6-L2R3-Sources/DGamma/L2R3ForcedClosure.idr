module DGamma.L2R3ForcedClosure

import Data.Nat

%default total
%unbound_implicits off

||| Least inductive set of ROOT INPUT OCCURRENCES, indexed by their physical
||| ordinal in the original trace (root-input order is its restricted order).
||| Parameters must classify actual roots and actual key-release dependencies.
||| No arbitrary ordinal is admitted: seeds and barriers both require rootInput.
||| All and only finite key-seeded, strictly later-root derivations are allowed.
public export
data ForcedRootInput : (rootInput, keyForced : Nat -> Type) -> Nat -> Type where
  KeyForces : {rootInput, keyForced : Nat -> Type} -> {ordinal : Nat} ->
    (0 root : rootInput ordinal) -> (0 released : keyForced ordinal) ->
    ForcedRootInput rootInput keyForced ordinal
  OrderForces : {rootInput, keyForced : Nat -> Type} -> {earlier, later : Nat} ->
    (0 prior : ForcedRootInput rootInput keyForced earlier) ->
    (0 root : rootInput later) -> (0 ordered : LT earlier later) ->
    ForcedRootInput rootInput keyForced later
