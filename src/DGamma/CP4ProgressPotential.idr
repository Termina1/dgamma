module DGamma.CP4ProgressPotential

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP4ProgressBound
import Data.Nat
import Decidable.Equality

%default total

||| Remaining same-target lifecycle budget used to mechanize Theorem 66(A).
||| Constants mirror the proof's stale leave/divert, unload, begin, and possible
||| post-raise unload steps around at most `bound` iterator landings.
public export
fiberProgressPotential : DecEq name => DecEq key => Nat ->
  Fiber name key value world error ->
  Registry name key value world error -> Nat
fiberProgressPotential bound fiber fibers = case fiberLifecycle fiber of
  Inactive (Just err) => Z
  Inactive Nothing => case targetFiber fiber fibers of
    Nothing => Z
    Just target => bound + 2
  Reloading remaining accumulator committedView =>
    if targetMatches (targetFiber fiber fibers) committedView
      then S (length remaining)
      else bound + 4
  Active accumulator committedView =>
    if targetMatches (targetFiber fiber fibers) committedView
      then Z
      else bound + 4
  Unloading accumulator committedView Nothing => bound + 3
  Unloading accumulator committedView (Just err) => 1

public export
actorProgressPotential : DecEq name => DecEq key => Nat -> name ->
  SystemState name key value world error -> Nat
actorProgressPotential bound actor state =
  case lookupFiber actor (registry state) of
    Nothing => Z
    Just fiber => fiberProgressPotential bound fiber (registry state)

0 boolLTEToLTE : (left, right : Nat) -> left <= right = True -> LTE left right
boolLTEToLTE Z right valid = LTEZero
boolLTEToLTE (S left) Z valid = case valid of Refl impossible
boolLTEToLTE (S left) (S right) valid =
  LTESucc (boolLTEToLTE left right valid)

0 lteReflexive : (number : Nat) -> LTE number number
lteReflexive Z = LTEZero
lteReflexive (S number) = LTESucc (lteReflexive number)

0 lteRight : LTE left right -> LTE left (S right)
lteRight LTEZero = LTEZero
lteRight (LTESucc smaller) = LTESucc (lteRight smaller)

0 oneLTEPlusFour : (bound : Nat) -> LTE 1 (bound + 4)
oneLTEPlusFour Z = LTESucc LTEZero
oneLTEPlusFour (S bound) = lteRight (oneLTEPlusFour bound)

0 plusTwoLTEPlusFour : (bound : Nat) -> LTE (bound + 2) (bound + 4)
plusTwoLTEPlusFour Z = LTESucc (LTESucc LTEZero)
plusTwoLTEPlusFour (S bound) = LTESucc (plusTwoLTEPlusFour bound)

0 plusThreeLTEPlusFour : (bound : Nat) -> LTE (bound + 3) (bound + 4)
plusThreeLTEPlusFour Z = LTESucc (LTESucc (LTESucc LTEZero))
plusThreeLTEPlusFour (S bound) = LTESucc (plusThreeLTEPlusFour bound)

0 successorLTEPlusFour : (remaining, bound : Nat) -> LTE remaining bound ->
  LTE (S remaining) (bound + 4)
successorLTEPlusFour Z Z LTEZero = LTESucc LTEZero
successorLTEPlusFour (S remaining) (S bound) (LTESucc smaller) =
  LTESucc (successorLTEPlusFour remaining bound smaller)
successorLTEPlusFour Z (S bound) LTEZero =
  LTESucc LTEZero

||| Every actor's potential is bounded by one Equation-61 interval budget.
public export
0 actorProgressPotentialBounded :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (bound : Nat) ->
  (actor : name) -> (state : SystemState name key value world error) ->
  continuationsBoundedBy bound state = True ->
  LTE (actorProgressPotential @{nameEq} @{keyEq} bound actor state) (bound + 4)
actorProgressPotentialBounded nameEq keyEq bound actor state continuations
  with (lookupFiber @{nameEq} actor (registry state)) proof found
  actorProgressPotentialBounded nameEq keyEq bound actor state continuations |
    Nothing = LTEZero
  actorProgressPotentialBounded nameEq keyEq bound actor state continuations |
    Just (MkFiber component parent retiredFlag table (Inactive (Just err))) =
      LTEZero
  actorProgressPotentialBounded nameEq keyEq bound actor state continuations |
    Just (MkFiber component parent retiredFlag table (Inactive Nothing))
    with (targetFiber @{nameEq} @{keyEq}
      (MkFiber component parent retiredFlag table (Inactive Nothing))
      (registry state))
    actorProgressPotentialBounded nameEq keyEq bound actor state continuations |
      Just (MkFiber component parent retiredFlag table (Inactive Nothing)) |
      Nothing = LTEZero
    actorProgressPotentialBounded nameEq keyEq bound actor state continuations |
      Just (MkFiber component parent retiredFlag table (Inactive Nothing)) |
      Just target = plusTwoLTEPlusFour bound
  actorProgressPotentialBounded nameEq keyEq bound actor state continuations |
    Just fiber@(MkFiber component parent retiredFlag table
      (Reloading remaining accumulator committedView))
    with (targetMatches @{nameEq}
      (targetFiber @{nameEq} @{keyEq} fiber (registry state)) committedView)
    actorProgressPotentialBounded nameEq keyEq bound actor state continuations |
      Just fiber@(MkFiber component parent retiredFlag table
        (Reloading remaining accumulator committedView)) | True =
        let bounded = continuationBoundedAtLookup nameEq bound state
              continuations actor
              (MkFiber component parent retiredFlag table
                (Reloading remaining accumulator committedView)) found
            0 remainingBoolean : (length remaining <= bound = True)
            remainingBoolean = bounded
        in successorLTEPlusFour (length remaining) bound
          (boolLTEToLTE (length remaining) bound remainingBoolean)
    actorProgressPotentialBounded nameEq keyEq bound actor state continuations |
      Just fiber@(MkFiber component parent retiredFlag table
        (Reloading remaining accumulator committedView)) | False =
        lteReflexive (bound + 4)
  actorProgressPotentialBounded nameEq keyEq bound actor state continuations |
    Just fiber@(MkFiber component parent retiredFlag table
      (Active accumulator committedView))
    with (targetMatches @{nameEq}
      (targetFiber @{nameEq} @{keyEq} fiber (registry state)) committedView)
    actorProgressPotentialBounded nameEq keyEq bound actor state continuations |
      Just fiber@(MkFiber component parent retiredFlag table
        (Active accumulator committedView)) | True = LTEZero
    actorProgressPotentialBounded nameEq keyEq bound actor state continuations |
      Just fiber@(MkFiber component parent retiredFlag table
        (Active accumulator committedView)) | False =
        lteReflexive (bound + 4)
  actorProgressPotentialBounded nameEq keyEq bound actor state continuations |
    Just (MkFiber component parent retiredFlag table
      (Unloading accumulator committedView Nothing)) =
        plusThreeLTEPlusFour bound
  actorProgressPotentialBounded nameEq keyEq bound actor state continuations |
    Just (MkFiber component parent retiredFlag table
      (Unloading accumulator committedView (Just err))) =
        oneLTEPlusFour bound
