module DGamma.L2R10UniqueMoveDomain

import Prelude.Types
import DGamma.Calculus
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.CP5UniqueRawNameInsertions
import DGamma.L2R6IterationObligations
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Owner-ratified R173 uniqueness premise for the move producer. This NEW
||| stronger-premise TYPE supersedes the unqualified L2R6 obligation for name
||| reuse; the old declaration remains byte-unchanged. TYPE ONLY, not an
||| existence producer. Initial installed names additionally need whole-trace
||| birth provenance/from-empty scope; trace insertion uniqueness alone does
||| not assert anything about names omitted from a nonempty initial prefix.
public export
GeneralAdmittedMoveExistenceUnique :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {initial, finalState : SystemState name key value world error} ->
  {trace : Transitions initial finalState} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  AvailabilityTrace name key world error value trace -> Type
GeneralAdmittedMoveExistenceUnique {name} {key} {world} {error} {value} {trace}
  nameEq keyEq trail =
  (0 unique : UniqueRawNameInsertions name key world error value nameEq keyEq trace) ->
  GeneralAdmittedMoveExistence nameEq keyEq trail
