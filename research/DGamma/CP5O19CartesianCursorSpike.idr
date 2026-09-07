module DGamma.CP5O19CartesianCursorSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5O19AdjacentReplayProducerSpike
import DGamma.CP5O19ReplayObservationSpike
import DGamma.CP5RankedEarlyApplicabilitySpike
import Data.List
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| R183 A1: the current actual trace and its SAME reached evidence are one
||| observed package. This is an iteration boundary, not a Cartesian producer
||| or a claim that a later selected action is applicable.
public export
record O19ReachedCursor
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, sourceFinal : SystemState name key value world error}
  (source : Transitions initial sourceFinal) where
  constructor MkO19ReachedCursor
  cursorFinal : SystemState name key value world error
  cursorTrace : Transitions initial cursorFinal
  0 cursorBundle : ReplayInvariantBundle name key world error value protocol
    nameEq keyEq cursorTrace
  0 cursorUnique : UniqueRawNameInsertions name key world error value
    nameEq keyEq cursorTrace
  0 cursorDerivation : FiniteAdjacentSwapDerivation name key world error value
    protocol nameEq keyEq source cursorTrace

||| R183 A2: initialize from actual source evidence; zero crossings are only
||| the base of a future induction, never a WholeBlockSwapDerivation.
public export
0 o19InitialCursor :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, sourceFinal : SystemState name key value world error} ->
  (source : Transitions initial sourceFinal) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq source ->
  (0 sourceUnique : UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
  O19ReachedCursor name key world error value protocol nameEq keyEq source
o19InitialCursor {sourceFinal} nameEq keyEq protocol source premises sourceUnique =
  MkO19ReachedCursor sourceFinal source premises sourceUnique FiniteAdjacentSwapDone
