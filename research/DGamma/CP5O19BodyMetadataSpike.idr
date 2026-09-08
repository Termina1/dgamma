module DGamma.CP5O19BodyMetadataSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ImmutableBirthMetadataSpike
import DGamma.CP5UniqueRawNameInsertions
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Original insertion uniqueness identifies the immutable metadata at any
||| TWO actual cuts of the SAME source. Both birth locations are derived by
||| the existing checked-update induction, not supplied as metadata oracles.
export
0 o19SourceCutMetadata :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, first, second, finalState : SystemState name key value world error} ->
  (source : Transitions initial finalState) ->
  (firstEarlier : Transitions initial first) -> (firstLater : Transitions first finalState) ->
  (appendTransitions firstEarlier firstLater = source) ->
  (secondEarlier : Transitions initial second) -> (secondLater : Transitions second finalState) ->
  (appendTransitions secondEarlier secondLater = source) ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq source ->
  UniqueRawNameInsertions name key world error value nameEq keyEq source ->
  (actor : name) -> (firstFiber, secondFiber : Fiber name key value world error) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry first) = Just firstFiber) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry second) = Just secondFiber) ->
  ((fiberParent firstFiber, fiberComponent firstFiber) = (fiberParent secondFiber, fiberComponent secondFiber))
o19SourceCutMetadata {name} {key} {world} {error} {value} nameEq keyEq protocol source
  firstEarlier firstLater firstExact secondEarlier secondLater secondExact premises unique actor firstFiber secondFiber firstFound secondFound =
    uniqueRawBirthMetadata name key world error value nameEq keyEq source unique actor
      (fiberParent firstFiber) (fiberParent secondFiber) (fiberComponent firstFiber) (fiberComponent secondFiber)
      (rawMetadataBirthAtPrefix name key world error value nameEq keyEq source firstEarlier firstLater firstExact
        (fst (alignedAppendSplit firstEarlier firstLater
          (replace {p = AlignedTransitions name key world error value nameEq keyEq} (sym firstExact) (replayAligned premises))))
        (replayInitialEmpty premises) actor firstFiber firstFound)
      (rawMetadataBirthAtPrefix name key world error value nameEq keyEq source secondEarlier secondLater secondExact
        (fst (alignedAppendSplit secondEarlier secondLater
          (replace {p = AlignedTransitions name key world error value nameEq keyEq} (sym secondExact) (replayAligned premises))))
        (replayInitialEmpty premises) actor secondFiber secondFound)
