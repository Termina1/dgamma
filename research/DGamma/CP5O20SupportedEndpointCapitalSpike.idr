module DGamma.CP5O20SupportedEndpointCapitalSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionControlCore
import DGamma.CP4DeletionSelectedForeignControlCore
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5O20SupportedBirthBridgeSpike
import Data.List.Elem
import Decidable.Equality

%default total
%unbound_implicits off

||| ORIGINAL support reaches actual canonical support through this very
||| schedule's block, not an assumed endpoint support-preservation oracle.
export
0 canonicalSupportedTruthFromOriginal :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, finalState : SystemState name key value world error} ->
  (original : Transitions initial finalState) ->
  (capital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq original) ->
  (selected : name) ->
  isSupported @{nameEq} @{keyEq} selected finalState = True ->
  isSupported @{nameEq} @{keyEq} selected (canonicalFinal (canonicalSchedule capital)) = True
canonicalSupportedTruthFromOriginal name key world error value nameEq keyEq protocol original capital selected supported =
  trans (replaySupportMatchesActive (canonicalReplayPremises capital) selected)
    (blockActiveAtFinal (canonicalBlock (canonicalSchedule capital) selected
      (orderComplete (supportLinearization (canonicalSchedule capital)) selected supported)))
