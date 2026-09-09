module DGamma.CP5O20CurrentNameRebaseSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionSelectedForeignControlCore
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5CurrentGenerationBirthSpike
import DGamma.CP5O20SupportedEndpointCapitalSpike
import DGamma.CP5O20HistoryNameTransportSpike
import DGamma.CP5O20ChainCurrentDisappearanceSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Retained-present class: ANY actual canonical fiber, including unsupported
||| present fibers, has a real original fiber and full same-name controls.
||| Actual presence excludes the endpoint's withdrawn-name branch; there is
||| no support restriction, supplied original presence or tail control premise.
export
0 o20CanonicalPresentOriginalControl :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, finalState : SystemState name key value world error} ->
  (original : Transitions initial finalState) ->
  (capital : IndependentCanonicalSchedule name key world error value protocol nameEq keyEq original) ->
  (selected : name) -> (fiber : Fiber name key value world error) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected
    (registry (canonicalFinal (canonicalSchedule capital))) = Just fiber) ->
  ForeignRelatedFiberFound name key world error value nameEq selected
    (registry (canonicalFinal (canonicalSchedule capital))) (registry finalState) fiber
o20CanonicalPresentOriginalControl name key world error value nameEq keyEq protocol {finalState}
  original capital selected fiber present =
    foreignControlLookupFound nameEq selected (registry (canonicalFinal (canonicalSchedule capital)))
      (registry finalState) fiber present
      (fiberControlMaybeSymmetric (endpointControlsOutside (canonicalEndpoint (canonicalSchedule capital)) selected
        (canonicalPresentOutsideWithdrawals name key world error value nameEq keyEq finalState
          (canonicalFinal (canonicalSchedule capital)) (canonicalEndpoint (canonicalSchedule capital)) selected fiber present)))
