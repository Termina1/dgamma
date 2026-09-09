module DGamma.CP5O20BlockEndRemainderSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionBoundaryDeleted
import DGamma.CP4DeletionSelectedForeignOrchestration
import DGamma.CP5O20ProgramRoleWordSpike
import DGamma.CP5O20PairedRemovalSpike
import DGamma.CP5O19AdjacentReplayProducerSpike
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCanonicalSortSpike
import DGamma.CP5O20CanonicalBlockWordAgreementSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| The same explicitly observed primitive lookup gives equal native Active
||| bits at two states. No projected guard is reconstructed from a record.
export
0 o20ActiveLookupFrame :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (observed : Maybe (Fiber name key value world error)) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry before) = observed) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry afterState) = observed) ->
  (supportedActiveAt {name} {key} {value} {world} {error} @{nameEq} selected before =
   supportedActiveAt {name} {key} {value} {world} {error} @{nameEq} selected afterState)
o20ActiveLookupFrame nameEq selected before afterState Nothing leftExact rightExact =
  rewrite leftExact in rewrite rightExact in Refl
o20ActiveLookupFrame nameEq selected before afterState (Just fiber) leftExact rightExact =
  rewrite leftExact in rewrite rightExact in Refl
