module DGamma.CP5O20BlockResolverFrameSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionSelectedForeignLifecycleAnchorTrace
import DGamma.CP5O19ActivationResolutionSpike
import DGamma.CP5O19InsertObservationSpike
import DGamma.CP5O19PairObservationSpike
import DGamma.CP5O20RightOpeningTransportSpike
import DGamma.CP5O20SelectorResolverFrameSpike
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Installed evidence yields physical presence by one explicit primitive
||| lookup observation. No existential fiber producer is eliminated.
export
0 o20InstalledLookupPresentObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (actor : name) ->
  (state : SystemState name key value world error) ->
  (installedAt {name} {key} {value} {world} {error} @{nameEq} actor state = True) ->
  (observed : Maybe (Fiber name key value world error)) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry state) = observed) ->
  (isJust (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry state)) = True)
o20InstalledLookupPresentObserved {name} {key} {world} {error} {value} nameEq actor state installed Nothing found =
  absurd (trans (sym (the (installedAt {name} {key} {value} {world} {error} @{nameEq} actor state = False)
    (rewrite found in Refl))) installed)
o20InstalledLookupPresentObserved nameEq actor state installed (Just fiber) found = rewrite found in Refl
