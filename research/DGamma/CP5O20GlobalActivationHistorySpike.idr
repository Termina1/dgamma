module DGamma.CP5O20GlobalActivationHistorySpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5O20ActivationPositionStepSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Every ordinary native index advance preserves ALL activation counters.
||| Begin changes the live activation key but not accumulated position counts;
||| Unload/Remove likewise retain counts indexed by their HISTORICAL keys.
export
0 o20OrdinaryIndexKeepsActivationCounts :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (ordinal : Nat) ->
  (action : Action name key value world error) -> (index : RegistrationIndexState name) ->
  (indexedSurvivingChildCounts (advanceRegistrationIndex @{nameEq} ordinal action index) =
    indexedSurvivingChildCounts index)
o20OrdinaryIndexKeepsActivationCounts nameEq ordinal (OInsert actor Root component)
  (MkRegistrationIndexState live activations counts deleted) = Refl
o20OrdinaryIndexKeepsActivationCounts nameEq ordinal (OInsert actor (ChildOf parent) component)
  (MkRegistrationIndexState live activations counts deleted) = Refl
o20OrdinaryIndexKeepsActivationCounts nameEq ordinal (ORetire actor)
  (MkRegistrationIndexState live activations counts deleted) = Refl
o20OrdinaryIndexKeepsActivationCounts nameEq ordinal (ORemove actor)
  (MkRegistrationIndexState live activations counts deleted) = Refl
o20OrdinaryIndexKeepsActivationCounts nameEq ordinal (LBegin actor)
  (MkRegistrationIndexState live activations counts deleted) =
    case the (found : Maybe (RegistrationGeneration name) **
      (lookupCurrentGeneration @{nameEq} actor live = found))
      (lookupCurrentGeneration @{nameEq} actor live ** Refl) of
      (Nothing ** exact) => rewrite exact in Refl
      (Just generation ** exact) => rewrite exact in Refl
o20OrdinaryIndexKeepsActivationCounts nameEq ordinal (LAdvance actor)
  (MkRegistrationIndexState live activations counts deleted) = Refl
o20OrdinaryIndexKeepsActivationCounts nameEq ordinal (LDivert actor)
  (MkRegistrationIndexState live activations counts deleted) = Refl
o20OrdinaryIndexKeepsActivationCounts nameEq ordinal (LLeave actor)
  (MkRegistrationIndexState live activations counts deleted) = Refl
o20OrdinaryIndexKeepsActivationCounts nameEq ordinal (LUnload actor)
  (MkRegistrationIndexState live activations counts deleted) = Refl
