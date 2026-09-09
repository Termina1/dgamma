module DGamma.CP5O20DeletionRetainedUnloadSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionInactiveInvariant
import DGamma.CP4DeletionGenerationUnique
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| A checked native Unload cannot belong to a registered generation known
||| Inactive at that exact scanner boundary. No raw-name-global exclusion is used.
export
0 o20RegisteredUnloadImpossible :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (actor : name) -> (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (applyAction @{nameEq} @{keyEq} (LUnload actor) before = Just (tag, afterState)) ->
  CurrentRegisteredInactiveFibers name key world error value nameEq registered live before ->
  GenerationOwnedActor nameEq registered ordinal live (the (Action name key value world error) (LUnload actor)) -> Void
o20RegisteredUnloadImpossible name key world error value nameEq keyEq registered ordinal live
  actor before afterState tag raw inactive owned =
    inactiveCannotUnload nameEq keyEq actor before afterState tag raw
      (inactive actor (fst owned) (snd (snd owned)) (fst (snd owned)))
