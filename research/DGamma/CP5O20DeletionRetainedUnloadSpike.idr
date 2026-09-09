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

||| Every native source step excludes an Unload owned by an exact registered
||| generation, using the continuously advanced ORIGINAL scanner environment.
public export
data O20RegisteredUnloadFree :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  {first, finalState : SystemState name key value world error} ->
  Transitions first finalState -> Type where
  O20RegisteredUnloadEnd :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {registered : List (RegistrationGeneration name)} ->
    {ordinal : Nat} -> {live : GenerationEnvironment name} ->
    {state : SystemState name key value world error} ->
    O20RegisteredUnloadFree name key world error value nameEq registered ordinal live
      (the (Transitions state state) NoTransitions)
  O20RegisteredUnloadStep :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {registered : List (RegistrationGeneration name)} ->
    {ordinal : Nat} -> {live : GenerationEnvironment name} ->
    {first, middle, finalState : SystemState name key value world error} ->
    (step : Transition first middle) -> (rest : Transitions middle finalState) ->
    (0 excludes : (actor : name) -> (transitionAction step = LUnload actor) ->
      GenerationOwnedActor nameEq registered ordinal live (transitionAction step) -> Void) ->
    (0 tail : O20RegisteredUnloadFree name key world error value nameEq registered (S ordinal)
      (advanceGenerationEnvironment @{nameEq} ordinal (transitionAction step) live) rest) ->
    O20RegisteredUnloadFree name key world error value nameEq registered ordinal live
      (MoreTransitions step rest)
