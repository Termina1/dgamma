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

||| Specialize a raw action only along its explicit Unload equation; the
||| registered exclusion remains generation-scoped at the same native cut.
export
0 o20RegisteredActionNotUnload :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (action : Action name key value world error) ->
  (before, afterState : SystemState name key value world error) -> (tag : RuleTag) ->
  (applyAction @{nameEq} @{keyEq} action before = Just (tag, afterState)) ->
  CurrentRegisteredInactiveFibers name key world error value nameEq registered live before ->
  (actor : name) -> (action = LUnload actor) ->
  GenerationOwnedActor nameEq registered ordinal live action -> Void
o20RegisteredActionNotUnload name key world error value nameEq keyEq registered ordinal live
  _ before afterState tag raw inactive actor Refl owned =
    o20RegisteredUnloadImpossible name key world error value nameEq keyEq registered ordinal live
      actor before afterState tag raw inactive owned

||| One aligned source edge produces Unload exclusion and advances both
||| unique generation state and the native registered-Inactive invariant.
export
0 o20RegisteredUnloadFreeHead :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  GenerationEnvironmentNamesUnique live ->
  {first, middle, finalState : SystemState name key value world error} ->
  (step : Transition first middle) -> (rest : Transitions middle finalState) ->
  (IsBeginAction (transitionAction step) ->
    GenerationOwnedActor nameEq registered ordinal live (transitionAction step) -> Void) ->
  CurrentRegisteredInactiveFibers name key world error value nameEq registered live first ->
  (AlignedTransitions name key world error value nameEq keyEq rest ->
    GenerationEnvironmentNamesUnique
      (advanceGenerationEnvironment @{nameEq} ordinal (transitionAction step) live) ->
    CurrentRegisteredInactiveFibers name key world error value nameEq registered
      (advanceGenerationEnvironment @{nameEq} ordinal (transitionAction step) live) middle ->
    O20RegisteredUnloadFree name key world error value nameEq registered (S ordinal)
      (advanceGenerationEnvironment @{nameEq} ordinal (transitionAction step) live) rest) ->
  AlignedTransitions name key world error value nameEq keyEq (MoreTransitions step rest) ->
  O20RegisteredUnloadFree name key world error value nameEq registered ordinal live
    (MoreTransitions step rest)
o20RegisteredUnloadFreeHead name key world error value nameEq keyEq registered ordinal live unique
  {first} {middle} _ _ noBegin inactive continue (AlignedStep action tag checked rest alignedRest) =
    O20RegisteredUnloadStep (Fired nameEq keyEq action tag checked) rest
      (o20RegisteredActionNotUnload name key world error value nameEq keyEq registered ordinal live
        action first middle tag (checkedActionProjects nameEq keyEq action first middle tag checked) inactive)
      (continue alignedRest
        (advanceGenerationEnvironmentPreservesUnique nameEq ordinal action live unique)
        (currentRegisteredInactiveStep nameEq keyEq registered ordinal live unique action first middle tag
          (checkedActionProjects nameEq keyEq action first middle tag checked) noBegin inactive))
