module DGamma.CP5O20DiscardedBirthOriginSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5O20DiscardedSelectionCoverageSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| A discarded stamp was either in the incoming scanner index or was born
||| at an exact occurrence of THIS suffix whose actual parent later Unloads.
||| The flat family carries no selection, canonical absence or coverage oracle.
public export
data O20DiscardedTraceOrigin :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {first, finalState : SystemState name key value world error} ->
  (ordinal : Nat) -> (incoming : List (RegistrationGeneration name)) ->
  (generation : RegistrationGeneration name) -> Transitions first finalState -> Type where
  O20DiscardedBefore :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {first, finalState : SystemState name key value world error} ->
    {ordinal : Nat} -> {incoming : List (RegistrationGeneration name)} ->
    {generation : RegistrationGeneration name} -> {trace : Transitions first finalState} ->
    (0 member : Elem generation incoming) ->
    O20DiscardedTraceOrigin name key world error value ordinal incoming generation trace
  O20DiscardedWithin :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {first, finalState : SystemState name key value world error} ->
    {ordinal : Nat} -> {incoming : List (RegistrationGeneration name)} ->
    {generation : RegistrationGeneration name} -> {trace : Transitions first finalState} ->
    (0 child, parent : name) -> (0 component : Component key value world error) ->
    (0 birth : LocatedGeneratedRegistration child parent component trace) ->
    (0 exact : (generation = MkRegistrationGeneration child (ordinal + registrationOrdinal birth))) ->
    (0 closing : ActionOccurs (LUnload parent) (afterRegistration birth)) ->
    O20DiscardedTraceOrigin name key world error value ordinal incoming generation trace
