module DGamma.CP5O19OriginalBlockClassSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5ImmutableBirthMetadataSpike
import DGamma.CP5O19ReplayObservationSpike
import DGamma.CP5ConfluenceRankObservationSpike
import DGamma.CP5O19PairObservationSpike
import Data.List
import Data.List.Elem
import Decidable.Equality

%default total
%unbound_implicits off

||| Producer-owned ORIGINAL block-word values and child exclusion. Lifecycle
||| ownership is not silently cast to PaperActivationStep: recovery/tag
||| exclusion still needs the actual final-active/no-unload evolution proof.
public export
data O19BlockWordObservation :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (actor, forbidden : name) -> Action name key value world error -> Type where
  BlockOwnLifecycle :
    {name, key, world, error : Type} -> {value : key -> Type} -> {actor, forbidden : name} ->
    {action : Action name key value world error} ->
    (0 lifecycle : isLifecycleAction action = True) -> (0 owner : actionOwner action = actor) ->
    O19BlockWordObservation name key world error value actor forbidden action
  BlockGenerated :
    {name, key, world, error : Type} -> {value : key -> Type} -> {actor, forbidden : name} ->
    {action : Action name key value world error} ->
    (child : name) -> (component : Component key value world error) ->
    (0 inserted : action = OInsert child (ChildOf actor) component) ->
    (0 childSafe : Not (child = forbidden)) ->
    O19BlockWordObservation name key world error value actor forbidden action
