module DGamma.L2R11PhaseDecode

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.CP5ActorLifecycleOnlyExtended
import DGamma.L2R8CoreContract
import DGamma.L2R10PhaseScan
import Data.List
import Data.List.Elem
import Data.List.Quantifiers
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Decode the ACTUAL event-owner classifier into its native child parent.
||| Only the parent is eliminated; Just injectivity preserves owner identity.
export
0 phaseParentDecoded : {name : Type} -> (parent : Parent name) -> (actor : name) ->
  (0 equation : phaseParentOwner parent = Just actor) -> parent = ChildOf actor
phaseParentDecoded Root actor equation = absurd equation
phaseParentDecoded (ChildOf owner) actor equation = cong ChildOf (injective equation)

||| Decode a control event's observed lookup into the SAME installed fiber
||| and own-child parent. The continuation receives data, not a semantic oracle.
export
0 phaseControlDecoded : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (child, actor : name) ->
  (source : SystemState name key value world error) ->
  (found : Maybe (Fiber name key value world error)) ->
  (0 equation : lookupFiber {name} {key} {value} {world} {error} @{nameEq}
    child (registry source) = found) ->
  (0 owner : phaseControlOwner nameEq child source found equation = Just actor) ->
  (0 result : Type) ->
  (0 done : (fiber : Fiber name key value world error) ->
    (0 nativeFound : lookupFiber {name} {key} {value} {world} {error} @{nameEq}
      child (registry source) = Just fiber) ->
    (0 nativeParent : fiberParent fiber = ChildOf actor) -> result) -> result
phaseControlDecoded nameEq child actor source Nothing equation owner result done = absurd owner
phaseControlDecoded nameEq child actor source (Just fiber) equation owner result done =
  done fiber equation (phaseParentDecoded (fiberParent fiber) actor owner)

||| One exact phase event extends the native actor grammar. The action and
||| source lookup are observed at their own call sites, not reconstructed.
export
0 phaseActionExtended : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, middle, finalState : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (actor : name) ->
  (step : Transition first middle) -> (rest : Transitions middle finalState) ->
  (action : Action name key value world error) ->
  (0 equation : transitionAction step = action) ->
  (0 owner : phaseActionOwner nameEq first action = Just actor) ->
  (0 only : ActorLifecycleOnlyExtended nameEq actor rest) ->
  ActorLifecycleOnlyExtended nameEq actor (MoreTransitions step rest)
phaseActionExtended nameEq actor step rest (OInsert child parent component) equation owner only =
  ExtendedYieldedRegistrationStep step rest
    (trans equation (cong (\nativeParent => OInsert child nativeParent component)
      (phaseParentDecoded parent actor owner))) only
phaseActionExtended {name} {key} {world} {error} {value} {first}
  nameEq actor step rest (ORetire child) equation owner only =
  phaseControlDecoded nameEq child actor first
    (lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry first)) Refl owner
    (ActorLifecycleOnlyExtended nameEq actor (MoreTransitions step rest))
    (\fiber, found, parent => ExtendedChildRetireStep step rest child fiber found parent equation only)
phaseActionExtended {name} {key} {world} {error} {value} {first}
  nameEq actor step rest (ORemove child) equation owner only =
  phaseControlDecoded nameEq child actor first
    (lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry first)) Refl owner
    (ActorLifecycleOnlyExtended nameEq actor (MoreTransitions step rest))
    (\fiber, found, parent => ExtendedChildRemoveStep step rest child fiber found parent equation only)
phaseActionExtended nameEq actor step rest (LBegin selected) equation owner only =
  ExtendedLifecycleStep step rest (rewrite equation in Refl)
    (rewrite equation in injective owner) only
phaseActionExtended nameEq actor step rest (LAdvance selected) equation owner only =
  ExtendedLifecycleStep step rest (rewrite equation in Refl)
    (rewrite equation in injective owner) only
phaseActionExtended nameEq actor step rest (LDivert selected) equation owner only =
  ExtendedLifecycleStep step rest (rewrite equation in Refl)
    (rewrite equation in injective owner) only
phaseActionExtended nameEq actor step rest (LUnload selected) equation owner only =
  ExtendedLifecycleStep step rest (rewrite equation in Refl)
    (rewrite equation in injective owner) only
phaseActionExtended nameEq actor step rest (LLeave selected) equation owner only =
  ExtendedLifecycleStep step rest (rewrite equation in Refl)
    (rewrite equation in injective owner) only

||| Decode an entire native event word into the extended actor grammar.
||| Ownership is an explicit per-event premise; phaseScanOk-to-interval
||| extraction and located lifecycle/release/maximality remain separate.
export
0 phaseEventsExtended : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  {trace : Transitions first finalState} ->
  (nameEq : DecEq name) -> (actor : name) ->
  (trail : AvailabilityTrace name key world error value trace) ->
  (0 owned : All (\event => fst event = Just actor) (phaseEvents nameEq trail)) ->
  ActorLifecycleOnlyExtended nameEq actor trace
phaseEventsExtended nameEq actor (AvailabilityEnd state) owned = ExtendedLifecycleEnd
phaseEventsExtended nameEq actor (AvailabilityStep source (Fired ne ke action tag checked) rest later) owned =
  phaseActionExtended nameEq actor (Fired ne ke action tag checked) rest action Refl
    (All.head owned) (phaseEventsExtended nameEq actor later (All.tail owned))

||| Produce the located extended-core record from an authentic physical
||| interval and its decoded event owners. The grammar field is derived.
||| Choosing the interval from phaseScanOk is NOT an input silently solved.
export
0 locatePhaseEventCore : {name, key, world, error : Type} -> {value : key -> Type} ->
  {initial, finalState : SystemState name key value world error} ->
  {global : Transitions initial finalState} ->
  (nameEq : DecEq name) -> (actor : name) ->
  (start, end : SystemState name key value world error) ->
  (before : Transitions initial start) -> (core : Transitions start end) ->
  (suffix : Transitions end finalState) ->
  (prefixTrail : AvailabilityTrace name key world error value before) ->
  (coreTrail : AvailabilityTrace name key world error value core) ->
  (suffixTrail : AvailabilityTrace name key world error value suffix) ->
  (0 physical : appendTransitions before (appendTransitions core suffix) = global) ->
  (0 owned : All (\event => fst event = Just actor) (phaseEvents nameEq coreTrail)) ->
  LocatedExtendedCore name key world error value nameEq actor global
locatePhaseEventCore nameEq actor start end before core suffix prefixTrail coreTrail suffixTrail physical owned =
  MkLocatedExtendedCore start end before core suffix prefixTrail coreTrail suffixTrail
    (phaseEventsExtended nameEq actor coreTrail owned) physical

||| The event word preserves physical native ordinals exactly, independently
||| of any actor ownership, forcing, or release-acceptance premise.
export
0 phaseEventsCount : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  {trace : Transitions first finalState} ->
  (nameEq : DecEq name) -> (trail : AvailabilityTrace name key world error value trace) ->
  length (phaseEvents nameEq trail) = transitionCount trace
phaseEventsCount nameEq (AvailabilityEnd state) = Refl
phaseEventsCount nameEq (AvailabilityStep source (Fired ne ke action tag checked) rest later) =
  cong S (phaseEventsCount nameEq later)

||| Native lifecycle owner field decoded from phaseEvents' classifier.
||| Orchestration cases cannot masquerade as the strictly earlier lifecycle.
export
0 phaseLifeOwnerDecoded : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (actor : name) ->
  (source : SystemState name key value world error) ->
  (action : Action name key value world error) ->
  (0 owner : phaseActionOwner nameEq source action = Just actor) ->
  (0 life : isLifecycleAction action = True) -> actionOwner action = actor
phaseLifeOwnerDecoded nameEq actor source (OInsert child parent component) owner life = absurd life
phaseLifeOwnerDecoded nameEq actor source (ORetire child) owner life = absurd life
phaseLifeOwnerDecoded nameEq actor source (ORemove child) owner life = absurd life
phaseLifeOwnerDecoded nameEq actor source (LBegin selected) owner life = injective owner
phaseLifeOwnerDecoded nameEq actor source (LAdvance selected) owner life = injective owner
phaseLifeOwnerDecoded nameEq actor source (LDivert selected) owner life = injective owner
phaseLifeOwnerDecoded nameEq actor source (LUnload selected) owner life = injective owner
phaseLifeOwnerDecoded nameEq actor source (LLeave selected) owner life = injective owner
