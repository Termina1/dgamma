module DGamma.L2R6Iteration

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R3ForcedClosure
import DGamma.L2R5RootCatalog
import DGamma.L2R5Extensional
import DGamma.L2R5ExtensionalRetire
import DGamma.L2R6ForcedScan
import DGamma.L2R6Anchors
import DGamma.L2R6FrontNormal
import Data.List
import Data.List.Elem
import Data.Nat
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Admitted predecessor shapes at the ACTUAL source of a located crossing.
||| Lifecycle has explicit Bool/equation; child controls carry real installed
||| fiber/parent evidence. Every owning actor/parent is foreign to the root.
||| No constructor admits an unplaced root-orchestration predecessor.
public export
data AdmittedCrossing :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  DecEq name -> name -> SystemState name key value world error -> Action name key value world error -> Type where
  CrossLifecycle : {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {root : name} -> {source : SystemState name key value world error} ->
    {action : Action name key value world error} ->
    (observed : Bool) -> (0 equation : isLifecycleAction action = observed) -> (0 accepted : observed = True) ->
    (0 foreign : actionOwner action = root -> Void) -> AdmittedCrossing nameEq root source action
  CrossChildInsert : {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {root, child, parent : name} -> {source : SystemState name key value world error} ->
    {component : Component key value world error} ->
    (0 foreign : parent = root -> Void) -> AdmittedCrossing nameEq root source (OInsert child (ChildOf parent) component)
  CrossChildRetire : {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {root, child, parent : name} -> {source : SystemState name key value world error} ->
    (fiber : Fiber name key value world error) ->
    (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry source) = Just fiber) ->
    (0 ownChild : fiberParent fiber = ChildOf parent) -> (0 foreign : parent = root -> Void) ->
    AdmittedCrossing nameEq root source (ORetire child)
  CrossChildRemove : {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {root, child, parent : name} -> {source : SystemState name key value world error} ->
    (fiber : Fiber name key value world error) ->
    (0 found : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child (registry source) = Just fiber) ->
    (0 ownChild : fiberParent fiber = ChildOf parent) -> (0 foreign : parent = root -> Void) ->
    AdmittedCrossing nameEq root source (ORemove child)

||| Exact chronological action word of a checked native trail, including ALL
||| root/child orchestration and lifecycle actions. Not the coarser root word.
public export
nativeActionWord : {name, key, world, error : Type} -> {value : key -> Type} ->
  {0 first, finalState : SystemState name key value world error} ->
  {0 trace : Transitions first finalState} ->
  DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace name key world error value trace -> List (Action name key value world error)
nativeActionWord (DGamma.CP5AvailabilityAwarePlacement.AvailabilityEnd state) = []
nativeActionWord (DGamma.CP5AvailabilityAwarePlacement.AvailabilityStep source (Fired ne ke action tag checked) rest later) = action :: nativeActionWord later

||| ONE actual adjacent action interchange between two checked runs from the
||| same initial state. Actual located source/crossing and moved birth, exact
||| full action words, trace-forcing, both declaration-free current cuts,
||| observed exact-one total distance, and RegistryExtensional endpoints are
||| owned together. This is not an original-edge-only general square producer
||| or a proof of the frozen SameExternalOrchestration relation.
public export
record AdmittedDistanceMove
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, oldFinal, newFinal : SystemState name key value world error}
  {oldTrace : Transitions initial oldFinal} {newTrace : Transitions initial newFinal}
  (oldTrail : DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace name key world error value oldTrace)
  (newTrail : DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace name key world error value newTrace) where
  constructor MkAdmittedDistanceMove
  movedRoot : name
  movedComponent : Component key value world error
  prefixWord : List (Action name key value world error)
  crossedAction : Action name key value world error
  suffixWord : List (Action name key value world error)
  crossedOccurrence : LocatedActionOccurrence crossedAction oldTrace
  movedBirthOccurrence : LocatedActionOccurrence (OInsert movedRoot Root movedComponent) newTrace
  0 crossedOrdinalExact : locatedActionOrdinal crossedOccurrence = length prefixWord
  0 movedBirthOrdinalExact : locatedActionOrdinal movedBirthOccurrence = length prefixWord
  crossingAdmitted : AdmittedCrossing nameEq movedRoot (actionBeforeState crossedOccurrence) crossedAction
  0 oldRootForced : ForcedOnTrace nameEq keyEq oldTrail (S (length prefixWord))
  0 oldWordExact : nativeActionWord oldTrail = prefixWord ++ crossedAction :: OInsert movedRoot Root movedComponent :: suffixWord
  0 newWordExact : nativeActionWord newTrail = prefixWord ++ OInsert movedRoot Root movedComponent :: crossedAction :: suffixWord
  0 oldCurrentCut : DGamma.CP5AvailabilityAwarePlacement.rootDeclaredProvisionsFree name key world error value keyEq movedComponent (actionAfterState crossedOccurrence) = True
  0 newCurrentCut : DGamma.CP5AvailabilityAwarePlacement.rootDeclaredProvisionsFree name key world error value keyEq movedComponent (actionBeforeState movedBirthOccurrence) = True
  beforeDistance : Nat
  afterDistance : Nat
  0 beforeDistanceEquation : totalDistance nameEq keyEq oldTrail = beforeDistance
  0 afterDistanceEquation : totalDistance nameEq keyEq newTrail = afterDistance
  0 dropsExactlyOne : beforeDistance = S afterDistance
  0 moveEndpoints : RegistryExtensional name key world error value nameEq oldFinal newFinal

||| Finite checked iteration of actual one-step moves. The middle TRAIL is
||| shared literally by adjacent iterations; endpoint preservation itself is
||| extensional, never equality of independently reconstructed registry states.
public export
data DistanceIteration :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  DecEq name -> DecEq key ->
  {initial, oldFinal, newFinal : SystemState name key value world error} ->
  {oldTrace : Transitions initial oldFinal} -> {newTrace : Transitions initial newFinal} ->
  DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace name key world error value oldTrace ->
  DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace name key world error value newTrace -> Type where
  IterationDone : {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {keyEq : DecEq key} ->
    {initial, finalState : SystemState name key value world error} ->
    {trace : Transitions initial finalState} ->
    (trail : DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace name key world error value trace) -> DistanceIteration nameEq keyEq trail trail
  IterationMove : {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {keyEq : DecEq key} ->
    {initial, oldFinal, middleFinal, newFinal : SystemState name key value world error} ->
    {oldTrace : Transitions initial oldFinal} -> {middleTrace : Transitions initial middleFinal} ->
    {newTrace : Transitions initial newFinal} ->
    {oldTrail : DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace name key world error value oldTrace} ->
    {middleTrail : DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace name key world error value middleTrace} ->
    {newTrail : DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace name key world error value newTrace} ->
    (0 move : AdmittedDistanceMove name key world error value nameEq keyEq oldTrail middleTrail) ->
    (0 later : DistanceIteration nameEq keyEq middleTrail newTrail) ->
    DistanceIteration nameEq keyEq oldTrail newTrail

||| Every finite produced iteration has RegistryExtensional endpoints.
||| This composes concrete move endpoints; it is NOT move existence or a
||| terminating normalizer from an oracle-free arbitrary input trace.
export
0 iterationEndpoint : {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, oldFinal, newFinal : SystemState name key value world error} ->
  {oldTrace : Transitions initial oldFinal} -> {newTrace : Transitions initial newFinal} ->
  {oldTrail : DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace name key world error value oldTrace} ->
  {newTrail : DGamma.CP5AvailabilityAwarePlacement.AvailabilityTrace name key world error value newTrace} ->
  DistanceIteration nameEq keyEq oldTrail newTrail -> RegistryExtensional name key world error value nameEq oldFinal newFinal
iterationEndpoint (IterationDone trail) = MkRegistryExtensional Refl (\wanted => Refl)
iterationEndpoint (IterationMove move later) = extensionalTransitive (moveEndpoints move) (iterationEndpoint later)
