module DGamma.CP4ProgressStepCore

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4ProgressPotential
import Data.Nat
import Decidable.Equality

%default total

||| The two local facts needed by the amortized Equation-61 induction. Every
||| successful lifecycle action has positive source potential; when the target
||| provider view stays fixed, that action consumes one unit of potential.
public export
record ActorPotentialStep
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (bound : Nat)
  (actor : name)
  (before, afterState : SystemState name key value world error) where
  constructor MkActorPotentialStep
  sourcePotentialPositive :
    LTE 1 (actorTargetPotential @{nameEq} @{keyEq} bound actor before)
  stayedPotentialDrops :
    sameTarget @{nameEq}
      (targetProvidersAt @{nameEq} @{keyEq} actor before)
      (targetProvidersAt @{nameEq} @{keyEq} actor afterState) = True ->
    LTE (S (actorTargetPotential @{nameEq} @{keyEq} bound actor afterState))
      (actorTargetPotential @{nameEq} @{keyEq} bound actor before)

public export
0 lteRefl : (number : Nat) -> LTE number number
lteRefl Z = LTEZero
lteRefl (S number) = LTESucc (lteRefl number)

public export
0 lteWeakenRight : LTE left right -> LTE left (S right)
lteWeakenRight LTEZero = LTEZero
lteWeakenRight (LTESucc smaller) = LTESucc (lteWeakenRight smaller)

public export
0 oneLTEPlus : (suffix : Nat) -> LTE 1 (suffix + 1)
oneLTEPlus Z = LTESucc LTEZero
oneLTEPlus (S suffix) = lteWeakenRight (oneLTEPlus suffix)

public export
0 oneLTEBoundPlusTwo : (bound : Nat) -> LTE 1 (bound + 2)
oneLTEBoundPlusTwo Z = LTESucc LTEZero
oneLTEBoundPlusTwo (S bound) = lteWeakenRight (oneLTEBoundPlusTwo bound)

public export
0 oneLTEBoundPlusThree : (bound : Nat) -> LTE 1 (bound + 3)
oneLTEBoundPlusThree Z = LTESucc LTEZero
oneLTEBoundPlusThree (S bound) = lteWeakenRight (oneLTEBoundPlusThree bound)

public export
0 oneLTEBoundPlusFour : (bound : Nat) -> LTE 1 (bound + 4)
oneLTEBoundPlusFour Z = LTESucc LTEZero
oneLTEBoundPlusFour (S bound) = lteWeakenRight (oneLTEBoundPlusFour bound)

public export
0 successorSuccessorLTEPlusTwo : (remaining, bound : Nat) ->
  LTE remaining bound -> LTE (S (S remaining)) (bound + 2)
successorSuccessorLTEPlusTwo Z Z LTEZero = LTESucc (LTESucc LTEZero)
successorSuccessorLTEPlusTwo Z (S bound) LTEZero =
  lteWeakenRight (successorSuccessorLTEPlusTwo Z bound LTEZero)
successorSuccessorLTEPlusTwo (S remaining) (S bound) (LTESucc smaller) =
  LTESucc (successorSuccessorLTEPlusTwo remaining bound smaller)

potentialFromLookup :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  DecEq name => Nat -> Maybe (Fiber name key value world error) ->
  Maybe (List name) -> Nat
potentialFromLookup bound Nothing target = Z
potentialFromLookup bound (Just fiber) target =
  fiberTargetPotential bound fiber target

public export
0 actorPotentialLookupEquation :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (bound : Nat) ->
  (actor : name) -> (state : SystemState name key value world error) ->
  actorTargetPotential @{nameEq} @{keyEq} {name = name} {key = key}
    {world = world} {error = error} {value = value} bound actor state =
    potentialFromLookup @{nameEq} {name = name} {key = key} {world = world}
      {error = error} {value = value} bound
      (lookupFiber @{nameEq} {key = key} {world = world} {error = error}
        {value = value} actor (registry state))
      (targetProvidersAt @{nameEq} @{keyEq} {name = name} {key = key}
        {world = world} {error = error} {value = value} actor state)
actorPotentialLookupEquation nameEq keyEq bound actor state
  with (lookupFiber @{nameEq} actor (registry state)) proof found
  actorPotentialLookupEquation nameEq keyEq bound actor state | Nothing = Refl
  actorPotentialLookupEquation nameEq keyEq bound actor state | Just fiber =
    cong (fiberTargetPotential @{nameEq} bound fiber)
      (targetProvidersAtLookup nameEq keyEq actor state fiber found)

public export
0 actorTargetPotentialAtLookup :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (bound : Nat) ->
  (actor : name) -> (state : SystemState name key value world error) ->
  (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} actor (registry state) = Just fiber ->
  actorTargetPotential @{nameEq} @{keyEq} bound actor state =
    fiberTargetPotential @{nameEq} bound fiber
      (targetProvidersAt @{nameEq} @{keyEq} actor state)
actorTargetPotentialAtLookup nameEq keyEq bound actor state fiber found =
  rewrite actorPotentialLookupEquation nameEq keyEq bound actor state in
  rewrite found in Refl

0 potentialCaseTargetEqual :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (bound : Nat) ->
  (found : Maybe (Fiber name key value world error)) ->
  (leftTarget, rightTarget : Maybe (List name)) ->
  leftTarget = rightTarget ->
  potentialFromLookup @{nameEq} {name = name} {key = key} {world = world}
    {error = error} {value = value} bound found leftTarget =
  potentialFromLookup @{nameEq} {name = name} {key = key} {world = world}
    {error = error} {value = value} bound found rightTarget
potentialCaseTargetEqual nameEq bound found leftTarget leftTarget Refl = Refl

public export
0 inactiveAvailablePotential :
  (nameEq : DecEq name) -> (bound : Nat) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (providers : List name) ->
  fiberTargetPotential @{nameEq} bound
    (MkFiber component parent retiredFlag table (Inactive Nothing))
    (Just providers) = bound + 2
inactiveAvailablePotential nameEq bound component parent retiredFlag table
  providers = Refl

public export
0 reloadingCommittedPotential :
  (nameEq : DecEq name) -> (bound : Nat) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (remaining : List (StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component))) ->
  (accumulator : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  fiberTargetPotential @{nameEq} bound
    (MkFiber component parent retiredFlag table
      (Reloading remaining accumulator view))
    (Just (viewProviders view)) = S (length remaining)
reloadingCommittedPotential nameEq bound component parent retiredFlag table
  remaining accumulator view =
    rewrite sameTargetJustReflexive nameEq (viewProviders view) in Refl

public export
0 reloadingStalePotential :
  (nameEq : DecEq name) -> (bound : Nat) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (remaining : List (StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component))) ->
  (accumulator : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (target : Maybe (List name)) ->
  sameTarget @{nameEq} target (Just (viewProviders view)) = False ->
  fiberTargetPotential @{nameEq} bound
    (MkFiber component parent retiredFlag table
      (Reloading remaining accumulator view)) target = bound + 4
reloadingStalePotential nameEq bound component parent retiredFlag table
  remaining accumulator view target stale = rewrite stale in Refl

public export
0 activeStalePotential :
  (nameEq : DecEq name) -> (bound : Nat) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (accumulator : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (target : Maybe (List name)) ->
  sameTarget @{nameEq} target (Just (viewProviders view)) = False ->
  fiberTargetPotential @{nameEq} bound
    (MkFiber component parent retiredFlag table (Active accumulator view))
    target = bound + 4
activeStalePotential nameEq bound component parent retiredFlag table accumulator
  view target stale = rewrite stale in Refl

public export
0 unloadingCleanPotential :
  (nameEq : DecEq name) -> (bound : Nat) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (accumulator : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  fiberTargetPotential @{nameEq} bound
    (MkFiber component parent retiredFlag table
      (Unloading accumulator view Nothing)) target = bound + 3
unloadingCleanPotential nameEq bound component parent retiredFlag table
  accumulator view = Refl

public export
0 unloadingFailedPotential :
  (nameEq : DecEq name) -> (bound : Nat) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (accumulator : LocalState key value world (componentProvisions component) ->
    LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (err : error) ->
  fiberTargetPotential @{nameEq} bound
    (MkFiber component parent retiredFlag table
      (Unloading accumulator view (Just err))) target = 1
unloadingFailedPotential nameEq bound component parent retiredFlag table
  accumulator view err = Refl

public export
0 inactiveFailedPotential :
  (nameEq : DecEq name) -> (bound : Nat) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (err : error) ->
  fiberTargetPotential @{nameEq} bound
    (MkFiber component parent retiredFlag table (Inactive (Just err))) target = Z
inactiveFailedPotential nameEq bound component parent retiredFlag table err = Refl

public export
0 boundPlusThreeStep : (bound : Nat) -> LTE (S (bound + 3)) (bound + 4)
boundPlusThreeStep Z = lteRefl 4
boundPlusThreeStep (S bound) = LTESucc (boundPlusThreeStep bound)

public export
0 inactiveCleanAfterUnload : (nameEq : DecEq name) -> (bound : Nat) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (target : Maybe (List name)) ->
  LTE (S (fiberTargetPotential @{nameEq} bound
    (MkFiber component parent retiredFlag table (Inactive Nothing)) target))
    (bound + 3)
inactiveCleanAfterUnload nameEq bound component parent retiredFlag table Nothing =
  oneLTEBoundPlusThree bound
inactiveCleanAfterUnload nameEq Z component parent retiredFlag table
  (Just providers) = lteRefl 3
inactiveCleanAfterUnload nameEq (S bound) component parent retiredFlag table
  (Just providers) = LTESucc
    (inactiveCleanAfterUnload nameEq bound component parent retiredFlag table
      (Just providers))

||| A foreign local update leaves the selected fiber exact. Under the
||| `TargetStayed` premise, the provider-name target is exact as well, so the
||| factored potential is unchanged without inspecting the evaluator rule.
public export
0 foreignActorTargetPotentialEqual :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (bound : Nat) ->
  (selected : name) ->
  (action : Action name key value world error) ->
  (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  Not (selected = actionOwner action) ->
  checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState) ->
  sameTarget @{nameEq}
    (targetProvidersAt @{nameEq} @{keyEq} selected before)
    (targetProvidersAt @{nameEq} @{keyEq} selected afterState) = True ->
  actorTargetPotential @{nameEq} @{keyEq} bound selected before =
    actorTargetPotential @{nameEq} @{keyEq} bound selected afterState
foreignActorTargetPotentialEqual nameEq keyEq bound selected action tag before
  afterState distinct checked targetStayed =
    let 0 raw = checkedActionProjects nameEq keyEq action before afterState tag
          checked
        0 update = applyActionLocalUpdate nameEq keyEq action before afterState
          tag raw
        0 lookupFrame = systemLocalUpdateForeign nameEq selected
          (actionOwner action) distinct before afterState update
        0 targetEqual = sameTargetTrueEqual nameEq
          (targetProvidersAt @{nameEq} @{keyEq} selected before)
          (targetProvidersAt @{nameEq} @{keyEq} selected afterState)
          targetStayed
    in rewrite actorPotentialLookupEquation nameEq keyEq bound selected before in
      rewrite actorPotentialLookupEquation nameEq keyEq bound selected afterState in
      rewrite targetEqual in rewrite lookupFrame in Refl
