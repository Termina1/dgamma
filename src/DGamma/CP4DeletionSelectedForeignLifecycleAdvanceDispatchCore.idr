module DGamma.CP4DeletionSelectedForeignLifecycleAdvanceDispatchCore

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionFrameCore
import DGamma.CP4DeletionSelectedBoundary
import DGamma.CP4DeletionSelectedForeignLifecycleAdvance
import DGamma.CP4DeletionSelectedForeignLifecycleCore
import DGamma.CP4DeletionSelectedForeignLifecycleGuards
import DGamma.CP4DeletionSelectedForeignLifecycleReplayCore
import Decidable.Equality

%default total

public export
0 nothingNotJustAdvanceDispatch : Nothing = Just item -> Void
nothingNotJustAdvanceDispatch Refl impossible

public export
0 undefinedDefinedOutcomeImpossible :
  IteratorOutcomeAgreement name key value world error keyEq Nothing
    (Just defined) -> Void
undefinedDefinedOutcomeImpossible agreement impossible

public export
0 successFailureOutcomeImpossible :
  IteratorOutcomeAgreement name key value world error keyEq
    (Just (IteratorYielded yieldedAfter yieldedUndo continuation))
    (Just (IteratorRaised failure)) -> Void
successFailureOutcomeImpossible agreement impossible

public export
0 failureSuccessOutcomeImpossible :
  IteratorOutcomeAgreement name key value world error keyEq
    (Just (IteratorRaised failure))
    (Just (IteratorYielded yieldedAfter yieldedUndo continuation)) -> Void
failureSuccessOutcomeImpossible agreement impossible

||| Runtime form of one concrete L-Advance stage.  It is deliberately expressed
||| with the evaluator's committed resolver and ordered local-table restriction;
||| `resolveEffectValuesProjected` identifies it with `iteratorStageOutcome` at
||| an actual projected system state.
public export
runtimeAdvanceOutcome :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (component : Component key value world error) ->
  (step : StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component)) ->
  (rest : List (StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component))) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (ambient : world) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (source : Registry name key value world error) ->
  Maybe (IteratorStageOutcome name key value world error)
runtimeAdvanceOutcome nameEq keyEq actor component step rest view ambient table
  source =
    iteratorStageOutcomeComponentData nameEq keyEq actor component view step rest
      (projectEffectState @{nameEq}
        (the (SystemState name key value world error)
          (MkSystemState ambient source)))

public export
record ReloadingRightAdvance
  {key, world, error, name : Type} {value : key -> Type}
  {deps : List key} {provision : CoeffectSpec key}
  (leftRemaining : List (StepEffect key value world error deps provision))
  (leftAccumulator : LocalState key value world provision ->
    LocalState key value world provision)
  (leftView : View name deps)
  (rightLifecycle : Lifecycle key value world error name deps provision) where
  constructor MkReloadingRightAdvance
  rightRemaining : List (StepEffect key value world error deps provision)
  rightAdvanceAccumulator : LocalState key value world provision ->
    LocalState key value world provision
  rightAdvanceView : View name deps
  0 rightLifecycleShape : rightLifecycle = Reloading rightRemaining
    rightAdvanceAccumulator rightAdvanceView
  0 remainingSame : leftRemaining = rightRemaining
  0 accumulatorsSame : AccumulatorRelated leftAccumulator
    rightAdvanceAccumulator
  0 viewsSame : leftView = rightAdvanceView

public export
0 reloadingRightAdvance :
  LifecycleControlRelated
    (Reloading leftRemaining leftAccumulator leftView) rightLifecycle ->
  ReloadingRightAdvance leftRemaining leftAccumulator leftView rightLifecycle
reloadingRightAdvance {rightLifecycle = Reloading rightRemaining
  rightAccumulator rightView}
  (ReloadingControls remainingSame accumulatorsSame viewsSame) =
    MkReloadingRightAdvance rightRemaining rightAccumulator rightView Refl
      remainingSame accumulatorsSame viewsSame

public export
0 advanceInactiveIsNothing :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (component : Component key value world error) ->
  (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (outcome : Maybe error) ->
  lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} actor source = Just
    (MkFiber component parent retiredFlag table (Inactive outcome)) ->
  applyAction @{nameEq} @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} (LAdvance actor)
    (MkSystemState ambient source) = Nothing
advanceInactiveIsNothing nameEq keyEq actor ambient source component parent
  retiredFlag table outcome found = rewrite found in Refl

public export
0 advanceActiveIsNothing :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (component : Component key value world error) ->
  (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (accumulator : LocalState key value world
    (componentProvisions component) -> LocalState key value world
    (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} actor source = Just
    (MkFiber component parent retiredFlag table (Active accumulator view)) ->
  applyAction @{nameEq} @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} (LAdvance actor)
    (MkSystemState ambient source) = Nothing
advanceActiveIsNothing nameEq keyEq actor ambient source component parent
  retiredFlag table accumulator view found = rewrite found in Refl

public export
0 advanceUnloadingIsNothing :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (component : Component key value world error) ->
  (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (accumulator : LocalState key value world
    (componentProvisions component) -> LocalState key value world
    (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (outcome : Maybe error) ->
  lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} actor source = Just
    (MkFiber component parent retiredFlag table
      (Unloading accumulator view outcome)) ->
  applyAction @{nameEq} @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} (LAdvance actor)
    (MkSystemState ambient source) = Nothing
advanceUnloadingIsNothing nameEq keyEq actor ambient source component parent
  retiredFlag table accumulator view outcome found = rewrite found in Refl

public export
0 advanceMissingCapabilityIsNothing :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (component : Component key value world error) ->
  (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (step : StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component)) ->
  (rest : List (StepEffect key value world error
    (dependencies (componentDependencies component))
    (componentProvisions component))) ->
  (accumulator : LocalState key value world
    (componentProvisions component) -> LocalState key value world
    (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  lookupFiber @{nameEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} actor source = Just
    (MkFiber component parent retiredFlag table
      (Reloading (step :: rest) accumulator view)) ->
  resolveCommittedValues @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error}
    (dependencies (componentDependencies component)) view source = Nothing ->
  applyAction @{nameEq} @{keyEq} {name = name} {key = key} {value = value}
    {world = world} {error = error} (LAdvance actor)
    (MkSystemState ambient source) = Nothing
advanceMissingCapabilityIsNothing nameEq keyEq actor ambient source component
  parent retiredFlag table step rest accumulator view found resolved =
    rewrite found in rewrite resolved in Refl

public export
0 targetFiberSameFromResolve :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (component : Component key value world error) ->
  (leftParent, rightParent : Parent name) ->
  (retiredFlag : Bool) ->
  (leftTable, rightTable : OwnedTable key value
    (componentProvisions component)) ->
  (leftLifecycle, rightLifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies component))
    (componentProvisions component)) ->
  (left, right : Registry name key value world error) ->
  resolveView @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error}
    (dependencies (componentDependencies component)) left =
  resolveView @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error}
    (dependencies (componentDependencies component)) right ->
  targetFiber @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error}
    (MkFiber component leftParent retiredFlag leftTable leftLifecycle) left =
  targetFiber @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error}
    (MkFiber component rightParent retiredFlag rightTable rightLifecycle) right
targetFiberSameFromResolve nameEq keyEq component leftParent rightParent False
  leftTable rightTable leftLifecycle rightLifecycle left right resolved = resolved
targetFiberSameFromResolve nameEq keyEq component leftParent rightParent True
  leftTable rightTable leftLifecycle rightLifecycle left right resolved = Refl

