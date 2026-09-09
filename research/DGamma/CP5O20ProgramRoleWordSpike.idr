module DGamma.CP5O20ProgramRoleWordSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5O20BeginObservationSpike
import DGamma.CP5O20CanonicalActionCompletenessSpike
import DGamma.CP5O19AdvanceObservationSpike
import DGamma.CP5O20NativeAdvanceAttachmentSpike
import DGamma.CP5O20SingleRoleAdvanceExtractionSpike
import DGamma.CP5O20PairedAdvanceSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Expected successful remaining activation tags for a finite program.
||| Empty and singleton programs finish on one Advance; longer programs emit
||| Iter until their final Finish. This function alone does not certify a run.
public export
o20ProgramRoleWord : {step : Type} -> List step -> List RuleTag
o20ProgramRoleWord [] = [LFinishTag]
o20ProgramRoleWord [current] = [LFinishTag]
o20ProgramRoleWord (current :: next :: later) = LIterTag :: o20ProgramRoleWord (next :: later)

||| Executable per-fiber successful-activation remainder. Inactive includes
||| its next Begin, Reloading includes its remaining Advances, and all other
||| phases/absence give the empty word. Applicability is not asserted by this
||| observer (in particular an inactive failure need not admit Begin).
public export
o20FiberRoleRemainder :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  Maybe (Fiber name key value world error) -> List RuleTag
o20FiberRoleRemainder Nothing = []
o20FiberRoleRemainder (Just (MkFiber component parent retiredFlag table (Inactive outcome))) =
  LBeginTag :: o20ProgramRoleWord (componentProgram component)
o20FiberRoleRemainder (Just (MkFiber component parent retiredFlag table (Reloading remaining accumulator view))) =
  o20ProgramRoleWord remaining
o20FiberRoleRemainder (Just (MkFiber component parent retiredFlag table (Active accumulator view))) = []
o20FiberRoleRemainder (Just (MkFiber component parent retiredFlag table (Unloading accumulator view outcome))) = []

||| An observed ACTUAL Begin consumes exactly the head Begin of its fiber's
||| remainder. The after lookup is produced by native replacement and the
||| observation's own endpoint equation, not an assumed target lookup.
export
0 o20ObservedBeginRoleConsumption :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (before, afterState : SystemState name key value world error) ->
  O20BeginObservation name key world error value nameEq keyEq actor before afterState ->
  (o20FiberRoleRemainder
    (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry before)) =
   LBeginTag :: o20FiberRoleRemainder
    (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry afterState)))
o20ObservedBeginRoleConsumption nameEq keyEq actor before afterState
  (MkO20BeginObservation component parent table view found resolved afterExact) =
    rewrite sym afterExact in
    rewrite lookupReplacedFiber @{nameEq} actor
      (MkFiber component parent False table (Inactive Nothing))
      (MkFiber component parent False table (Reloading (componentProgram component) id view))
      (registry before) found in
    rewrite found in Refl

||| Evaluator determinism attaches the SAME observed successful Advance to
||| BOTH its actual tag and actual endpoint. No reconstructed-state equality
||| or caller tag equation is input; native source/callback observations own it.
export
0 o20ActualAdvanceObservedResult :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (afterState : SystemState name key value world error) -> (tag : RuleTag) ->
  (component : Component key value world error) -> (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (step : StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component)) ->
  (rest : List (StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component))) ->
  (older : LocalState key value world (componentProvisions component) -> LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor fibers = Just (MkFiber component parent retiredFlag table (Reloading (step :: rest) older view))) ->
  (targetFiber {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (MkFiber component parent retiredFlag table (Reloading (step :: rest) older view)) fibers = Just view) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (LAdvance actor) (MkSystemState ambient fibers) = Just (tag, afterState)) ->
  (observed : O20NativeStepValues name key world error value nameEq keyEq (MkSystemState ambient fibers) component table step view) ->
  ((tag, afterState) = ((case rest of [] => LFinishTag; _ :: _ => LIterTag),
    MkSystemState (localWorld (stepObservedAfter (nativeCallback observed)))
    (replaceBinding @{nameEq} actor
      (MkFiber component parent retiredFlag (localTable (stepObservedAfter (nativeCallback observed)))
        (o20SuccessfulAdvanceLifecycle {name} {key} {value} {world} {error} rest
          (pushLocalUndo {key} {value} {world} @{keyEq} (componentProvisions component) older (stepObservedUndo (nativeCallback observed))) view)) fibers)))
o20ActualAdvanceObservedResult nameEq keyEq actor ambient fibers afterState tag component parent retiredFlag table step rest older view
  found target checked (MkO20NativeStepValues capability resolved callback) =
    justInjective (trans
      (sym (checkedActionProjects nameEq keyEq (LAdvance actor) (MkSystemState ambient fibers) afterState tag checked))
      (o20ObservedAdvanceRawEquation nameEq keyEq actor ambient fibers component parent retiredFlag table step rest older view
        capability (stepObservedAfter callback) (stepObservedUndo callback) found target resolved (stepObservedRan callback)))

||| Every observed successful NONEMPTY native Advance consumes exactly its
||| actual head role. Both tag and target come from one evaluator equation;
||| the actual target lookup is proved by replacement. No successor role
||| equation or lookup is supplied. Empty-program Finish is separate.
export
0 o20ObservedAdvanceRoleConsumption :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (afterState : SystemState name key value world error) -> (tag : RuleTag) ->
  (component : Component key value world error) -> (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (step : StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component)) ->
  (rest : List (StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component))) ->
  (older : LocalState key value world (componentProvisions component) -> LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor fibers = Just (MkFiber component parent retiredFlag table (Reloading (step :: rest) older view))) ->
  (targetFiber {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (MkFiber component parent retiredFlag table (Reloading (step :: rest) older view)) fibers = Just view) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (LAdvance actor) (MkSystemState ambient fibers) = Just (tag, afterState)) ->
  (observed : O20NativeStepValues name key world error value nameEq keyEq (MkSystemState ambient fibers) component table step view) ->
  (o20FiberRoleRemainder
    (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor fibers) =
   tag :: o20FiberRoleRemainder
    (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry afterState)))
o20ObservedAdvanceRoleConsumption nameEq keyEq actor ambient fibers afterState tag component parent retiredFlag table step [] older view found target checked observed =
    rewrite cong fst (o20ActualAdvanceObservedResult nameEq keyEq actor ambient fibers afterState tag component parent retiredFlag table step [] older view found target checked observed) in
    rewrite cong snd (o20ActualAdvanceObservedResult nameEq keyEq actor ambient fibers afterState tag component parent retiredFlag table step [] older view found target checked observed) in
    rewrite lookupReplacedFiber @{nameEq} actor
      (MkFiber component parent retiredFlag table (Reloading (step :: []) older view))
      (MkFiber component parent retiredFlag (localTable (stepObservedAfter (nativeCallback observed)))
        (o20SuccessfulAdvanceLifecycle []
          (pushLocalUndo @{keyEq} (componentProvisions component) older (stepObservedUndo (nativeCallback observed))) view)) fibers found in
    rewrite found in Refl
o20ObservedAdvanceRoleConsumption nameEq keyEq actor ambient fibers afterState tag component parent retiredFlag table step (next :: more) older view found target checked observed =
    rewrite cong fst (o20ActualAdvanceObservedResult nameEq keyEq actor ambient fibers afterState tag component parent retiredFlag table step (next :: more) older view found target checked observed) in
    rewrite cong snd (o20ActualAdvanceObservedResult nameEq keyEq actor ambient fibers afterState tag component parent retiredFlag table step (next :: more) older view found target checked observed) in
    rewrite lookupReplacedFiber @{nameEq} actor
      (MkFiber component parent retiredFlag table (Reloading (step :: (next :: more)) older view))
      (MkFiber component parent retiredFlag (localTable (stepObservedAfter (nativeCallback observed)))
        (o20SuccessfulAdvanceLifecycle (next :: more)
          (pushLocalUndo @{keyEq} (componentProvisions component) older (stepObservedUndo (nativeCallback observed))) view)) fibers found in
    rewrite found in Refl
