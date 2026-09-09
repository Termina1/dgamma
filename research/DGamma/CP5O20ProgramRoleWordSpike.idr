module DGamma.CP5O20ProgramRoleWordSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4ProgressPotential
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

||| At the actual Iter source packet, produce capability/callback values and
||| the exact role consumption. Only the one Iter constructor is eliminated;
||| no caller success value, shared program or successor lookup is required.
export
0 o20IterRoleAtSource :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (before, afterState : SystemState name key value world error) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (LAdvance actor) before = Just (LIterTag, afterState)) ->
  PaperAdvanceSource name key world error value nameEq keyEq actor LIterTag before ->
  (o20FiberRoleRemainder
    (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry before)) =
   LIterTag :: o20FiberRoleRemainder
    (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry afterState)))
o20IterRoleAtSource nameEq keyEq actor _ afterState checked
  (AdvanceSourceIter {ambient} {fibers} {component} {parent} {retiredFlag} {table}
    {step} {next} {more} {accumulator} {view} Refl found target) =
    o20ObservedAdvanceRoleConsumption nameEq keyEq actor ambient fibers afterState LIterTag
      component parent retiredFlag table step (next :: more) accumulator view found target checked
      (o20IterNativeValues nameEq keyEq actor (MkSystemState ambient fibers) afterState
        component parent retiredFlag table step next more accumulator view found checked)

||| Empty-program Finish consumes its single Finish role. Its actual target
||| is attached by native evaluator determinism, and its actual lookup comes
||| from replacement. There is no callback in this branch.
export
0 o20EmptyFinishRoleConsumption :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (afterState : SystemState name key value world error) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (retiredFlag : Bool) -> (table : OwnedTable key value (componentProvisions component)) ->
  (older : LocalState key value world (componentProvisions component) -> LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor fibers =
    Just (MkFiber component parent retiredFlag table (Reloading [] older view))) ->
  (targetFiber {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (MkFiber component parent retiredFlag table (Reloading [] older view)) fibers = Just view) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (LAdvance actor) (MkSystemState ambient fibers) = Just (LFinishTag, afterState)) ->
  (o20FiberRoleRemainder
    (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor fibers) =
   LFinishTag :: o20FiberRoleRemainder
    (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry afterState)))
o20EmptyFinishRoleConsumption nameEq keyEq actor ambient fibers afterState
  component parent retiredFlag table older view found target checked =
    rewrite cong snd (justInjective (trans
      (sym (checkedActionProjects nameEq keyEq (LAdvance actor)
        (MkSystemState ambient fibers) afterState LFinishTag checked))
      (the (applyAction @{nameEq} @{keyEq} (LAdvance actor) (MkSystemState ambient fibers) =
        Just (LFinishTag, MkSystemState ambient (replaceBinding @{nameEq} actor
          (MkFiber component parent retiredFlag table (Active older view)) fibers)))
        (rewrite found in rewrite target in
          rewrite trans (viewEqSameNameList nameEq view view)
            (sameNameListReflexive nameEq (DGamma.Calculus.viewProviders view)) in Refl)))) in
    rewrite lookupReplacedFiber @{nameEq} actor
      (MkFiber component parent retiredFlag table (Reloading [] older view))
      (MkFiber component parent retiredFlag table (Active older view)) fibers found in
    rewrite found in Refl

||| The two actual Finish source constructors each consume exactly Finish.
||| Empty has no callback; singleton produces its own native success values.
||| This is single-role source elimination, not an Either callback adapter.
export
0 o20FinishRoleAtSource :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (before, afterState : SystemState name key value world error) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (LAdvance actor) before = Just (LFinishTag, afterState)) ->
  PaperAdvanceSource name key world error value nameEq keyEq actor LFinishTag before ->
  (o20FiberRoleRemainder
    (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry before)) =
   LFinishTag :: o20FiberRoleRemainder
    (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry afterState)))
o20FinishRoleAtSource nameEq keyEq actor _ afterState checked
  (AdvanceSourceFinishEmpty {ambient} {fibers} {component} {parent} {retiredFlag} {table}
    {accumulator} {view} Refl found target) =
    o20EmptyFinishRoleConsumption nameEq keyEq actor ambient fibers afterState
      component parent retiredFlag table accumulator view found target checked
o20FinishRoleAtSource nameEq keyEq actor _ afterState checked
  (AdvanceSourceFinishOne {ambient} {fibers} {component} {parent} {retiredFlag} {table}
    {step} {accumulator} {view} Refl found target) =
    o20ObservedAdvanceRoleConsumption nameEq keyEq actor ambient fibers afterState LFinishTag
      component parent retiredFlag table step [] accumulator view found target checked
      (o20FinishOneNativeValues nameEq keyEq actor (MkSystemState ambient fibers) afterState
        component parent retiredFlag table step accumulator view found checked)

||| EVERY actual paper activation consumes its own native tag from the
||| owner's remainder. Native source and callback observations are produced
||| internally; neither a pre-cut relation nor successor word is assumed.
export
0 o20ActualPaperRoleConsumption :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (before, afterState : SystemState name key value world error) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (checked : (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    action before = Just (tag, afterState))) ->
  PaperActivationStep (Fired {name} {key} {value} {world} {error}
    {before} {afterState} nameEq keyEq action tag checked) ->
  (o20FiberRoleRemainder
    (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (actionOwner action) (registry before)) =
   tag :: o20FiberRoleRemainder
    (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (actionOwner action) (registry afterState)))
o20ActualPaperRoleConsumption {name} {key} {value} {world} {error}
  nameEq keyEq before afterState action tag checked
  (PaperBeginStep {actor} actionExact tagExact) =
    replace {p = \selected => (o20FiberRoleRemainder (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry before)) = tag :: o20FiberRoleRemainder (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry afterState)))}
      (sym (cong actionOwner actionExact))
      (replace {p = \observedTag => (o20FiberRoleRemainder (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry before)) = observedTag :: o20FiberRoleRemainder (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry afterState)))}
        (sym tagExact)
        (o20ObservedBeginRoleConsumption nameEq keyEq actor before afterState
        (o20ObserveActualBegin nameEq keyEq actor before afterState (MkBeginStep (trans (sym (cong (\observedAction => checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} observedAction before) actionExact))
          (trans checked (cong (\observedTag => Just (observedTag, afterState)) tagExact)))))))

o20ActualPaperRoleConsumption {name} {key} {value} {world} {error}
  nameEq keyEq before afterState action tag checked
  (PaperIterStep {actor} actionExact tagExact) =
    replace {p = \selected => (o20FiberRoleRemainder (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry before)) = tag :: o20FiberRoleRemainder (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry afterState)))}
      (sym (cong actionOwner actionExact))
      (replace {p = \observedTag => (o20FiberRoleRemainder (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry before)) = observedTag :: o20FiberRoleRemainder (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry afterState)))}
        (sym tagExact)
        (o20IterRoleAtSource nameEq keyEq actor before afterState (trans (sym (cong (\observedAction => checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} observedAction before) actionExact))
          (trans checked (cong (\observedTag => Just (observedTag, afterState)) tagExact)))
        (paperAdvanceSource nameEq keyEq actor LIterTag
          (checkedActionProjects nameEq keyEq (LAdvance actor) before afterState LIterTag (trans (sym (cong (\observedAction => checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} observedAction before) actionExact))
          (trans checked (cong (\observedTag => Just (observedTag, afterState)) tagExact)))) (Left Refl))))

o20ActualPaperRoleConsumption {name} {key} {value} {world} {error}
  nameEq keyEq before afterState action tag checked
  (PaperFinishStep {actor} actionExact tagExact) =
    replace {p = \selected => (o20FiberRoleRemainder (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry before)) = tag :: o20FiberRoleRemainder (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry afterState)))}
      (sym (cong actionOwner actionExact))
      (replace {p = \observedTag => (o20FiberRoleRemainder (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry before)) = observedTag :: o20FiberRoleRemainder (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry afterState)))}
        (sym tagExact)
        (o20FinishRoleAtSource nameEq keyEq actor before afterState (trans (sym (cong (\observedAction => checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} observedAction before) actionExact))
          (trans checked (cong (\observedTag => Just (observedTag, afterState)) tagExact)))
        (paperAdvanceSource nameEq keyEq actor LFinishTag
          (checkedActionProjects nameEq keyEq (LAdvance actor) before afterState LFinishTag (trans (sym (cong (\observedAction => checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} observedAction before) actionExact))
          (trans checked (cong (\observedTag => Just (observedTag, afterState)) tagExact)))) (Right Refl))))

||| The complete lifecycle-tag subsequence of ONE actual actor-only body.
||| Genuine yielded Insert edges are omitted from this projection, NOT from
||| the native trace and NOT declared zero transitions. No decider is used.
public export
0 o20ActorLifecycleRoleWord :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  {selected : name} -> {trace : Transitions first finalState} ->
  ActorLifecycleOnly selected trace -> List RuleTag
o20ActorLifecycleRoleWord ActorLifecycleEnd = []
o20ActorLifecycleRoleWord (ActorLifecycleStep step rest lifecycle owner later) =
  transitionTag step :: o20ActorLifecycleRoleWord later
o20ActorLifecycleRoleWord (ActorYieldedRegistrationStep step rest inserted later) =
  o20ActorLifecycleRoleWord later

||| Native orchestration role evidence determines the primitive lifecycle
||| discriminator. No action/tag equality is eliminated in the patterns.
export
0 o20OrchestrationRoleNonLifecycle :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {before, afterState : SystemState name key value world error} ->
  {step : Transition before afterState} ->
  PaperOrchestrationStep step ->
  (isLifecycleAction (transitionAction step) = False)
o20OrchestrationRoleNonLifecycle (PaperInsertStep exact) =
  trans (cong isLifecycleAction exact) Refl
o20OrchestrationRoleNonLifecycle (PaperRetireStep exact) =
  trans (cong isLifecycleAction exact) Refl
o20OrchestrationRoleNonLifecycle (PaperRemoveStep exact) =
  trans (cong isLifecycleAction exact) Refl

||| Consume one whole-word canonical role at a lifecycle node. This theorem
||| returns only the role-remainder equation, NOT a callback-domain adapter.
||| The orchestration branch contradicts the node's own lifecycle equation.
export
0 o20CanonicalLifecycleRoleConsumption :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (before, afterState : SystemState name key value world error) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (checked : (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    action before = Just (tag, afterState))) ->
  Either
    (PaperActivationStep (Fired {name} {key} {value} {world} {error} {before} {afterState} nameEq keyEq action tag checked))
    (PaperOrchestrationStep (Fired {name} {key} {value} {world} {error} {before} {afterState} nameEq keyEq action tag checked)) ->
  (isLifecycleAction action = True) ->
  (o20FiberRoleRemainder
    (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (actionOwner action) (registry before)) =
   tag :: o20FiberRoleRemainder
    (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (actionOwner action) (registry afterState)))
o20CanonicalLifecycleRoleConsumption nameEq keyEq before afterState action tag checked (Left paperRole) lifecycle =
  o20ActualPaperRoleConsumption nameEq keyEq before afterState action tag checked paperRole
o20CanonicalLifecycleRoleConsumption nameEq keyEq before afterState action tag checked (Right orchestrationRole) lifecycle =
  absurd (trans (sym (o20OrchestrationRoleNonLifecycle orchestrationRole)) lifecycle)
