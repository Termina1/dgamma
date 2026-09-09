module DGamma.L2R10AdvanceReplay

import Prelude.Types
import Prelude.Interfaces
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
import DGamma.CP4DeletionSelectedForeignLifecycleBegin
import DGamma.CP5L2R1ChildRelocation
import DGamma.L2R2CheckedSnapshot
import DGamma.L2R4RetireReplay
import DGamma.L2R5RetirementFrame
import DGamma.L2R9ResolverRetirement
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Target invariance consumes only the explicit retired Bool observation.
||| No reconstructed/projected conditional family is passed to a consumer.
export
0 retirementTargetAtFlag :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child, parent, actor : name) ->
  (childFiber, actorFiber : Fiber name key value world error) ->
  (source : Registry name key value world error) ->
  (frame : RetirementProviderFrame name key world error value nameEq keyEq child parent actor childFiber actorFiber source) ->
  (seen : Bool) -> (0 equation : retired actorFiber = seen) ->
  targetFiber {name} {key} {value} {world} {error} @{nameEq} @{keyEq} actorFiber
    (replaceBinding @{nameEq} child (retireFiber childFiber) source) =
  targetFiber {name} {key} {value} {world} {error} @{nameEq} @{keyEq} actorFiber source
retirementTargetAtFlag nameEq keyEq child parent actor childFiber actorFiber source frame False equation =
  rewrite equation in sym (fst (retirementFrameResolverSame nameEq keyEq child parent actor childFiber actorFiber source frame))
retirementTargetAtFlag nameEq keyEq child parent actor childFiber actorFiber source frame True equation =
  rewrite equation in Refl

||| Actual frame producer for native target equality, no equality oracle.
export
0 retirementTargetSame :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child, parent, actor : name) ->
  (childFiber, actorFiber : Fiber name key value world error) ->
  (source : Registry name key value world error) ->
  (frame : RetirementProviderFrame name key world error value nameEq keyEq child parent actor childFiber actorFiber source) ->
  targetFiber {name} {key} {value} {world} {error} @{nameEq} @{keyEq} actorFiber
    (replaceBinding @{nameEq} child (retireFiber childFiber) source) =
  targetFiber {name} {key} {value} {world} {error} @{nameEq} @{keyEq} actorFiber source
retirementTargetSame nameEq keyEq child parent actor childFiber actorFiber source frame =
  retirementTargetAtFlag nameEq keyEq child parent actor childFiber actorFiber source frame (retired actorFiber) Refl

||| Precise ALL-TAG native LAdvance observation equation. TYPE only until
||| the observed elimination helpers supply its producer. The RHS retires
||| the original child at the actual original evaluator result, not a chosen
||| late state, and retains the exact ordered binding snapshot.
public export
RetirementAdvanceEquation :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child, actor : name) ->
  (childFiber : Fiber name key value world error) ->
  (ambient : world) -> (source : Registry name key value world error) -> Type
RetirementAdvanceEquation {name} {key} {world} {error} {value}
  nameEq keyEq child actor childFiber ambient source =
  observeActionResult {name} {key} {world} {error} {value}
    (applyAction @{nameEq} @{keyEq} (LAdvance actor)
      (MkSystemState ambient (replaceBinding @{nameEq} child (retireFiber childFiber) source))) =
  Prelude.map {f = Maybe}
    (\out => (fst out, runtimeSnapshot {name} {key} {value} {world} {error}
      (MkSystemState (worldState (snd out))
        (replaceBinding @{nameEq} child (retireFiber childFiber) (registry (snd out))))))
    (applyAction @{nameEq} @{keyEq} (LAdvance actor) (MkSystemState ambient source))

||| Successful original iterator outcome and True target observation. Only
||| the remaining-list constructor is eliminated; updates commute natively.
export
0 advanceYieldAtRest :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child, parent, actor : name) ->
  (childFiber, actorFiber : Fiber name key value world error) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (frame : RetirementProviderFrame name key world error value nameEq keyEq child parent actor childFiber actorFiber source) ->
  (0 distinct : Not (child = actor)) ->
  (step : (StepEffect key value world error (dependencies (componentDependencies (fiberComponent actorFiber))) (componentProvisions (fiberComponent actorFiber)))) -> (rest : List (StepEffect key value world error (dependencies (componentDependencies (fiberComponent actorFiber))) (componentProvisions (fiberComponent actorFiber)))) ->
  (accumulator : (LocalState key value world (componentProvisions (fiberComponent actorFiber))) -> (LocalState key value world (componentProvisions (fiberComponent actorFiber)))) -> (view : View name (dependencies (componentDependencies (fiberComponent actorFiber)))) ->
  (0 lifeEquation : fiberLifecycle actorFiber = Reloading (step :: rest) accumulator view) ->
  (capability : DepValues key value (dependencies (componentDependencies (fiberComponent actorFiber)))) ->
  (0 capEquation : resolveCommittedValues {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (dependencies (componentDependencies (fiberComponent actorFiber))) view source = Just capability) ->
  (localAfter : (LocalState key value world (componentProvisions (fiberComponent actorFiber)))) -> (undo : (LocalState key value world (componentProvisions (fiberComponent actorFiber))) -> (LocalState key value world (componentProvisions (fiberComponent actorFiber)))) ->
  (0 outcomeEquation : runStepEffect step capability (MkLocalState ambient (restrictOwnedPreservingOrder (componentProvisions (fiberComponent actorFiber)) (ownedValues (fiberTable actorFiber)))) = Right (localAfter, undo)) ->
  (0 matchEquation : targetMatches @{nameEq} (targetFiber {name} {key} {value} {world} {error} @{nameEq} @{keyEq} actorFiber source) view = True) ->
  RetirementAdvanceEquation nameEq keyEq child actor childFiber ambient source
advanceYieldAtRest {name} {key} {world} {error} {value}
  nameEq keyEq child parent actor childFiber actorFiber ambient source frame distinct
  step [] accumulator view lifeEquation capability capEquation localAfter undo outcomeEquation matchEquation =
  rewrite lookupReplaceOther {key = name} {value = FiberAt name key value world error} @{nameEq}
    actor child (\same => distinct (sym same)) (retireFiber childFiber) source in
  rewrite frameActorFound frame in
  rewrite lifeEquation in
  rewrite resolveCommittedValuesRetireRegistry {name} {key} {value} {world} {error} nameEq keyEq (dependencies (componentDependencies (fiberComponent actorFiber))) view
    child childFiber source (frameChildFound frame) in
  rewrite capEquation in
  rewrite outcomeEquation in
  rewrite retirementTargetSame nameEq keyEq child parent actor childFiber actorFiber source frame in
  rewrite matchEquation in
  cong (\snapshot => Just (LFinishTag, snapshot))
    (retirementUpdateSnapshot nameEq child actor childFiber
      (setFiberRuntime actorFiber (localTable localAfter) (Active (pushLocalUndo @{keyEq} (componentProvisions (fiberComponent actorFiber)) accumulator undo) view)) (localWorld localAfter) source distinct)
advanceYieldAtRest {name} {key} {world} {error} {value}
  nameEq keyEq child parent actor childFiber actorFiber ambient source frame distinct
  step (next :: later) accumulator view lifeEquation capability capEquation localAfter undo outcomeEquation matchEquation =
  rewrite lookupReplaceOther {key = name} {value = FiberAt name key value world error} @{nameEq}
    actor child (\same => distinct (sym same)) (retireFiber childFiber) source in
  rewrite frameActorFound frame in
  rewrite lifeEquation in
  rewrite resolveCommittedValuesRetireRegistry {name} {key} {value} {world} {error} nameEq keyEq (dependencies (componentDependencies (fiberComponent actorFiber))) view
    child childFiber source (frameChildFound frame) in
  rewrite capEquation in
  rewrite outcomeEquation in
  rewrite retirementTargetSame nameEq keyEq child parent actor childFiber actorFiber source frame in
  rewrite matchEquation in
  cong (\snapshot => Just (LIterTag, snapshot))
    (retirementUpdateSnapshot nameEq child actor childFiber
      (setFiberRuntime actorFiber (localTable localAfter) (Reloading (next :: later) (pushLocalUndo @{keyEq} (componentProvisions (fiberComponent actorFiber)) accumulator undo) view)) (localWorld localAfter) source distinct)
