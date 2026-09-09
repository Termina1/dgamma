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

||| Consume the explicitly observed native target Bool after a successful
||| yield. False is LDivert; True delegates to the checked remaining-list step.
export
0 advanceYieldAtMatch :
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
  (seen : Bool) -> (0 matchEquation : targetMatches @{nameEq} (targetFiber {name} {key} {value} {world} {error} @{nameEq} @{keyEq} actorFiber source) view = seen) ->
  RetirementAdvanceEquation nameEq keyEq child actor childFiber ambient source
advanceYieldAtMatch {name} {key} {world} {error} {value}
  nameEq keyEq child parent actor childFiber actorFiber ambient source frame distinct
  step rest accumulator view lifeEquation capability capEquation localAfter undo outcomeEquation False matchEquation =
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
  cong (\snapshot => Just (LDivertTag, snapshot))
    (retirementUpdateSnapshot nameEq child actor childFiber
      (setFiberRuntime actorFiber (localTable localAfter) (Unloading (pushLocalUndo @{keyEq} (componentProvisions (fiberComponent actorFiber)) accumulator undo) view Nothing)) (localWorld localAfter) source distinct)
advanceYieldAtMatch {name} {key} {world} {error} {value}
  nameEq keyEq child parent actor childFiber actorFiber ambient source frame distinct
  step rest accumulator view lifeEquation capability capEquation localAfter undo outcomeEquation True matchEquation =
  advanceYieldAtRest nameEq keyEq child parent actor childFiber actorFiber ambient source frame distinct step rest accumulator view lifeEquation capability capEquation localAfter undo outcomeEquation matchEquation

||| Empty-program native Finish/Divert observation, with the Bool explicitly
||| supplied at its own equation. No iterator outcome or late edge is assumed.
export
0 advanceEmptyAtMatch :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child, parent, actor : name) ->
  (childFiber, actorFiber : Fiber name key value world error) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (frame : RetirementProviderFrame name key world error value nameEq keyEq child parent actor childFiber actorFiber source) ->
  (0 distinct : Not (child = actor)) ->
  (accumulator : (LocalState key value world (componentProvisions (fiberComponent actorFiber))) -> (LocalState key value world (componentProvisions (fiberComponent actorFiber)))) -> (view : View name (dependencies (componentDependencies (fiberComponent actorFiber)))) ->
  (0 lifeEquation : fiberLifecycle actorFiber = Reloading [] accumulator view) ->
  (seen : Bool) -> (0 matchEquation : targetMatches @{nameEq} (targetFiber {name} {key} {value} {world} {error} @{nameEq} @{keyEq} actorFiber source) view = seen) ->
  RetirementAdvanceEquation nameEq keyEq child actor childFiber ambient source
advanceEmptyAtMatch {name} {key} {world} {error} {value}
  nameEq keyEq child parent actor childFiber actorFiber ambient source frame distinct
  accumulator view lifeEquation False matchEquation =
  rewrite lookupReplaceOther {key = name} {value = FiberAt name key value world error} @{nameEq}
    actor child (\same => distinct (sym same)) (retireFiber childFiber) source in
  rewrite frameActorFound frame in
  rewrite lifeEquation in
  rewrite retirementTargetSame nameEq keyEq child parent actor childFiber actorFiber source frame in
  rewrite matchEquation in
  cong (\snapshot => Just (LDivertTag, snapshot))
    (retirementUpdateSnapshot nameEq child actor childFiber
      (setFiberLifecycle actorFiber (Unloading accumulator view Nothing)) ambient source distinct)
advanceEmptyAtMatch {name} {key} {world} {error} {value}
  nameEq keyEq child parent actor childFiber actorFiber ambient source frame distinct
  accumulator view lifeEquation True matchEquation =
  rewrite lookupReplaceOther {key = name} {value = FiberAt name key value world error} @{nameEq}
    actor child (\same => distinct (sym same)) (retireFiber childFiber) source in
  rewrite frameActorFound frame in
  rewrite lifeEquation in
  rewrite retirementTargetSame nameEq keyEq child parent actor childFiber actorFiber source frame in
  rewrite matchEquation in
  cong (\snapshot => Just (LFinishTag, snapshot))
    (retirementUpdateSnapshot nameEq child actor childFiber
      (setFiberLifecycle actorFiber (Active accumulator view)) ambient source distinct)

||| Split ONLY the already observed yielded pair, then observe the native
||| target-match Bool at its actual call site. No inferred local view.
export
0 advanceAtYield :
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
  (yielded : ((LocalState key value world (componentProvisions (fiberComponent actorFiber))), (LocalState key value world (componentProvisions (fiberComponent actorFiber))) -> (LocalState key value world (componentProvisions (fiberComponent actorFiber))))) ->
  (0 outcomeEquation : runStepEffect step capability (MkLocalState ambient (restrictOwnedPreservingOrder (componentProvisions (fiberComponent actorFiber)) (ownedValues (fiberTable actorFiber)))) = Right yielded) ->
  RetirementAdvanceEquation nameEq keyEq child actor childFiber ambient source
advanceAtYield {name} {key} {world} {error} {value}
  nameEq keyEq child parent actor childFiber actorFiber ambient source frame distinct
  step rest accumulator view lifeEquation capability capEquation (localAfter, undo) outcomeEquation =
  advanceYieldAtMatch nameEq keyEq child parent actor childFiber actorFiber ambient source frame distinct
    step rest accumulator view lifeEquation capability capEquation localAfter undo outcomeEquation
    (targetMatches @{nameEq} (targetFiber {name} {key} {value} {world} {error} @{nameEq} @{keyEq} actorFiber source) view) Refl

||| Eliminate the observed native iterator Either once. Failure reproduces
||| LRaise; success uses a separate yielded-pair consumer.
export
0 advanceAtOutcome :
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
  (outcome : Either error ((LocalState key value world (componentProvisions (fiberComponent actorFiber))), (LocalState key value world (componentProvisions (fiberComponent actorFiber))) -> (LocalState key value world (componentProvisions (fiberComponent actorFiber))))) ->
  (0 outcomeEquation : runStepEffect step capability (MkLocalState ambient (restrictOwnedPreservingOrder (componentProvisions (fiberComponent actorFiber)) (ownedValues (fiberTable actorFiber)))) = outcome) ->
  RetirementAdvanceEquation nameEq keyEq child actor childFiber ambient source
advanceAtOutcome {name} {key} {world} {error} {value}
  nameEq keyEq child parent actor childFiber actorFiber ambient source frame distinct
  step rest accumulator view lifeEquation capability capEquation (Left failure) outcomeEquation =
  rewrite lookupReplaceOther {key = name} {value = FiberAt name key value world error} @{nameEq}
    actor child (\same => distinct (sym same)) (retireFiber childFiber) source in
  rewrite frameActorFound frame in
  rewrite lifeEquation in
  rewrite resolveCommittedValuesRetireRegistry {name} {key} {value} {world} {error} nameEq keyEq (dependencies (componentDependencies (fiberComponent actorFiber))) view
    child childFiber source (frameChildFound frame) in
  rewrite capEquation in
  rewrite outcomeEquation in
  cong (\snapshot => Just (LRaiseTag, snapshot))
    (retirementUpdateSnapshot nameEq child actor childFiber
      (setFiberLifecycle actorFiber (Unloading accumulator view (Just failure))) ambient source distinct)
advanceAtOutcome {name} {key} {world} {error} {value}
  nameEq keyEq child parent actor childFiber actorFiber ambient source frame distinct
  step rest accumulator view lifeEquation capability capEquation (Right yielded) outcomeEquation =
  advanceAtYield nameEq keyEq child parent actor childFiber actorFiber ambient source frame distinct
    step rest accumulator view lifeEquation capability capEquation yielded outcomeEquation

||| Observe the native committed-capability Maybe, whose retirement
||| invariance is the existing Calculus theorem. Nothing remains undefined.
export
0 advanceAtCapability :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child, parent, actor : name) ->
  (childFiber, actorFiber : Fiber name key value world error) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (frame : RetirementProviderFrame name key world error value nameEq keyEq child parent actor childFiber actorFiber source) ->
  (0 distinct : Not (child = actor)) ->
  (step : (StepEffect key value world error (dependencies (componentDependencies (fiberComponent actorFiber))) (componentProvisions (fiberComponent actorFiber)))) -> (rest : List (StepEffect key value world error (dependencies (componentDependencies (fiberComponent actorFiber))) (componentProvisions (fiberComponent actorFiber)))) ->
  (accumulator : (LocalState key value world (componentProvisions (fiberComponent actorFiber))) -> (LocalState key value world (componentProvisions (fiberComponent actorFiber)))) -> (view : View name (dependencies (componentDependencies (fiberComponent actorFiber)))) ->
  (0 lifeEquation : fiberLifecycle actorFiber = Reloading (step :: rest) accumulator view) ->
  (capability : Maybe (DepValues key value (dependencies (componentDependencies (fiberComponent actorFiber))))) ->
  (0 capEquation : resolveCommittedValues {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (dependencies (componentDependencies (fiberComponent actorFiber))) view source = capability) ->
  RetirementAdvanceEquation nameEq keyEq child actor childFiber ambient source
advanceAtCapability {name} {key} {world} {error} {value}
  nameEq keyEq child parent actor childFiber actorFiber ambient source frame distinct
  step rest accumulator view lifeEquation Nothing capEquation =
  rewrite lookupReplaceOther {key = name} {value = FiberAt name key value world error} @{nameEq}
    actor child (\same => distinct (sym same)) (retireFiber childFiber) source in
  rewrite frameActorFound frame in
  rewrite lifeEquation in
  rewrite resolveCommittedValuesRetireRegistry {name} {key} {value} {world} {error} nameEq keyEq (dependencies (componentDependencies (fiberComponent actorFiber))) view
    child childFiber source (frameChildFound frame) in
  rewrite capEquation in
  Refl
advanceAtCapability {name} {key} {world} {error} {value}
  nameEq keyEq child parent actor childFiber actorFiber ambient source frame distinct
  step rest accumulator view lifeEquation (Just capability) capEquation =
  advanceAtOutcome nameEq keyEq child parent actor childFiber actorFiber ambient source frame distinct
    step rest accumulator view lifeEquation capability capEquation
    (runStepEffect step capability (MkLocalState ambient (restrictOwnedPreservingOrder (componentProvisions (fiberComponent actorFiber)) (ownedValues (fiberTable actorFiber))))) Refl

||| Eliminate only the actual reloading program list. Library resolver and
||| target Bool are observed HERE with equations, never reconstructed views.
export
0 advanceAtRemaining :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child, parent, actor : name) ->
  (childFiber, actorFiber : Fiber name key value world error) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (frame : RetirementProviderFrame name key world error value nameEq keyEq child parent actor childFiber actorFiber source) ->
  (0 distinct : Not (child = actor)) ->
  (remaining : List (StepEffect key value world error (dependencies (componentDependencies (fiberComponent actorFiber))) (componentProvisions (fiberComponent actorFiber)))) ->
  (accumulator : (LocalState key value world (componentProvisions (fiberComponent actorFiber))) -> (LocalState key value world (componentProvisions (fiberComponent actorFiber)))) -> (view : View name (dependencies (componentDependencies (fiberComponent actorFiber)))) ->
  (0 lifeEquation : fiberLifecycle actorFiber = Reloading remaining accumulator view) ->
  RetirementAdvanceEquation nameEq keyEq child actor childFiber ambient source
advanceAtRemaining {name} {key} {world} {error} {value}
  nameEq keyEq child parent actor childFiber actorFiber ambient source frame distinct [] accumulator view lifeEquation =
  advanceEmptyAtMatch nameEq keyEq child parent actor childFiber actorFiber ambient source frame distinct accumulator view lifeEquation
    (targetMatches @{nameEq} (targetFiber {name} {key} {value} {world} {error} @{nameEq} @{keyEq} actorFiber source) view) Refl
advanceAtRemaining {name} {key} {world} {error} {value}
  nameEq keyEq child parent actor childFiber actorFiber ambient source frame distinct (step :: rest) accumulator view lifeEquation =
  advanceAtCapability nameEq keyEq child parent actor childFiber actorFiber ambient source frame distinct step rest accumulator view lifeEquation
    (resolveCommittedValues {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (dependencies (componentDependencies (fiberComponent actorFiber))) view source) Refl

||| Single native lifecycle elimination. Non-reloading actions remain
||| undefined on BOTH sides; reloading is handled by the observed pipeline.
export
0 advanceAtLifecycle :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child, parent, actor : name) ->
  (childFiber, actorFiber : Fiber name key value world error) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (frame : RetirementProviderFrame name key world error value nameEq keyEq child parent actor childFiber actorFiber source) ->
  (0 distinct : Not (child = actor)) ->
  (lifecycle : Lifecycle key value world error name (dependencies (componentDependencies (fiberComponent actorFiber))) (componentProvisions (fiberComponent actorFiber))) ->
  (0 lifeEquation : fiberLifecycle actorFiber = lifecycle) ->
  RetirementAdvanceEquation nameEq keyEq child actor childFiber ambient source
advanceAtLifecycle {name} {key} {world} {error} {value}
  nameEq keyEq child parent actor childFiber actorFiber ambient source frame distinct (Inactive outcome) lifeEquation =
  rewrite lookupReplaceOther {key = name} {value = FiberAt name key value world error} @{nameEq}
    actor child (\same => distinct (sym same)) (retireFiber childFiber) source in
  rewrite frameActorFound frame in
  rewrite lifeEquation in
  Refl
advanceAtLifecycle {name} {key} {world} {error} {value}
  nameEq keyEq child parent actor childFiber actorFiber ambient source frame distinct (Active accumulator view) lifeEquation =
  rewrite lookupReplaceOther {key = name} {value = FiberAt name key value world error} @{nameEq}
    actor child (\same => distinct (sym same)) (retireFiber childFiber) source in
  rewrite frameActorFound frame in
  rewrite lifeEquation in
  Refl
advanceAtLifecycle {name} {key} {world} {error} {value}
  nameEq keyEq child parent actor childFiber actorFiber ambient source frame distinct (Unloading accumulator view outcome) lifeEquation =
  rewrite lookupReplaceOther {key = name} {value = FiberAt name key value world error} @{nameEq}
    actor child (\same => distinct (sym same)) (retireFiber childFiber) source in
  rewrite frameActorFound frame in
  rewrite lifeEquation in
  Refl
advanceAtLifecycle {name} {key} {world} {error} {value}
  nameEq keyEq child parent actor childFiber actorFiber ambient source frame distinct (Reloading remaining accumulator view) lifeEquation =
  advanceAtRemaining nameEq keyEq child parent actor childFiber actorFiber ambient source frame distinct remaining accumulator view lifeEquation
