module DGamma.CP5O19AdvanceObservationSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP4DeletionFrameCore
import DGamma.CP4ProgressPotential
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5O19OpeningPropagationSpike
import DGamma.CP5O19ActualCommutedDomainSpike
import DGamma.CP5O19CommutedDomainSpike
import DGamma.CP5RankedEarlyApplicabilitySpike
import Data.List
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Captured-map rebasing from EXPLICIT equal owner observations. The source
||| states may differ in ambient state and every foreign fiber. This observes
||| the primitive map, not a nested existential replay/diamond builder.
export
0 o19AdvanceCapturedMapAt :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (earlier, later : SystemState name key value world error) ->
  (fiber : Fiber name key value world error) -> (tag : RuleTag) ->
  (lookupFiber @{nameEq} actor (registry earlier) = Just fiber) ->
  (lookupFiber @{nameEq} actor (registry later) = Just fiber) ->
  (state : EffectState name key value world) ->
  partialEffectMapFor nameEq keyEq (LAdvance actor) tag earlier state =
  partialEffectMapFor nameEq keyEq (LAdvance actor) tag later state
o19AdvanceCapturedMapAt nameEq keyEq actor earlier later fiber OInsertTag foundEarly foundLate state = Refl
o19AdvanceCapturedMapAt nameEq keyEq actor earlier later fiber ORetireTag foundEarly foundLate state = Refl
o19AdvanceCapturedMapAt nameEq keyEq actor earlier later fiber ORemoveTag foundEarly foundLate state = Refl
o19AdvanceCapturedMapAt nameEq keyEq actor earlier later fiber LBeginTag foundEarly foundLate state = Refl
o19AdvanceCapturedMapAt nameEq keyEq actor earlier later fiber LIterTag foundEarly foundLate state =
  rewrite foundEarly in rewrite foundLate in Refl
o19AdvanceCapturedMapAt nameEq keyEq actor earlier later fiber LFinishTag foundEarly foundLate state =
  rewrite foundEarly in rewrite foundLate in Refl
o19AdvanceCapturedMapAt nameEq keyEq actor earlier later fiber LDivertTag foundEarly foundLate state =
  rewrite foundEarly in rewrite foundLate in Refl
o19AdvanceCapturedMapAt nameEq keyEq actor earlier later fiber LRaiseTag foundEarly foundLate state = Refl
o19AdvanceCapturedMapAt nameEq keyEq actor earlier later fiber LLeaveTag foundEarly foundLate state = Refl
o19AdvanceCapturedMapAt nameEq keyEq actor earlier later fiber LUnloadTag foundEarly foundLate state = Refl

||| Transport only the EXPLICIT resolver observation of a concrete fiber.
||| Retirement is eliminated as an actual Boolean argument; no opaque target
||| or early applicability certificate is supplied by a caller.
export
0 o19ObservedTargetRebase :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (retiredFlag : Bool) -> (table : OwnedTable key value (componentProvisions component)) ->
  (lifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies component)) (componentProvisions component)) ->
  (earlier, later : Registry name key value world error) ->
  (observed : Maybe (View name (dependencies (componentDependencies component)))) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (dependencies (componentDependencies component)) earlier = observed) ->
  (resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (dependencies (componentDependencies component)) later = observed) ->
  (targetFiber @{nameEq} @{keyEq} (MkFiber component parent retiredFlag table lifecycle) later = Just view) ->
  (targetFiber @{nameEq} @{keyEq} (MkFiber component parent retiredFlag table lifecycle) earlier = Just view)
o19ObservedTargetRebase nameEq keyEq component parent False table lifecycle earlier later
  observed view earlyResolution lateResolution target =
    trans earlyResolution (trans (sym lateResolution) target)
o19ObservedTargetRebase nameEq keyEq component parent True table lifecycle earlier later
  observed view earlyResolution lateResolution target = void (nothingIsNotJust target)

||| Actual successful step output, retaining its own inverse and local state.
||| This observation authenticates the primitive callback, not a control guard.
public export
record O19StepObservation (key, world, error : Type) (value : key -> Type)
  (deps : List key) (provision : CoeffectSpec key)
  (step : StepEffect key value world error deps provision)
  (capability : DepValues key value deps)
  (localBefore : LocalState key value world provision) where
  constructor MkO19StepObservation
  stepObservedAfter : LocalState key value world provision
  stepObservedUndo : LocalState key value world provision -> LocalState key value world provision
  0 stepObservedRan : runStepEffect step capability localBefore = Right (stepObservedAfter, stepObservedUndo)

||| Decode an EXPLICIT callback result using partial-map definedness. A failed
||| callback contradicts that domain; no successful callback is an input.
export
0 o19StepSuccessObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {deps : List key} -> {provision : CoeffectSpec key} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (step : StepEffect key value world error deps provision) ->
  (capability : DepValues key value deps) -> (state : EffectState name key value world) ->
  (observed : Either error (LocalState key value world provision,
    LocalState key value world provision -> LocalState key value world provision)) ->
  (runStepEffect step capability (MkLocalState (effectAmbient state)
    (restrictOwnedPreservingOrder @{keyEq} provision (effectTables state actor))) = observed) ->
  (isJust (stepForwardEffectMap nameEq keyEq actor step capability state) = True) ->
  O19StepObservation key world error value deps provision step capability
    (MkLocalState (effectAmbient state) (restrictOwnedPreservingOrder @{keyEq} provision (effectTables state actor)))
o19StepSuccessObserved nameEq keyEq actor step capability state (Left failure) exact defined =
  case trans (sym (cong isJust
    (the (stepForwardEffectMap nameEq keyEq actor step capability state = Nothing)
      (rewrite exact in Refl)))) defined of
    Refl impossible
o19StepSuccessObserved nameEq keyEq actor step capability state (Right (localAfter, undo)) exact defined =
  MkO19StepObservation localAfter undo exact

||| Decode the ACTUAL captured capability map first, then the callback. Both
||| observations come from ordinary evaluator arguments; no computed dependent
||| result is scrutinized locally and no checked early edge is assumed.
export
0 o19AdvanceValuesObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (component : Component key value world error) -> (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (step : StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component)) ->
  (rest : List (StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component))) ->
  (accumulator : LocalState key value world (componentProvisions component) -> LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (state : EffectState name key value world) ->
  (observed : Maybe (DepValues key value (dependencies (componentDependencies component)))) ->
  (resolveEffectValues @{keyEq} (dependencies (componentDependencies component)) view state = observed) ->
  (isJust (fiberAdvanceRuntimeEffectMap nameEq keyEq actor
    (MkFiber component parent retiredFlag table (Reloading (step :: rest) accumulator view)) state) = True) ->
  (capability : DepValues key value (dependencies (componentDependencies component)) **
    (resolveEffectValues @{keyEq} (dependencies (componentDependencies component)) view state = Just capability,
     O19StepObservation key world error value (dependencies (componentDependencies component))
       (componentProvisions component) step capability
       (MkLocalState (effectAmbient state) (restrictOwnedPreservingOrder @{keyEq} (componentProvisions component) (effectTables state actor)))))
o19AdvanceValuesObserved nameEq keyEq actor component parent retiredFlag table step rest accumulator view state Nothing exact defined =
  case trans (sym (cong isJust
    (the (fiberAdvanceRuntimeEffectMap nameEq keyEq actor
      (MkFiber component parent retiredFlag table (Reloading (step :: rest) accumulator view)) state = Nothing)
      (rewrite exact in Refl)))) defined of
    Refl impossible
o19AdvanceValuesObserved nameEq keyEq actor component parent retiredFlag table step rest accumulator view state (Just capability) exact defined =
  (capability ** (exact,
    o19StepSuccessObserved nameEq keyEq actor step capability state
      (runStepEffect step capability (MkLocalState (effectAmbient state)
        (restrictOwnedPreservingOrder @{keyEq} (componentProvisions component) (effectTables state actor)))) Refl
      (trans (sym (cong isJust
        (the (fiberAdvanceRuntimeEffectMap nameEq keyEq actor
          (MkFiber component parent retiredFlag table (Reloading (step :: rest) accumulator view)) state =
          stepForwardEffectMap nameEq keyEq actor step capability state)
          (rewrite exact in Refl)))) defined)))

||| Rebase the EXPLICIT capability/callback output onto the raw evaluator's
||| actual committed resolver and owned-table normalization. The two existing
||| projection lemmas do the transport; no proof irrelevance is involved.
export
0 o19AdvanceValuesAtSource :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (before : SystemState name key value world error) ->
  (component : Component key value world error) -> (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (step : StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component)) ->
  (rest : List (StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component))) ->
  (accumulator : LocalState key value world (componentProvisions component) -> LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (lookupFiber @{nameEq} actor (registry before) = Just (MkFiber component parent retiredFlag table (Reloading (step :: rest) accumulator view))) ->
  (observed : (capability : DepValues key value (dependencies (componentDependencies component)) **
    (resolveEffectValues @{keyEq} (dependencies (componentDependencies component)) view (projectEffectState @{nameEq} before) = Just capability,
     O19StepObservation key world error value (dependencies (componentDependencies component)) (componentProvisions component) step capability
       (MkLocalState (effectAmbient (projectEffectState @{nameEq} before))
         (restrictOwnedPreservingOrder @{keyEq} (componentProvisions component) (effectTables (projectEffectState @{nameEq} before) actor)))))) ->
  (capability : DepValues key value (dependencies (componentDependencies component)) **
    (resolveCommittedValues {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (dependencies (componentDependencies component)) view (registry before) = Just capability,
     O19StepObservation key world error value (dependencies (componentDependencies component)) (componentProvisions component) step capability
       (MkLocalState (worldState before) (restrictOwnedPreservingOrder @{keyEq} (componentProvisions component) (ownedValues table)))))
o19AdvanceValuesAtSource nameEq keyEq actor (MkSystemState ambient fibers) component parent retiredFlag table step rest accumulator view found
  (capability ** (resolved, ran)) =
    (capability **
      (trans (sym (resolveEffectValuesProjected nameEq keyEq (dependencies (componentDependencies component)) view (MkSystemState ambient fibers))) resolved,
       rewrite sym (projectedActorTable nameEq actor (MkSystemState ambient fibers)
         (MkFiber component parent retiredFlag table (Reloading (step :: rest) accumulator view)) found) in ran))

||| Empty Finish has no callback but still needs the actual target guard.
export
0 o19FinishEmptyAtObservedTarget :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (component : Component key value world error) -> (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (accumulator : LocalState key value world (componentProvisions component) -> LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (lookupFiber @{nameEq} actor fibers = Just (MkFiber component parent retiredFlag table (Reloading [] accumulator view))) ->
  (targetFiber @{nameEq} @{keyEq} (MkFiber component parent retiredFlag table (Reloading [] accumulator view)) fibers = Just view) ->
  RawActivationMove {name} {key} {value} {world} {error} nameEq keyEq (LAdvance actor) LFinishTag (MkSystemState ambient fibers)
o19FinishEmptyAtObservedTarget nameEq keyEq actor ambient fibers component parent retiredFlag table accumulator view found target =
  MkRawActivationMove
    (MkSystemState ambient (replaceBinding @{nameEq} actor (MkFiber component parent retiredFlag table (Active accumulator view)) fibers))
    (rewrite found in rewrite target in
      rewrite trans (viewEqSameNameList nameEq view view) (sameNameListReflexive nameEq (DGamma.Calculus.viewProviders view)) in Refl)

||| The actual remaining-list constructor selects Iter versus Finish. This
||| consumes D8's EXPLICIT output once and builds the real raw control edge.
export
0 o19AdvanceAtObservedValues :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (component : Component key value world error) -> (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (step : StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component)) ->
  (rest : List (StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component))) ->
  (accumulator : LocalState key value world (componentProvisions component) -> LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (lookupFiber @{nameEq} actor fibers = Just (MkFiber component parent retiredFlag table (Reloading (step :: rest) accumulator view))) ->
  (targetFiber @{nameEq} @{keyEq} (MkFiber component parent retiredFlag table (Reloading (step :: rest) accumulator view)) fibers = Just view) ->
  (observed : (capability : DepValues key value (dependencies (componentDependencies component)) **
    (resolveCommittedValues {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (dependencies (componentDependencies component)) view fibers = Just capability,
     O19StepObservation key world error value (dependencies (componentDependencies component)) (componentProvisions component) step capability
       (MkLocalState ambient (restrictOwnedPreservingOrder @{keyEq} (componentProvisions component) (ownedValues table)))))) ->
  RawActivationMove {name} {key} {value} {world} {error} nameEq keyEq (LAdvance actor)
    (case rest of [] => LFinishTag; _ => LIterTag) (MkSystemState ambient fibers)
o19AdvanceAtObservedValues nameEq keyEq actor ambient fibers component parent retiredFlag table step [] accumulator view found target
  (capability ** (resolved, MkO19StepObservation localAfter undo ran)) =
    MkRawActivationMove
      (MkSystemState (localWorld localAfter) (replaceBinding @{nameEq} actor
        (MkFiber component parent retiredFlag (localTable localAfter)
          (Active (pushLocalUndo (componentProvisions component) accumulator undo) view)) fibers))
      (rewrite found in rewrite resolved in rewrite ran in rewrite target in
        rewrite trans (viewEqSameNameList nameEq view view) (sameNameListReflexive nameEq (DGamma.Calculus.viewProviders view)) in Refl)
o19AdvanceAtObservedValues nameEq keyEq actor ambient fibers component parent retiredFlag table step (next :: more) accumulator view found target
  (capability ** (resolved, MkO19StepObservation localAfter undo ran)) =
    MkRawActivationMove
      (MkSystemState (localWorld localAfter) (replaceBinding @{nameEq} actor
        (MkFiber component parent retiredFlag (localTable localAfter)
          (Reloading (next :: more) (pushLocalUndo (componentProvisions component) accumulator undo) view)) fibers))
      (rewrite found in rewrite resolved in rewrite ran in rewrite target in
        rewrite trans (viewEqSameNameList nameEq view view) (sameNameListReflexive nameEq (DGamma.Calculus.viewProviders view)) in Refl)

||| Whole nonempty reconstruction from a CAPTURED MAP DOMAIN, deriving both
||| capability and successful callback internally before constructing control.
export
0 o19AdvanceAtCapturedDomain :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (fibers : Registry name key value world error) ->
  (component : Component key value world error) -> (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (step : StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component)) ->
  (rest : List (StepEffect key value world error (dependencies (componentDependencies component)) (componentProvisions component))) ->
  (accumulator : LocalState key value world (componentProvisions component) -> LocalState key value world (componentProvisions component)) ->
  (view : View name (dependencies (componentDependencies component))) ->
  (lookupFiber @{nameEq} actor fibers = Just (MkFiber component parent retiredFlag table (Reloading (step :: rest) accumulator view))) ->
  (targetFiber @{nameEq} @{keyEq} (MkFiber component parent retiredFlag table (Reloading (step :: rest) accumulator view)) fibers = Just view) ->
  (isJust (fiberAdvanceRuntimeEffectMap nameEq keyEq actor
    (MkFiber component parent retiredFlag table (Reloading (step :: rest) accumulator view))
    (projectEffectState @{nameEq} (the (SystemState name key value world error) (MkSystemState ambient fibers)))) = True) ->
  RawActivationMove {name} {key} {value} {world} {error} nameEq keyEq (LAdvance actor)
    (case rest of [] => LFinishTag; _ => LIterTag) (MkSystemState ambient fibers)
o19AdvanceAtCapturedDomain nameEq keyEq actor ambient fibers component parent retiredFlag table step rest accumulator view found target defined =
  o19AdvanceAtObservedValues nameEq keyEq actor ambient fibers component parent retiredFlag table step rest accumulator view found target
    (o19AdvanceValuesAtSource nameEq keyEq actor (MkSystemState ambient fibers) component parent retiredFlag table step rest accumulator view found
      (o19AdvanceValuesObserved nameEq keyEq actor component parent retiredFlag table step rest accumulator view
        (projectEffectState @{nameEq} (the (SystemState name key value world error) (MkSystemState ambient fibers)))
        (resolveEffectValues @{keyEq} (dependencies (componentDependencies component)) view
          (projectEffectState @{nameEq} (the (SystemState name key value world error) (MkSystemState ambient fibers)))) Refl defined))

||| Reconstruct right Advance from its ACTUAL later source and captured-map
||| domain, plus explicit shared resolver values and owner lookup framing.
||| Shared resolution for ALL lists fits insertion cuts; it is not claimed
||| for arbitrary activation cuts whose unrelated targets may genuinely grow.
export
0 o19AdvanceBeforeObservedCut :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (early, late : SystemState name key value world error) -> (tag : RuleTag) ->
  (observed : (deps : List key) -> Maybe (View name deps)) ->
  ((deps : List key) -> resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq} deps (registry early) = observed deps) ->
  ((deps : List key) -> resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq} deps (registry late) = observed deps) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor (registry early) = lookupFiber @{nameEq} actor (registry late)) ->
  PaperAdvanceSource name key world error value nameEq keyEq actor tag late ->
  (isJust (partialEffectMapFor nameEq keyEq (LAdvance actor) tag late (projectEffectState @{nameEq} early)) = True) ->
  RawActivationMove {name} {key} {value} {world} {error} nameEq keyEq (LAdvance actor) tag early
o19AdvanceBeforeObservedCut nameEq keyEq actor (MkSystemState ambient fibers) _ _ observed earlyResolution lateResolution sameLookup
  (AdvanceSourceFinishEmpty {ambient = lateWorld} {fibers = lateFibers} {component} {parent} {retiredFlag} {table} {accumulator} {view} Refl found target) defined =
    o19FinishEmptyAtObservedTarget nameEq keyEq actor ambient fibers component parent retiredFlag table accumulator view
      (trans sameLookup found)
      (o19ObservedTargetRebase nameEq keyEq component parent retiredFlag table (Reloading [] accumulator view) fibers lateFibers
        (observed (dependencies (componentDependencies component))) view
        (earlyResolution (dependencies (componentDependencies component))) (lateResolution (dependencies (componentDependencies component))) target)
o19AdvanceBeforeObservedCut nameEq keyEq actor (MkSystemState ambient fibers) _ _ observed earlyResolution lateResolution sameLookup
  (AdvanceSourceFinishOne {ambient = lateWorld} {fibers = lateFibers} {component} {parent} {retiredFlag} {table} {step} {accumulator} {view} Refl found target) defined =
    o19AdvanceAtCapturedDomain nameEq keyEq actor ambient fibers component parent retiredFlag table step [] accumulator view
      (trans sameLookup found)
      (o19ObservedTargetRebase nameEq keyEq component parent retiredFlag table (Reloading [step] accumulator view) fibers lateFibers
        (observed (dependencies (componentDependencies component))) view
        (earlyResolution (dependencies (componentDependencies component))) (lateResolution (dependencies (componentDependencies component))) target)
      (trans (sym (cong isJust
        (the (partialEffectMapFor nameEq keyEq (LAdvance actor) LFinishTag (the (SystemState name key value world error) (MkSystemState lateWorld lateFibers))
          (projectEffectState @{nameEq} (the (SystemState name key value world error) (MkSystemState ambient fibers))) =
          fiberAdvanceRuntimeEffectMap nameEq keyEq actor (MkFiber component parent retiredFlag table (Reloading [step] accumulator view))
            (projectEffectState @{nameEq} (the (SystemState name key value world error) (MkSystemState ambient fibers))))
          (rewrite found in Refl)))) defined)
o19AdvanceBeforeObservedCut nameEq keyEq actor (MkSystemState ambient fibers) _ _ observed earlyResolution lateResolution sameLookup
  (AdvanceSourceIter {ambient = lateWorld} {fibers = lateFibers} {component} {parent} {retiredFlag} {table} {step} {next} {more} {accumulator} {view} Refl found target) defined =
    o19AdvanceAtCapturedDomain nameEq keyEq actor ambient fibers component parent retiredFlag table step (next :: more) accumulator view
      (trans sameLookup found)
      (o19ObservedTargetRebase nameEq keyEq component parent retiredFlag table (Reloading (step :: next :: more) accumulator view) fibers lateFibers
        (observed (dependencies (componentDependencies component))) view
        (earlyResolution (dependencies (componentDependencies component))) (lateResolution (dependencies (componentDependencies component))) target)
      (trans (sym (cong isJust
        (the (partialEffectMapFor nameEq keyEq (LAdvance actor) LIterTag (the (SystemState name key value world error) (MkSystemState lateWorld lateFibers))
          (projectEffectState @{nameEq} (the (SystemState name key value world error) (MkSystemState ambient fibers))) =
          fiberAdvanceRuntimeEffectMap nameEq keyEq actor (MkFiber component parent retiredFlag table (Reloading (step :: next :: more) accumulator view))
            (projectEffectState @{nameEq} (the (SystemState name key value world error) (MkSystemState ambient fibers))))
          (rewrite found in Refl)))) defined)

||| Actual source edges/independence now produce a CHECKED earlier Advance.
||| Captured-domain commutation, owner framing, control/tag source inversion,
||| capability/callback extraction and preservation all run in this pipeline.
||| Only the explicit shared resolver observations remain cut-specific inputs.
export
0 o19AdvanceBeforeActualObservedPair :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (first, middle, finalState : SystemState name key value world error) ->
  (leftAction : Action name key value world error) -> (leftTag, rightTag : RuleTag) ->
  (leftChecked : checkedApplyAction @{nameEq} @{keyEq} leftAction first = Just (leftTag, middle)) ->
  (rightChecked : checkedApplyAction @{nameEq} @{keyEq} (LAdvance actor) middle = Just (rightTag, finalState)) ->
  Either (rightTag = LIterTag) (rightTag = LFinishTag) ->
  Not (actionOwner leftAction = actor) ->
  TraceIndependent name key world error value keyEq
    (MoreTransitions (Fired {before = first} {afterState = middle} nameEq keyEq leftAction leftTag leftChecked)
      (MoreTransitions (Fired {before = middle} {afterState = finalState} nameEq keyEq (LAdvance actor) rightTag rightChecked) NoTransitions)) ->
  (observed : (deps : List key) -> Maybe (View name deps)) ->
  ((deps : List key) -> resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq} deps (registry first) = observed deps) ->
  ((deps : List key) -> resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq} deps (registry middle) = observed deps) ->
  (registryWellFormed {name} {key} {value} {world} {error} @{nameEq} @{keyEq} first = True) ->
  CheckedEarlyApplication name key world error value nameEq keyEq first (LAdvance actor) rightTag
o19AdvanceBeforeActualObservedPair nameEq keyEq actor first middle finalState leftAction leftTag rightTag leftChecked rightChecked
  rightPaper distinct independent observed earlyResolution lateResolution wellFormed =
    o19CheckObservedRawMove nameEq keyEq (LAdvance actor) rightTag first wellFormed
      (o19AdvanceBeforeObservedCut nameEq keyEq actor first middle rightTag observed earlyResolution lateResolution
        (sym (systemLocalUpdateForeign nameEq actor (actionOwner leftAction) (\same => distinct (sym same)) first middle
          (applyActionLocalUpdate nameEq keyEq leftAction first middle leftTag
            (checkedActionProjects nameEq keyEq leftAction first middle leftTag leftChecked))))
        (paperAdvanceSource nameEq keyEq actor rightTag
          (checkedActionProjects nameEq keyEq (LAdvance actor) middle finalState rightTag rightChecked) rightPaper)
        (cong isJust (partialRunChecked
          (o19ActualPairEarlyPartialRun nameEq keyEq leftAction (LAdvance actor) leftTag rightTag leftChecked rightChecked distinct independent))))
