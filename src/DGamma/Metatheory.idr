module DGamma.Metatheory

import DGamma.Core
import DGamma.Coeffects
import DGamma.Unified
import DGamma.Calculus
import Decidable.Equality
import Data.List
import Data.Maybe

%default total

public export
parentValid : DecEq name => Parent name -> Registry name key value world error -> Bool
parentValid Root fibers = True
parentValid (ChildOf parent) fibers = isJust (lookupFiber parent fibers)

public export
parentChainSafe : DecEq name => Nat -> List name -> name ->
  Registry name key value world error -> Bool
parentChainSafe Z seen current fibers = False
parentChainSafe (S fuel) seen current fibers = case lookupFiber current fibers of
  Nothing => False
  Just fiber => case fiberParent fiber of
    Root => True
    ChildOf parent => if elemDec parent seen
      then False
      else parentChainSafe fuel (parent :: seen) parent fibers

public export
viewProvidersPresent : DecEq name => Registry name key value world error ->
  View name deps -> Bool
viewProvidersPresent fibers EmptyView = True
viewProvidersPresent fibers (ProviderView provider rest) =
  case lookupFiber provider fibers of
    Nothing => False
    Just fiber => installed (fiberLifecycle fiber) &&
                  viewProvidersPresent fibers rest

||| Definition 58(3–4), strengthened with the key/provider-table connection
||| needed by reachable committed views. The extra connection is established by
||| L-Begin and preserved until guarded L-Unload.
public export
viewBindingsValid : DecEq name => DecEq key => (deps : List key) ->
  View name deps -> Registry name key value world error -> Bool
viewBindingsValid deps view fibers =
  viewProvidersPresent fibers view &&
  isJust (resolveCommittedValues deps view fibers)

public export
fiberViewValid : DecEq name => DecEq key =>
  (fiber : Fiber name key value world error) ->
  Registry name key value world error -> Bool
fiberViewValid (MkFiber component parent retired table lifecycle) fibers =
  case lifecycle of
    Inactive _ => True
    Reloading _ _ view =>
      viewBindingsValid (dependencies (componentDependencies component)) view fibers
    Active _ view =>
      viewBindingsValid (dependencies (componentDependencies component)) view fibers
    Unloading _ view _ =>
      viewBindingsValid (dependencies (componentDependencies component)) view fibers

public export
pairwiseProvisionDisjoint : DecEq key =>
  List (Binding name (FiberAt name key value world error)) -> Bool
pairwiseProvisionDisjoint [] = True
pairwiseProvisionDisjoint (Bind _ fiber :: rest) =
  provisionsDisjointFrom (componentProvisions (fiberComponent fiber)) rest &&
  pairwiseProvisionDisjoint rest

||| Definition 58, executable. Registry/table uniqueness and view totality are
||| intrinsic; the Boolean checks the remaining global obligations.
public export
wellFormed : DecEq name => DecEq key =>
  SystemState name key value world error -> Bool
wellFormed = registryWellFormed

public export
0 justInjective : Just left = Just right -> left = right
justInjective Refl = Refl

public export
0 nothingIsNotJust : Nothing = Just x -> Void
nothingIsNotJust Refl impossible

public export
0 checkedActionProjects :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  checkedApplyAction @{nameEq} @{keyEq} action before = Just (tag, afterState) ->
  applyAction @{nameEq} @{keyEq} action before = Just (tag, afterState)
checkedActionProjects nameEq keyEq action before afterState tag equation
  with (applyAction @{nameEq} @{keyEq} action before) proof raw
  checkedActionProjects nameEq keyEq action before afterState tag equation | Nothing =
    void (nothingIsNotJust equation)
  checkedActionProjects nameEq keyEq action before afterState tag equation |
    Just (rawTag, rawAfter) with (registryWellFormed @{nameEq} @{keyEq} rawAfter)
    checkedActionProjects nameEq keyEq action before afterState tag equation |
      Just (rawTag, rawAfter) | False = void (nothingIsNotJust equation)
    checkedActionProjects nameEq keyEq action before afterState tag equation |
      Just (rawTag, rawAfter) | True =
        case justInjective equation of Refl => Refl

public export
0 checkedActionTargetValid :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  checkedApplyAction @{nameEq} @{keyEq} action before = Just (tag, afterState) ->
  registryWellFormed @{nameEq} @{keyEq} afterState = True
checkedActionTargetValid nameEq keyEq action before afterState tag equation
  with (applyAction @{nameEq} @{keyEq} action before)
  checkedActionTargetValid nameEq keyEq action before afterState tag equation | Nothing =
    void (nothingIsNotJust equation)
  checkedActionTargetValid nameEq keyEq action before afterState tag equation |
    Just (rawTag, rawAfter) with (registryWellFormed @{nameEq} @{keyEq} rawAfter) proof valid
    checkedActionTargetValid nameEq keyEq action before afterState tag equation |
      Just (rawTag, rawAfter) | False = void (nothingIsNotJust equation)
    checkedActionTargetValid nameEq keyEq action before afterState tag equation |
      Just (rawTag, rawAfter) | True =
        case justInjective equation of Refl => valid

public export
0 applyActionDeterministic : (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  (state : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq} action state = Just (leftTag, leftState) ->
  applyAction @{nameEq} @{keyEq} action state = Just (rightTag, rightState) ->
  (leftTag = rightTag, leftState = rightState)
applyActionDeterministic nameEq keyEq action state left right =
  case justInjective (trans (sym left) right) of Refl => (Refl, Refl)

public export
TransitionSourceValid : {before, afterState :
  SystemState name key value world error} -> Transition before afterState -> Type
TransitionSourceValid {before} (Fired nameEq keyEq action tag equation) =
  registryWellFormed @{nameEq} @{keyEq} before = True

public export
TransitionTargetValid : {before, afterState :
  SystemState name key value world error} -> Transition before afterState -> Type
TransitionTargetValid {afterState} (Fired nameEq keyEq action tag equation) =
  registryWellFormed @{nameEq} @{keyEq} afterState = True

||| Theorem 59. The checked LTS admits only evaluator endpoints satisfying the
||| executable Definition-58 invariant.
public export
0 preservationTheorem : (step : Transition before afterState) ->
  TransitionSourceValid step -> TransitionTargetValid step
preservationTheorem (Fired nameEq keyEq action tag equation) valid =
  checkedActionTargetValid nameEq keyEq action _ _ tag equation

||| Rule identity predicates used by episode boundaries.
public export
record BeginStep (nameEq : DecEq name) (keyEq : DecEq key) (n : name)
                 (before, afterState : SystemState name key value world error) where
  constructor MkBeginStep
  beginEquation : checkedApplyAction @{nameEq} @{keyEq} (LBegin n) before =
                  Just (LBeginTag, afterState)

public export
beginTransition : {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {n : name} ->
  {before, afterState : SystemState name key value world error} ->
  BeginStep nameEq keyEq n before afterState -> Transition before afterState
beginTransition {nameEq} {keyEq} {n} opening =
  Fired nameEq keyEq (LBegin n) LBeginTag (beginEquation opening)

public export
record UnloadStep (nameEq : DecEq name) (keyEq : DecEq key) (n : name)
                  (before, afterState : SystemState name key value world error) where
  constructor MkUnloadStep
  unloadEquation : checkedApplyAction @{nameEq} @{keyEq} (LUnload n) before =
                   Just (LUnloadTag, afterState)

public export
unloadTransition : {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {n : name} ->
  {before, afterState : SystemState name key value world error} ->
  UnloadStep nameEq keyEq n before afterState -> Transition before afterState
unloadTransition {nameEq} {keyEq} {n} closing =
  Fired nameEq keyEq (LUnload n) LUnloadTag (unloadEquation closing)

||| Every state in this trace segment, including both endpoints, is installed.
public export
data InstalledTrace : (name, key, world, error : Type) ->
  (value : key -> Type) -> (nameEq : DecEq name) -> (n : name) ->
  {start, end : SystemState name key value world error} ->
  Transitions start end -> Type where
  InstalledEnd : installedAt @{nameEq} n state = True ->
    InstalledTrace name key world error value nameEq n (NoTransitions {state})
  InstalledStep : (transition : Transition first middle) ->
    (rest : Transitions middle finalState) ->
    installedAt @{nameEq} n first = True ->
    InstalledTrace name key world error value nameEq n rest ->
    InstalledTrace name key world error value nameEq n
      (MoreTransitions transition rest)

||| A prefix is anchored at the unique left boundary: the state immediately
||| after L-Begin. It cannot be manufactured from an Active/Unloading suffix.
public export
record EpisodePrefix (name, key, world, error : Type) (value : key -> Type)
                     (nameEq : DecEq name) (keyEq : DecEq key) (n : name)
                     (preStart, current : SystemState name key value world error) where
  constructor MkEpisodePrefix
  episodeStartState : SystemState name key value world error
  opening : BeginStep nameEq keyEq n preStart episodeStartState
  inside : Transitions episodeStartState current
  insideInstalled : InstalledTrace name key world error value nameEq n inside

||| A maximal closed episode has both boundaries: L-Begin on the left and the
||| first L-Unload on the right.
public export
record ClosedEpisode (name, key, world, error : Type) (value : key -> Type)
                     (nameEq : DecEq name) (keyEq : DecEq key) (n : name)
                     (preStart, afterClose : SystemState name key value world error) where
  constructor MkClosedEpisode
  closedStartState : SystemState name key value world error
  lastInstalledState : SystemState name key value world error
  closedOpening : BeginStep nameEq keyEq n preStart closedStartState
  closedInside : Transitions closedStartState lastInstalledState
  closedInsideInstalled : InstalledTrace name key world error value nameEq n closedInside
  closing : UnloadStep nameEq keyEq n lastInstalledState afterClose

public export
closedTransitions : {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {n : name} ->
  {pre, afterState : SystemState name key value world error} ->
  (episode : ClosedEpisode name key world error value nameEq keyEq n pre afterState) ->
  Transitions (closedStartState episode) afterState
closedTransitions episode = appendTransitions (closedInside episode)
  (MoreTransitions (unloadTransition (closing episode)) NoTransitions)

public export
prefixTransitions : {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {n : name} ->
  {pre, current : SystemState name key value world error} ->
  (episode : EpisodePrefix name key world error value nameEq keyEq n pre current) ->
  Transitions (episodeStartState episode) current
prefixTransitions episode = inside episode

||| Partial Table-1 state map. A moved successful iterator may fail, and that
||| remains `Nothing`; it is never silently totalized to identity.
public export
partialWorldMapFor : (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  Action name key value world error -> RuleTag ->
  SystemState name key value world error -> PartialMap world
partialWorldMapFor nameEq keyEq (LAdvance n) tag state world =
  case lookupFiber @{nameEq} n (registry state) of
    Nothing => Nothing
    Just fiber => case fiberLifecycle fiber of
      Reloading [] accumulator view => Just world
      Reloading (step :: rest) accumulator view =>
        case resolveCommittedValues @{nameEq} @{keyEq}
          (dependencies (componentDependencies (fiberComponent fiber)))
          view (registry state) of
          Nothing => Nothing
          Just capability => case runStepEffect step capability
            (MkLocalState world (fiberTable fiber)) of
              Left _ => Nothing
              Right (after, undo) => Just (localWorld after)
      _ => Nothing
partialWorldMapFor nameEq keyEq (LUnload n) tag state world =
  case lookupFiber @{nameEq} n (registry state) of
    Just fiber => case fiberLifecycle fiber of
      Unloading accumulator view outcome =>
        Just (localWorld (accumulator (MkLocalState world (fiberTable fiber))))
      _ => Nothing
    Nothing => Nothing
partialWorldMapFor nameEq keyEq action tag state world = Just world

public export
partialWorldMap : {before, afterState : SystemState name key value world error} ->
  Transition before afterState -> PartialMap world
partialWorldMap {before} (Fired nameEq keyEq action tag equation) =
  partialWorldMapFor nameEq keyEq action tag before

||| Occurrence proof selecting only transformations actually present in a trace.
public export
data OccursIn : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, last : SystemState name key value world error} ->
  {stepBefore, stepAfter : SystemState name key value world error} ->
  Transition stepBefore stepAfter -> Transitions first last -> Type where
  OccursHere : OccursIn transition (MoreTransitions transition rest)
  OccursLater : OccursIn selected rest ->
    OccursIn selected (MoreTransitions transition rest)

||| Non-vacuous Definition-60 hypothesis: only actual transitions at distinct
||| names in this supplied trace are quantified. It is satisfiable on nontrivial
||| worlds and includes partial-map commutation and definedness stability.
public export
record TraceIndependent (name, key, world, error : Type)
                        (value : key -> Type)
                        {first, last : SystemState name key value world error}
                        (trace : Transitions first last) where
  constructor MkTraceIndependent
  0 actualMapsCommute :
    {leftBefore, leftAfter, rightBefore, rightAfter :
      SystemState name key value world error} ->
    (left : Transition leftBefore leftAfter) ->
    (right : Transition rightBefore rightAfter) ->
    OccursIn left trace -> OccursIn right trace ->
    Not (transitionActor left = transitionActor right) ->
    PartialCommute (EqEquivalence {a = world})
      (partialWorldMap left) (partialWorldMap right)
  0 definednessStable :
    {leftBefore, leftAfter, rightBefore, rightAfter :
      SystemState name key value world error} ->
    (left : Transition leftBefore leftAfter) ->
    (right : Transition rightBefore rightAfter) ->
    OccursIn left trace -> OccursIn right trace ->
    Not (transitionActor left = transitionActor right) ->
    (origin, moved, result : world) ->
    partialWorldMap right origin = Just moved ->
    partialWorldMap left origin = Just result ->
    (movedResult : world ** partialWorldMap left moved = Just movedResult)

public export
0 noOccurrenceInEmpty : OccursIn transition NoTransitions -> Void
noOccurrenceInEmpty occurrence impossible

||| Concrete non-vacuity witness: independence of an empty actual trace exists
||| for every ambient world, including Bool and other non-subsingleton types.
public export
emptyTraceIndependent : TraceIndependent name key world error value
  (NoTransitions {state})
emptyTraceIndependent = MkTraceIndependent
  (\left, right, leftOccurs, rightOccurs, distinct =>
    void (noOccurrenceInEmpty leftOccurs))
  (\left, right, leftOccurs, rightOccurs, distinct, origin, moved, result,
    rightDefined, leftDefined => void (noOccurrenceInEmpty leftOccurs))

||| Replay skips the selected actor and propagates foreign failure honestly.
public export
data ForeignReplay : (name, key, world, error : Type) -> (value : key -> Type) ->
  {start, end : SystemState name key value world error} ->
  (selected : name) -> Transitions start end -> world -> world -> Type where
  ReplayDone : ForeignReplay name key world error value selected
                             NoTransitions initial initial
  ReplayOwn : (transition : Transition first middle) ->
    transitionActor transition = selected ->
    ForeignReplay name key world error value selected rest initial final ->
    ForeignReplay name key world error value selected
      (MoreTransitions transition rest) initial final
  ReplayForeign : (transition : Transition first middle) ->
    Not (transitionActor transition = selected) ->
    partialWorldMap transition initial = Just nextWorld ->
    ForeignReplay name key world error value selected rest nextWorld final ->
    ForeignReplay name key world error value selected
      (MoreTransitions transition rest) initial final

||| A trace-specific accumulator/foreign-map hypothesis. Unlike the rejected
||| universal Component quantifier, it mentions only this episode prefix.
public export
record PrefixRecoveryIndependent
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (selected : name)
  {start, current : SystemState name key value world error}
  (trace : Transitions start current) (accumulator : PartialMap world) where
  constructor MkPrefixRecoveryIndependent
  0 accumulatorCommutes :
    {before, afterState : SystemState name key value world error} ->
    (foreign : Transition before afterState) ->
    OccursIn foreign trace ->
    Not (transitionActor foreign = selected) ->
    PartialCommute (EqEquivalence {a = world}) accumulator
      (partialWorldMap foreign)

||| Theorem 61, corrected to start immediately after L-Begin and use only
||| trace-indexed non-vacuous independence. The accumulator is supplied with its
||| actual endpoint equation rather than guessed from an arbitrary suffix.
||| TODO(proof): induction over InstalledTrace.
public export
recoveryExactnessTheorem : (name : Type) -> (key : Type) ->
  (value : key -> Type) -> (world, error : Type) -> Type
recoveryExactnessTheorem name key value world error =
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (n : name) -> (pre, current : SystemState name key value world error) ->
  (episode : EpisodePrefix name key world error value nameEq keyEq n pre current) ->
  (accumulator : PartialMap world) ->
  PrefixRecoveryIndependent name key world error value nameEq n
    (prefixTransitions episode) accumulator ->
  (restored : world) -> accumulator (worldState current) = Just restored ->
  ForeignReplay name key world error value n (prefixTransitions episode)
    (worldState (episodeStartState episode)) restored

||| Corollary 62, corrected to quantify a maximal closed episode.
||| TODO(proof): Theorem 61 at lastInstalledState followed by L-Unload.
public export
terminalRecoveryTheorem : (name : Type) -> (key : Type) ->
  (value : key -> Type) -> (world, error : Type) -> Type
terminalRecoveryTheorem name key value world error =
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (n : name) -> (pre, afterState : SystemState name key value world error) ->
  (episode : ClosedEpisode name key world error value nameEq keyEq n pre afterState) ->
  TraceIndependent name key world error value (closedTransitions episode) ->
  ForeignReplay name key world error value n (closedTransitions episode)
    (worldState (closedStartState episode)) (worldState afterState)

||| Equation 58's exact L-Begin premise, isolated as a tractable theorem.
public export
BeginSatisfied : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (n : name) -> SystemState name key value world error -> Type
BeginSatisfied {name} {key} {world} {error} {value} nameEq keyEq n state =
  isJust (targetAt @{nameEq} @{keyEq} n state) = True

0 beginSatisfiedFromEquation :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (n : name) ->
  (before, afterState : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq} (LBegin n) before =
    Just (LBeginTag, afterState) ->
  BeginSatisfied nameEq keyEq n before
beginSatisfiedFromEquation nameEq keyEq n before afterState equation
  with (lookupFiber @{nameEq} n (registry before)) proof found
  beginSatisfiedFromEquation nameEq keyEq n before afterState equation | Nothing =
    void (nothingIsNotJust equation)
  beginSatisfiedFromEquation nameEq keyEq n before afterState equation | Just fiber
    with (fiberLifecycle fiber)
    beginSatisfiedFromEquation nameEq keyEq n before afterState equation | Just fiber
      | Inactive Nothing with (targetFiber @{nameEq} @{keyEq} fiber (registry before)) proof target
      beginSatisfiedFromEquation nameEq keyEq n before afterState equation | Just fiber
        | Inactive Nothing | Nothing = void (nothingIsNotJust equation)
      beginSatisfiedFromEquation nameEq keyEq n before afterState equation | Just fiber
        | Inactive Nothing | Just view = Refl
    beginSatisfiedFromEquation nameEq keyEq n before afterState equation | Just fiber
      | Inactive (Just err) = void (nothingIsNotJust equation)
    beginSatisfiedFromEquation nameEq keyEq n before afterState equation | Just fiber
      | Reloading remaining accumulator view = void (nothingIsNotJust equation)
    beginSatisfiedFromEquation nameEq keyEq n before afterState equation | Just fiber
      | Active accumulator view = void (nothingIsNotJust equation)
    beginSatisfiedFromEquation nameEq keyEq n before afterState equation | Just fiber
      | Unloading accumulator view outcome = void (nothingIsNotJust equation)

||| Equation 58 is proved directly from the L-Begin evaluator equation.
public export
0 beginSatisfactionTheorem :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (n : name) -> (before, afterState : SystemState name key value world error) ->
  BeginStep nameEq keyEq n before afterState ->
  BeginSatisfied nameEq keyEq n before
beginSatisfactionTheorem nameEq keyEq n before afterState opening =
  beginSatisfiedFromEquation nameEq keyEq n before afterState
    (checkedActionProjects nameEq keyEq (LBegin n) before afterState LBeginTag
      (beginEquation opening))

||| Structural result for one successful LAdvance. Iter/Finish constructors
||| expose Equation 59; Divert/Raise are the only exits.
public export
data AdvanceStructure : (name, key, world, error : Type) ->
  (value : key -> Type) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected : name) -> (tag : RuleTag) ->
  (before : SystemState name key value world error) -> Type where
  IterAdvance : (fiber : Fiber name key value world error) ->
    lookupFiber @{nameEq} selected (registry before) = Just fiber ->
    (remaining : List (StepEffect key value world error
      (dependencies (componentDependencies (fiberComponent fiber)))
      (componentProvisions (fiberComponent fiber))) **
     (accumulator : LocalState key value world
        (componentProvisions (fiberComponent fiber)) ->
        LocalState key value world (componentProvisions (fiberComponent fiber)) **
      (view : View name
        (dependencies (componentDependencies (fiberComponent fiber))) **
       (fiberLifecycle fiber = Reloading remaining accumulator view,
        targetMatches @{nameEq}
          (targetFiber @{nameEq} @{keyEq} fiber (registry before)) view = True)))) ->
    AdvanceStructure name key world error value nameEq keyEq selected LIterTag before
  FinishAdvance : (fiber : Fiber name key value world error) ->
    lookupFiber @{nameEq} selected (registry before) = Just fiber ->
    (remaining : List (StepEffect key value world error
      (dependencies (componentDependencies (fiberComponent fiber)))
      (componentProvisions (fiberComponent fiber))) **
     (accumulator : LocalState key value world
        (componentProvisions (fiberComponent fiber)) ->
        LocalState key value world (componentProvisions (fiberComponent fiber)) **
      (view : View name
        (dependencies (componentDependencies (fiberComponent fiber))) **
       (fiberLifecycle fiber = Reloading remaining accumulator view,
        targetMatches @{nameEq}
          (targetFiber @{nameEq} @{keyEq} fiber (registry before)) view = True)))) ->
    AdvanceStructure name key world error value nameEq keyEq selected LFinishTag before
  DivertAdvance : AdvanceStructure name key world error value nameEq keyEq
    selected LDivertTag before
  RaiseAdvance : AdvanceStructure name key world error value nameEq keyEq
    selected LRaiseTag before

0 advanceStructureFromEquation :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (n : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (LAdvance n) before = Just (tag, afterState) ->
  AdvanceStructure name key world error value nameEq keyEq n tag before
advanceStructureFromEquation nameEq keyEq n before afterState tag equation
  with (lookupFiber @{nameEq} n (registry before)) proof found
  advanceStructureFromEquation nameEq keyEq n before afterState tag equation | Nothing =
    void (nothingIsNotJust equation)
  advanceStructureFromEquation nameEq keyEq n before afterState tag equation | Just fiber
    with (fiberLifecycle fiber) proof life
    advanceStructureFromEquation nameEq keyEq n before afterState tag equation | Just fiber
      | Inactive outcome = void (nothingIsNotJust equation)
    advanceStructureFromEquation nameEq keyEq n before afterState tag equation | Just fiber
      | Active accumulator view = void (nothingIsNotJust equation)
    advanceStructureFromEquation nameEq keyEq n before afterState tag equation | Just fiber
      | Unloading accumulator view outcome = void (nothingIsNotJust equation)
    advanceStructureFromEquation nameEq keyEq n before afterState tag equation | Just fiber
      | Reloading [] accumulator view
        with (targetMatches @{nameEq}
          (targetFiber @{nameEq} @{keyEq} fiber (registry before)) view) proof matches
      advanceStructureFromEquation nameEq keyEq n before afterState tag equation | Just fiber
        | Reloading [] accumulator view | True =
          case justInjective equation of
            Refl => FinishAdvance fiber found
              ([] ** (accumulator ** (view ** (life, matches))))
      advanceStructureFromEquation nameEq keyEq n before afterState tag equation | Just fiber
        | Reloading [] accumulator view | False =
          case justInjective equation of Refl => DivertAdvance
    advanceStructureFromEquation nameEq keyEq n before afterState tag equation | Just fiber
      | Reloading (step :: rest) accumulator view
        with (resolveCommittedValues @{nameEq} @{keyEq}
          (dependencies (componentDependencies (fiberComponent fiber)))
          view (registry before))
      advanceStructureFromEquation nameEq keyEq n before afterState tag equation | Just fiber
        | Reloading (step :: rest) accumulator view | Nothing =
          void (nothingIsNotJust equation)
      advanceStructureFromEquation nameEq keyEq n before afterState tag equation | Just fiber
        | Reloading (step :: rest) accumulator view | Just capability
          with (runStepEffect step capability
            (MkLocalState (worldState before) (fiberTable fiber)))
        advanceStructureFromEquation nameEq keyEq n before afterState tag equation | Just fiber
          | Reloading (step :: rest) accumulator view | Just capability | Left err =
            case justInjective equation of Refl => RaiseAdvance
        advanceStructureFromEquation nameEq keyEq n before afterState tag equation | Just fiber
          | Reloading (step :: rest) accumulator view | Just capability |
            Right (localAfter, undo)
            with (targetMatches @{nameEq}
              (targetFiber @{nameEq} @{keyEq} fiber (registry before)) view) proof matches
          advanceStructureFromEquation nameEq keyEq n before afterState tag equation | Just fiber
            | Reloading (step :: rest) accumulator view | Just capability |
              Right (localAfter, undo) | False =
                case justInjective equation of Refl => DivertAdvance
          advanceStructureFromEquation nameEq keyEq n before afterState tag equation | Just fiber
            | Reloading (step :: []) accumulator view | Just capability |
              Right (localAfter, undo) | True =
                case justInjective equation of
                  Refl => FinishAdvance fiber found
                    ((step :: []) ** (accumulator **
                      (view ** (life, matches))))
          advanceStructureFromEquation nameEq keyEq n before afterState tag equation | Just fiber
            | Reloading (step :: next :: more) accumulator view | Just capability |
              Right (localAfter, undo) | True =
                case justInjective equation of
                  Refl => IterAdvance fiber found
                    ((step :: next :: more) ** (accumulator **
                      (view ** (life, matches))))

||| Proven structural Equation-59/exit lemma for every successful LAdvance.
public export
0 advanceStructureTheorem :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (n : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (LAdvance n) before = Just (tag, afterState) ->
  AdvanceStructure name key world error value nameEq keyEq n tag before
advanceStructureTheorem = advanceStructureFromEquation

0 unloadGuardFromEquation :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (n : name) ->
  (before, afterState : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq} (LUnload n) before =
    Just (LUnloadTag, afterState) ->
  relied @{nameEq} {key = key} {value = value} {world = world} {error = error} n (registry before) = False
unloadGuardFromEquation nameEq keyEq n before afterState equation
  with (lookupFiber @{nameEq} n (registry before))
  unloadGuardFromEquation nameEq keyEq n before afterState equation | Nothing =
    void (nothingIsNotJust equation)
  unloadGuardFromEquation nameEq keyEq n before afterState equation | Just fiber
    with (fiberLifecycle fiber)
    unloadGuardFromEquation nameEq keyEq n before afterState equation | Just fiber
      | Inactive outcome = void (nothingIsNotJust equation)
    unloadGuardFromEquation nameEq keyEq n before afterState equation | Just fiber
      | Reloading remaining accumulator view = void (nothingIsNotJust equation)
    unloadGuardFromEquation nameEq keyEq n before afterState equation | Just fiber
      | Active accumulator view = void (nothingIsNotJust equation)
    unloadGuardFromEquation nameEq keyEq n before afterState equation | Just fiber
      | Unloading accumulator view outcome
        with (relied @{nameEq} {key = key} {value = value} {world = world} {error = error} n (registry before))
      unloadGuardFromEquation nameEq keyEq n before afterState equation | Just fiber
        | Unloading accumulator view outcome | True =
          void (nothingIsNotJust equation)
      unloadGuardFromEquation nameEq keyEq n before afterState equation | Just fiber
        | Unloading accumulator view outcome | False = Refl

||| Proven local ordering guard: a provider cannot L-Unload while any installed
||| committed view still resolves to it.
public export
0 unloadGuardTheorem :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (n : name) ->
  (before, afterState : SystemState name key value world error) ->
  UnloadStep nameEq keyEq n before afterState ->
  relied @{nameEq} {key = key} {value = value} {world = world} {error = error} n (registry before) = False
unloadGuardTheorem nameEq keyEq n before afterState closing =
  unloadGuardFromEquation nameEq keyEq n before afterState
    (checkedActionProjects nameEq keyEq (LUnload n) before afterState LUnloadTag
      (unloadEquation closing))

||| A nonempty path represents a strict time inequality.
public export
data StrictTransitions : SystemState name key value world error ->
                         SystemState name key value world error -> Type where
  OneOrMore : Transition first middle -> Transitions middle finalState ->
              StrictTransitions first finalState

public export
strictToTransitions : StrictTransitions first finalState ->
  Transitions first finalState
strictToTransitions (OneOrMore step rest) = MoreTransitions step rest

||| Locate a closed episode in one global trace, including its opening boundary.
public export
record LocatedClosedEpisode
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (n : name)
  {initial, final : SystemState name key value world error}
  (global : Transitions initial final) where
  constructor MkLocatedClosedEpisode
  locatedPreStart : SystemState name key value world error
  locatedAfter : SystemState name key value world error
  traceBeforeOpening : Transitions initial locatedPreStart
  locatedEpisode : ClosedEpisode name key world error value nameEq keyEq n
    locatedPreStart locatedAfter
  traceAfterClosing : Transitions locatedAfter final
  0 locatedDecomposition :
    appendTransitions traceBeforeOpening
      (MoreTransitions (beginTransition (closedOpening locatedEpisode))
        (appendTransitions (closedTransitions locatedEpisode) traceAfterClosing)) = global

public export
prefixThroughOpening :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {n : name} ->
  {initial, final : SystemState name key value world error} ->
  {global : Transitions initial final} ->
  (located : LocatedClosedEpisode name key world error value nameEq keyEq n global) ->
  Transitions initial (closedStartState (locatedEpisode located))
prefixThroughOpening located = appendTransitions (traceBeforeOpening located)
  (MoreTransitions (beginTransition (closedOpening (locatedEpisode located))) NoTransitions)

public export
prefixThroughClose :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {n : name} ->
  {initial, final : SystemState name key value world error} ->
  {global : Transitions initial final} ->
  (located : LocatedClosedEpisode name key world error value nameEq keyEq n global) ->
  Transitions initial (locatedAfter located)
prefixThroughClose located = appendTransitions (prefixThroughOpening located)
  (closedTransitions (locatedEpisode located))

||| The selected provider episode is tied to the consumer by prefix equations,
||| so an unrelated earlier/later provider episode cannot be supplied.
public export
record ProviderContainsConsumer
  (providerEpisode : LocatedClosedEpisode name key world error value nameEq keyEq provider global)
  (consumerEpisode : LocatedClosedEpisode name key world error value nameEq keyEq consumer global) where
  constructor MkProviderContainsConsumer
  providerToConsumer : StrictTransitions
    (closedStartState (locatedEpisode providerEpisode))
    (closedStartState (locatedEpisode consumerEpisode))
  consumerToProviderClose : StrictTransitions
    (locatedAfter consumerEpisode) (locatedAfter providerEpisode)
  0 openingOrderInGlobal :
    prefixThroughOpening consumerEpisode =
      appendTransitions (prefixThroughOpening providerEpisode)
        (strictToTransitions providerToConsumer)
  0 closingOrderInGlobal :
    prefixThroughClose providerEpisode =
      appendTransitions (prefixThroughClose consumerEpisode)
        (strictToTransitions consumerToProviderClose)

||| Proven elimination of the same-global-trace containment witness into the two
||| strict ordering paths b < b' and u' < u.
public export
0 providerOrderingProof :
  (containment : ProviderContainsConsumer providerEpisode consumerEpisode) ->
  (StrictTransitions
     (closedStartState (locatedEpisode providerEpisode))
     (closedStartState (locatedEpisode consumerEpisode)),
   StrictTransitions (locatedAfter consumerEpisode) (locatedAfter providerEpisode))
providerOrderingProof containment =
  (providerToConsumer containment, consumerToProviderClose containment)

public export
resolvedProviderAt : DecEq name => DecEq key => name -> key -> name ->
  SystemState name key value world error -> Bool
resolvedProviderAt consumer k provider state =
  case lookupFiber consumer (registry state) of
    Nothing => False
    Just fiber => case committed (fiberLifecycle fiber) of
      Nothing => False
      Just view => case viewLookup k
        (dependencies (componentDependencies (fiberComponent fiber))) view of
          Nothing => False
          Just actual => case decEq actual provider of
            Yes Refl => True
            No _ => False

public export
data ConsumerResolutionConstant : (name, key, world, error : Type) ->
  (value : key -> Type) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  name -> key -> name -> {start, end : SystemState name key value world error} ->
  Transitions start end -> Type where
  ResolutionConstantEnd :
    resolvedProviderAt @{nameEq} @{keyEq} consumer k provider state = True ->
    ConsumerResolutionConstant name key world error value nameEq keyEq
      consumer k provider (NoTransitions {state})
  ResolutionConstantStep :
    (transition : Transition first middle) -> (rest : Transitions middle finalState) ->
    resolvedProviderAt @{nameEq} @{keyEq} consumer k provider first = True ->
    ConsumerResolutionConstant name key world error value nameEq keyEq
      consumer k provider rest ->
    ConsumerResolutionConstant name key world error value nameEq keyEq
      consumer k provider (MoreTransitions transition rest)

public export
providerValueAt : DecEq name => DecEq key => name -> (k : key) ->
  SystemState name key value world error -> Maybe (value k)
providerValueAt provider k state = valueFromProvider provider k (registry state)

public export
data ProviderValueConstant : (name, key, world, error : Type) ->
  (value : key -> Type) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  name -> (k : key) -> value k ->
  {start, end : SystemState name key value world error} ->
  Transitions start end -> Type where
  ValueConstantEnd : providerValueAt @{nameEq} @{keyEq} provider k state = Just v ->
    ProviderValueConstant name key world error value nameEq keyEq
      provider k v (NoTransitions {state})
  ValueConstantStep :
    (transition : Transition first middle) -> (rest : Transitions middle finalState) ->
    providerValueAt @{nameEq} @{keyEq} provider k first = Just v ->
    ProviderValueConstant name key world error value nameEq keyEq provider k v rest ->
    ProviderValueConstant name key world error value nameEq keyEq provider k v
      (MoreTransitions transition rest)

public export
record OrderingResult
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (provider, consumer : name)
  {initial, final : SystemState name key value world error}
  (global : Transitions initial final)
  (providerEpisode : LocatedClosedEpisode name key world error value
    nameEq keyEq provider global)
  (consumerEpisode : LocatedClosedEpisode name key world error value
    nameEq keyEq consumer global)
  (k : key) where
  constructor MkOrderingResult
  distinctFibers : Not (provider = consumer)
  containment : ProviderContainsConsumer providerEpisode consumerEpisode
  consumerResolution : ConsumerResolutionConstant name key world error value
    nameEq keyEq consumer k provider
    (closedTransitions (locatedEpisode consumerEpisode))
  providedValue : value k
  providerValueStable : ProviderValueConstant name key world error value
    nameEq keyEq provider k providedValue
    (closedTransitions (locatedEpisode consumerEpisode))

||| Theorem 63 selects (rather than accepts) the containing provider episode.
||| TODO(proof): global-trace induction using L-Begin and the relied L-Unload guard.
public export
orderingTheorem : (name : Type) -> (key : Type) ->
  (value : key -> Type) -> (world, error : Type) -> Type
orderingTheorem name key value world error =
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (initial, final : SystemState name key value world error) ->
  (global : Transitions initial final) ->
  wellFormed @{nameEq} @{keyEq} initial = True ->
  bindings (registry initial) = [] ->
  (consumer, provider : name) -> (k : key) ->
  installedAt @{nameEq} provider final = False ->
  (consumerEpisode : LocatedClosedEpisode name key world error value
    nameEq keyEq consumer global) ->
  resolvedProviderAt @{nameEq} @{keyEq} consumer k provider
    (closedStartState (locatedEpisode consumerEpisode)) = True ->
  (providerEpisode : LocatedClosedEpisode name key world error value
      nameEq keyEq provider global **
    OrderingResult name key world error value nameEq keyEq provider consumer
      global providerEpisode consumerEpisode k)

||| Executable Equation-59 check for the selected fiber.
public export
transitionResolutionCoherent : (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  name -> {before, afterState : SystemState name key value world error} ->
  Transition before afterState -> Bool
transitionResolutionCoherent nameEq keyEq selected {before}
  (Fired firedNameEq firedKeyEq action tag equation) = case action of
    LAdvance actor => case decEq @{nameEq} actor selected of
      No _ => True
      Yes Refl => case tag of
        LIterTag => currentTarget
        LFinishTag => currentTarget
        _ => True
    _ => True
  where
  currentTarget : Bool
  currentTarget = case lookupFiber @{nameEq} selected (registry before) of
    Nothing => False
    Just fiber => case fiberLifecycle fiber of
      Reloading remaining accumulator view =>
        targetMatches @{nameEq}
          (targetFiber @{nameEq} @{keyEq} fiber (registry before)) view
      _ => False

public export
data ResolutionCoherent : (name, key, world, error : Type) ->
  (value : key -> Type) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  name -> {start, end : SystemState name key value world error} ->
  Transitions start end -> Type where
  CoherentEnd : ResolutionCoherent name key world error value nameEq keyEq
    selected NoTransitions
  CoherentStep : (transition : Transition first middle) ->
    (rest : Transitions middle finalState) ->
    transitionResolutionCoherent nameEq keyEq selected transition = True ->
    ResolutionCoherent name key world error value nameEq keyEq selected rest ->
    ResolutionCoherent name key world error value nameEq keyEq selected
      (MoreTransitions transition rest)

public export
reloadingAt : DecEq name => name -> SystemState name key value world error -> Bool
reloadingAt selected state = case lookupFiber selected (registry state) of
  Nothing => False
  Just fiber => case fiberLifecycle fiber of
    Reloading _ _ _ => True
    _ => False

public export
data ReloadingThroughout : (name, key, world, error : Type) ->
  (value : key -> Type) -> (nameEq : DecEq name) -> name ->
  {start, end : SystemState name key value world error} ->
  Transitions start end -> Type where
  ReloadingEnd : (fiber : Fiber name key value world error) ->
    lookupFiber @{nameEq} selected (registry state) = Just fiber ->
    (remaining : List (StepEffect key value world error
      (dependencies (componentDependencies (fiberComponent fiber)))
      (componentProvisions (fiberComponent fiber))) **
     (accumulator : LocalState key value world
        (componentProvisions (fiberComponent fiber)) ->
        LocalState key value world
          (componentProvisions (fiberComponent fiber)) **
      (view : View name
        (dependencies (componentDependencies (fiberComponent fiber))) **
       fiberLifecycle fiber = Reloading remaining accumulator view))) ->
    ReloadingThroughout name key world error value nameEq selected
      (NoTransitions {state})
  ReloadingStep : (transition : Transition first middle) ->
    (rest : Transitions middle finalState) ->
    reloadingAt @{nameEq} selected first = True ->
    ReloadingThroughout name key world error value nameEq selected rest ->
    ReloadingThroughout name key world error value nameEq selected
      (MoreTransitions transition rest)

public export
committedProvidersAt : DecEq name => name ->
  SystemState name key value world error -> Maybe (List name)
committedProvidersAt selected state = case lookupFiber selected (registry state) of
  Nothing => Nothing
  Just fiber => map viewProviders (committed (fiberLifecycle fiber))

public export
activeAt : DecEq name => name -> SystemState name key value world error -> Bool
activeAt selected state = case lookupFiber selected (registry state) of
  Nothing => False
  Just fiber => isActive (fiberLifecycle fiber)

public export
unloadingAt : DecEq name => name -> SystemState name key value world error -> Bool
unloadingAt selected state = case lookupFiber selected (registry state) of
  Nothing => False
  Just fiber => case fiberLifecycle fiber of
    Unloading _ _ _ => True
    _ => False

public export
data CommittedProvidersConstant : (name, key, world, error : Type) ->
  (value : key -> Type) -> (nameEq : DecEq name) -> name -> List name ->
  {start, end : SystemState name key value world error} ->
  Transitions start end -> Type where
  CommittedProvidersEnd :
    committedProvidersAt @{nameEq} selected state = Just providers ->
    CommittedProvidersConstant name key world error value nameEq selected providers
      (NoTransitions {state})
  CommittedProvidersStep :
    (transition : Transition first middle) -> (rest : Transitions middle finalState) ->
    committedProvidersAt @{nameEq} selected first = Just providers ->
    CommittedProvidersConstant name key world error value nameEq selected providers rest ->
    CommittedProvidersConstant name key world error value nameEq selected providers
      (MoreTransitions transition rest)

public export
data StructuralExit : (name, key, world, error : Type) ->
  (value : key -> Type) ->
  {before, afterState : SystemState name key value world error} ->
  (nameEq : DecEq name) -> name -> List name ->
  Transition before afterState -> Type where
  Finishes : transitionAction transition = LAdvance selected ->
    transitionTag transition = LFinishTag ->
    activeAt @{nameEq} {key = key} {value = value} {world = world} {error = error} selected afterState = True ->
    committedProvidersAt @{nameEq} {key = key} {value = value} {world = world} {error = error} selected afterState = Just providers ->
    StructuralExit name key world error value nameEq selected providers transition
  DivertsBefore : transitionAction transition = LDivert selected ->
    transitionTag transition = LDivertTag ->
    unloadingAt @{nameEq} {key = key} {value = value} {world = world} {error = error} selected afterState = True ->
    StructuralExit name key world error value nameEq selected providers transition
  DivertsAfter : transitionAction transition = LAdvance selected ->
    transitionTag transition = LDivertTag ->
    unloadingAt @{nameEq} {key = key} {value = value} {world = world} {error = error} selected afterState = True ->
    StructuralExit name key world error value nameEq selected providers transition
  Raises : transitionAction transition = LAdvance selected ->
    transitionTag transition = LRaiseTag ->
    unloadingAt @{nameEq} {key = key} {value = value} {world = world} {error = error} selected afterState = True ->
    StructuralExit name key world error value nameEq selected providers transition

||| Structural part of Theorem 64, covering open final episodes by `StillReloading`.
public export
data ResolutionStructure : (name, key, world, error : Type) ->
  (value : key -> Type) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected : name) -> (openingProviders : List name) ->
  {start, current : SystemState name key value world error} ->
  Transitions start current -> Type where
  StillReloading : ReloadingThroughout name key world error value nameEq selected trace ->
    ResolutionCoherent name key world error value nameEq keyEq selected trace ->
    CommittedProvidersConstant name key world error value nameEq selected
      openingProviders trace ->
    ResolutionStructure name key world error value nameEq keyEq selected
      openingProviders trace
  ExitedReloading :
    (exitBefore, exitAfter : SystemState name key value world error) ->
    (initialPart : Transitions start exitBefore) ->
    (exitStep : Transition exitBefore exitAfter) ->
    (remainingPart : Transitions exitAfter current) ->
    appendTransitions initialPart (MoreTransitions exitStep remainingPart) = trace ->
    ReloadingThroughout name key world error value nameEq selected initialPart ->
    ResolutionCoherent name key world error value nameEq keyEq selected initialPart ->
    CommittedProvidersConstant name key world error value nameEq selected
      openingProviders trace ->
    StructuralExit name key world error value nameEq selected openingProviders exitStep ->
    ResolutionStructure name key world error value nameEq keyEq selected
      openingProviders trace

||| Structural Equation-59/exit theorem. Its input is anchored at L-Begin, so an
||| arbitrary Unloading suffix is unrepresentable.
||| TODO(proof): induction over the anchored InstalledTrace.
public export
resolutionStructureTheorem : (name : Type) -> (key : Type) ->
  (value : key -> Type) -> (world, error : Type) -> Type
resolutionStructureTheorem name key value world error =
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (n : name) -> (pre, current : SystemState name key value world error) ->
  (episode : EpisodePrefix name key world error value nameEq keyEq n pre current) ->
  (openingProviders : List name **
    (committedProvidersAt @{nameEq} n (episodeStartState episode) =
       Just openingProviders,
     ResolutionStructure name key world error value nameEq keyEq n
       openingProviders (prefixTransitions episode)))

||| Full Theorem 64 recovery branch over a maximal closed episode. Structural
||| coherence is separated so it can be proved without assuming temporal recovery.
||| TODO(proof): combine resolutionStructureTheorem with terminalRecoveryTheorem.
public export
resolutionCoherenceTheorem : (name : Type) -> (key : Type) ->
  (value : key -> Type) -> (world, error : Type) -> Type
resolutionCoherenceTheorem name key value world error =
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (n : name) -> (pre, afterState : SystemState name key value world error) ->
  (episode : ClosedEpisode name key world error value nameEq keyEq n pre afterState) ->
  TraceIndependent name key world error value (closedTransitions episode) ->
  (openingProviders : List name **
    (committedProvidersAt @{nameEq} n (closedStartState episode) =
       Just openingProviders,
     ResolutionStructure name key world error value nameEq keyEq n
       openingProviders (closedInside episode),
     ForeignReplay name key world error value n (closedTransitions episode)
      (worldState (closedStartState episode)) (worldState afterState)))
