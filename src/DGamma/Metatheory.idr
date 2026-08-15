module DGamma.Metatheory

import DGamma.Core
import DGamma.Effects
import DGamma.Coeffects
import DGamma.Unified
import DGamma.Calculus
import Decidable.Equality
import Data.List
import Data.List.Elem
import Data.Maybe

%default total

public export
parentValid : DecEq name => Parent name ->
  Registry name key value world error -> Bool
parentValid Root fibers = True
parentValid (ChildOf parent) fibers = isJust (lookupFiber parent fibers)

public export
parentChainSafe : DecEq name => Nat -> List name -> name ->
  Registry name key value world error -> Bool
parentChainSafe Z seen current fibers = False
parentChainSafe (S fuel) seen current fibers =
  case lookupFiber current fibers of
    Nothing => False
    Just fiber => case fiberParent fiber of
      Root => True
      ChildOf parent =>
        if elemDec parent seen
          then False
          else parentChainSafe fuel (parent :: seen) parent fibers

public export
viewProvidersInstalled : DecEq name => Registry name key value world error ->
  View name deps -> Bool
viewProvidersInstalled fibers EmptyView = True
viewProvidersInstalled fibers (ProviderView provider rest) =
  case lookupFiber provider fibers of
    Nothing => False
    Just fiber => installed (fiberLifecycle fiber) &&
                  viewProvidersInstalled fibers rest

public export
lifecycleProvidersInstalled : DecEq name =>
  Registry name key value world error -> Lifecycle world error name deps -> Bool
lifecycleProvidersInstalled fibers (Inactive _) = True
lifecycleProvidersInstalled fibers (Reloading _ _ view) = viewProvidersInstalled fibers view
lifecycleProvidersInstalled fibers (Active _ view) = viewProvidersInstalled fibers view
lifecycleProvidersInstalled fibers (Unloading _ view _) = viewProvidersInstalled fibers view

public export
pairwiseProvisionDisjoint : DecEq key =>
  List (Binding name (FiberAt name key value world error)) -> Bool
pairwiseProvisionDisjoint [] = True
pairwiseProvisionDisjoint (Bind n fiber :: rest) =
  provisionsDisjointFrom (componentProvisions (fiberComponent fiber)) rest &&
  pairwiseProvisionDisjoint rest

||| Definition 58 as an executable decision procedure. Name uniqueness is
||| intrinsic to Registry; View totality is intrinsic to View. The remaining
||| clauses check parent closure/acyclicity, provision disjointness, and that all
||| committed providers are active.
public export
wellFormed : DecEq name => DecEq key =>
  SystemState name key value world error -> Bool
wellFormed state =
  let fibers = registry state
      entries = registryFibers fibers
      fuel = S (length entries)
      parentsClosed = all (\(Bind n fiber) => parentValid (fiberParent fiber) fibers) entries
      parentsAcyclic = all (\(Bind n fiber) => parentChainSafe fuel [n] n fibers) entries
      providersInstalled = all (\(Bind n fiber) =>
        lifecycleProvidersInstalled fibers (fiberLifecycle fiber)) entries
   in parentsClosed && parentsAcyclic &&
      pairwiseProvisionDisjoint entries && providersInstalled

public export
0 justInjective : Just left = Just right -> left = right
justInjective Refl = Refl

||| Same-action determinism is a tractable checked property of the evaluator.
public export
0 applyActionDeterministic : (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  (state : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq} action state = Just (leftTag, leftState) ->
  applyAction @{nameEq} @{keyEq} action state = Just (rightTag, rightState) ->
  (leftTag = rightTag, leftState = rightState)
applyActionDeterministic nameEq keyEq action state left right =
  case justInjective (trans (sym left) right) of
    Refl => (Refl, Refl)

||| Theorem 59 (Preservation), stated against the complete executable
||| Definition-58 invariant above. It is deliberately not postulated.
||| TODO(proof): exhaustive rule proof, with O-Insert/O-Remove tree lemmas and
||| the L-Unload relied guard discharging provider installation.
public export
preservationTheorem : (name : Type) -> (key : Type) ->
  (value : key -> Type) -> (world, error : Type) -> Type
preservationTheorem name key value world error =
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (before, after : SystemState name key value world error) ->
  Transition before after ->
  wellFormed @{nameEq} @{keyEq} before = True ->
  wellFormed @{nameEq} @{keyEq} after = True

||| Definition 60 for this executable calculus. Programs are partial because an
||| iteration may raise. Successful inverses remain partial maps.
public export
stepPartialEffect : StepEffect world error -> PartialEffFn world
stepPartialEffect step before = case runStepEffect step before of
  Left _ => Nothing
  Right (after, undo) => Just (after, \later => Just (undo later))

public export
programPartialEffect : List (StepEffect world error) -> PartialEffFn world
programPartialEffect [] before = Just (before, \later => Just later)
programPartialEffect (step :: rest) before =
  case stepPartialEffect step before of
    Nothing => Nothing
    Just (middle, undo) => case programPartialEffect rest middle of
      Nothing => Nothing
      Just (after, restUndo) => Just (after, partialCompose undo restUndo)

public export
ComponentsIndependent : {key, world, error : Type} -> {value : key -> Type} ->
  Component key value world error -> Component key value world error -> Type
ComponentsIndependent {world} left right =
  PartialEffectIndependent (EqEquivalence {a = world})
    (programPartialEffect (componentProgram left))
    (programPartialEffect (componentProgram right))

public export
RegistryProgramsIndependent : {name, key, world, error : Type} ->
  {value : key -> Type} -> (nameEq : DecEq name) ->
  Registry name key value world error -> Type
RegistryProgramsIndependent {name} nameEq fibers =
  (leftName, rightName : name) ->
  (leftFiber, rightFiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} leftName fibers = Just leftFiber ->
  lookupFiber @{nameEq} rightName fibers = Just rightFiber ->
  Not (leftName = rightName) ->
  ComponentsIndependent (fiberComponent leftFiber) (fiberComponent rightFiber)

public export
actionActor : Action name key value world error -> name
actionActor (OInsert n _ _) = n
actionActor (ORetire n) = n
actionActor (ORemove n) = n
actionActor (LBegin n) = n
actionActor (LAdvance n) = n
actionActor (LDivert n) = n
actionActor (LLeave n) = n
actionActor (LUnload n) = n

public export
worldTransformerFor : (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  Action name key value world error -> RuleTag ->
  SystemState name key value world error -> world -> world
worldTransformerFor nameEq keyEq (LAdvance n) tag state =
  case lookupFiber @{nameEq} n (registry state) of
    Nothing => id
    Just fiber => case fiberLifecycle fiber of
      Reloading (step :: _) accumulator view => case tag of
        LIterTag => forward step
        LFinishTag => forward step
        LDivertTag => forward step
        _ => id
      _ => id
  where
  forward : StepEffect world error -> world -> world
  forward step before = case runStepEffect step before of
    Left _ => before
    Right (after, _) => after
worldTransformerFor nameEq keyEq (LUnload n) tag state =
  case lookupFiber @{nameEq} n (registry state) of
    Just fiber => case fiberLifecycle fiber of
      Unloading accumulator view outcome => accumulator
      _ => id
    Nothing => id
worldTransformerFor nameEq keyEq action tag state = id

public export
worldTransformer : {before, after : SystemState name key value world error} ->
  Transition before after -> world -> world
worldTransformer {before} (Fired nameEq keyEq action tag equation) =
  worldTransformerFor nameEq keyEq action tag before

||| Relational replay of only transitions not acting on the selected fiber.
||| The relation avoids smuggling an equality decision independent of the one
||| captured by each Transition.
public export
data ForeignReplay : (name, key, world, error : Type) -> (value : key -> Type) ->
  {start, end : SystemState name key value world error} ->
  (selected : name) -> Transitions start end -> world -> world -> Type where
  ReplayDone : ForeignReplay name key world error value selected
                             NoTransitions initialWorld initialWorld
  ReplayOwn : (transition : Transition first middle) ->
    actionActor (transitionAction transition) = selected ->
    ForeignReplay name key world error value selected rest
                  initialWorld finalWorld ->
    ForeignReplay name key world error value selected
                  (MoreTransitions transition rest) initialWorld finalWorld
  ReplayForeign : (transition : Transition first middle) ->
    Not (actionActor (transitionAction transition) = selected) ->
    ForeignReplay name key world error value selected rest
                  (worldTransformer transition initialWorld) finalWorld ->
    ForeignReplay name key world error value selected
                  (MoreTransitions transition rest) initialWorld finalWorld

||| A trace that starts installed and closes exactly at L-Unload, while all
||| preceding states in the segment remain installed: Definition 53 episode.
public export
data EpisodeTrace : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (n : name) ->
  SystemState name key value world error ->
  SystemState name key value world error -> Type where
  EpisodeCloses : (transition : Transition before afterState) ->
    transitionAction transition = LUnload n ->
    installedAt @{nameEq} n before = True ->
    installedAt @{nameEq} n afterState = False ->
    EpisodeTrace nameEq n before afterState
  EpisodeContinues : (transition : Transition before middle) ->
    installedAt @{nameEq} n before = True ->
    installedAt @{nameEq} n middle = True ->
    EpisodeTrace nameEq n middle afterState ->
    EpisodeTrace nameEq n before afterState

public export
episodeTransitions : EpisodeTrace nameEq n before afterState ->
  Transitions before afterState
episodeTransitions (EpisodeCloses transition action isBefore isAfter) =
  MoreTransitions transition NoTransitions
episodeTransitions (EpisodeContinues transition isBefore isMiddle rest) =
  MoreTransitions transition (episodeTransitions rest)

||| Definition 60's global hypothesis: every pair of component programs that
||| can participate in the run is independent. This is stronger than checking
||| only one snapshot and accommodates insertion during an episode.
public export
AllComponentsIndependent : (key, world, error : Type) ->
  (value : key -> Type) -> Type
AllComponentsIndependent key world error value =
  (left, right : Component key value world error) ->
  ComponentsIndependent left right

public export
accumulatorAt : DecEq name => name ->
  SystemState name key value world error -> Maybe (world -> world)
accumulatorAt n state = case lookupFiber n (registry state) of
  Nothing => Nothing
  Just fiber => case fiberLifecycle fiber of
    Inactive _ => Nothing
    Reloading _ accumulator view => Just accumulator
    Active accumulator view => Just accumulator
    Unloading accumulator view outcome => Just accumulator

||| A prefix contained wholly inside one episode.
public export
data OpenEpisodeTrace : (name, key, world, error : Type) ->
  (value : key -> Type) -> (nameEq : DecEq name) -> (n : name) ->
  {start, end : SystemState name key value world error} ->
  Transitions start end -> Type where
  OpenEpisodeEnd : installedAt @{nameEq} n state = True ->
    OpenEpisodeTrace name key world error value nameEq n (NoTransitions {state})
  OpenEpisodeStep : installedAt @{nameEq} n first = True ->
    OpenEpisodeTrace name key world error value nameEq n rest ->
    OpenEpisodeTrace name key world error value nameEq n
      (MoreTransitions transition rest)

||| Theorem 61 (recovery exactness), stated at every open episode prefix.
||| TODO(proof): induction over OpenEpisodeTrace, commuting each foreign world
||| map across the selected accumulator with Definition-60 independence.
public export
recoveryExactnessTheorem : (name : Type) -> (key : Type) ->
  (value : key -> Type) -> (world, error : Type) -> Type
recoveryExactnessTheorem name key value world error =
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (n : name) -> (before, current : SystemState name key value world error) ->
  (trace : Transitions before current) ->
  OpenEpisodeTrace name key world error value nameEq n trace ->
  AllComponentsIndependent key world error value ->
  (accumulator : world -> world **
    (accumulatorAt @{nameEq} n current = Just accumulator,
     ForeignReplay name key world error value n trace (worldState before)
       (accumulator (worldState current))))

||| Corollary 62 (terminal recovery), precisely stated for a closed episode in
||| the executable LTS. Control fields are intentionally excluded: worldState is
||| this model's paper relation `approximately equal`.
||| TODO(proof): induction over EpisodeTrace using Definition-60 independence
||| and each StepEffect witness; registration/control edits are world identity.
public export
terminalRecoveryTheorem : (name : Type) -> (key : Type) ->
  (value : key -> Type) -> (world, error : Type) -> Type
terminalRecoveryTheorem name key value world error =
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (n : name) -> (before, after : SystemState name key value world error) ->
  (episode : EpisodeTrace nameEq n before after) ->
  AllComponentsIndependent key world error value ->
  ForeignReplay name key world error value n (episodeTransitions episode)
    (worldState before) (worldState after)

||| A consumer's committed resolution at one state.
public export
record ResolvesAt (nameEq : DecEq name) (keyEq : DecEq key)
                  (state : SystemState name key value world error)
                  (consumer : name) (k : key) (provider : name) where
  constructor MkResolvesAt
  consumerFiber : Fiber name key value world error
  consumerPresent : lookupFiber @{nameEq} consumer (registry state) = Just consumerFiber
  consumerInstalled : installed (fiberLifecycle consumerFiber) = True
  committedProvider : case committed (fiberLifecycle consumerFiber) of
    Nothing => Void
    Just view => viewLookup @{keyEq} k
      (dependencies (componentDependencies (fiberComponent consumerFiber))) view =
      Just provider

public export
record ProviderAvailable (nameEq : DecEq name) (keyEq : DecEq key)
                         (state : SystemState name key value world error)
                         (provider : name) (k : key) where
  constructor MkProviderAvailable
  providerFiber : Fiber name key value world error
  providerPresent : lookupFiber @{nameEq} provider (registry state) = Just providerFiber
  providerInstalled : installed (fiberLifecycle providerFiber) = True
  providedValue : (v : value k **
    lookupBinding @{keyEq} k (providedValues (fiberComponent providerFiber)) = Just v)

public export
providerValueAt : DecEq name => DecEq key => name -> (k : key) ->
  SystemState name key value world error -> Maybe (value k)
providerValueAt provider k state = case lookupFiber provider (registry state) of
  Nothing => Nothing
  Just fiber => lookupBinding k (providedValues (fiberComponent fiber))

||| The static component-table normalization makes the paper's visibility
||| clause directly checkable along a trace.
public export
data ProviderValueConstant : (name, key, world, error : Type) ->
  (value : key -> Type) -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (provider : name) -> (k : key) -> value k ->
  {start, end : SystemState name key value world error} ->
  Transitions start end -> Type where
  ValueConstantEnd :
    providerValueAt @{nameEq} @{keyEq} provider k state = Just v ->
    ProviderValueConstant name key world error value nameEq keyEq
      provider k v (NoTransitions {state})
  ValueConstantStep :
    {first, middle, finalState : SystemState name key value world error} ->
    (transition : Transition first middle) ->
    (rest : Transitions middle finalState) ->
    providerValueAt @{nameEq} @{keyEq} provider k first = Just v ->
    ProviderValueConstant name key world error value nameEq keyEq
      provider k v rest ->
    ProviderValueConstant name key world error value nameEq keyEq
      provider k v (MoreTransitions transition rest)

||| Theorem 63's pointwise visibility invariant. Its episode-order corollary is
||| stated below through LocatedEpisode.
||| TODO(proof): derive provider lookup/installation from WellFormed clause 4 and
||| the intrinsically total View.
public export
providerVisibilityTheorem : (name : Type) -> (key : Type) ->
  (value : key -> Type) -> (world, error : Type) -> Type
providerVisibilityTheorem name key value world error =
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  wellFormed @{nameEq} @{keyEq} state = True ->
  (consumer, provider : name) -> (k : key) ->
  ResolvesAt nameEq keyEq state consumer k provider ->
  ProviderAvailable nameEq keyEq state provider k

public export
appendTransitions : Transitions first middle -> Transitions middle finalState ->
  Transitions first finalState
appendTransitions NoTransitions second = second
appendTransitions (MoreTransitions step rest) second =
  MoreTransitions step (appendTransitions rest second)

||| Locate an episode inside one global trace.
public export
record LocatedEpisode {name, key, world, error : Type} {value : key -> Type}
                      (nameEq : DecEq name) (n : name)
                      {initial, final : SystemState name key value world error}
                      (global : Transitions initial final) where
  constructor MkLocatedEpisode
  episodeStart : SystemState name key value world error
  episodeEnd : SystemState name key value world error
  traceBefore : Transitions initial episodeStart
  episodeBody : EpisodeTrace nameEq n episodeStart episodeEnd
  traceAfter : Transitions episodeEnd final
  0 traceDecomposition :
    appendTransitions traceBefore
      (appendTransitions (episodeTransitions episodeBody) traceAfter) = global

public export
record OrderingResult (name, key, world, error : Type) (value : key -> Type)
                      (nameEq : DecEq name) (keyEq : DecEq key)
                      (provider : name) (k : key)
                      (providerStart, consumerStart, consumerEnd, providerEnd :
                        SystemState name key value world error)
                      (consumerTrace : Transitions consumerStart consumerEnd) where
  constructor MkOrderingResult
  providerBeforeConsumer : Transitions providerStart consumerStart
  consumerBeforeProviderClose : Transitions consumerEnd providerEnd
  providedValue : value k
  valueConstant : ProviderValueConstant name key world error value
    nameEq keyEq provider k providedValue consumerTrace

||| Theorem 63 (ordering), including provider-before-consumer,
||| consumer-before-provider-close, and exact provider-table constancy through
||| the whole consumer episode.
||| TODO(proof): decompose the global trace at both L-Begin/L-Unload boundaries;
||| the relied guard rules out the opposite close order.
public export
orderingTheorem : (name : Type) -> (key : Type) ->
  (value : key -> Type) -> (world, error : Type) -> Type
orderingTheorem name key value world error =
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (initial, final : SystemState name key value world error) ->
  (global : Transitions initial final) ->
  wellFormed @{nameEq} @{keyEq} initial = True ->
  (provider, consumer : name) -> (k : key) ->
  (providerEpisode : LocatedEpisode nameEq provider global) ->
  (consumerEpisode : LocatedEpisode nameEq consumer global) ->
  ResolvesAt nameEq keyEq (episodeStart consumerEpisode) consumer k provider ->
  OrderingResult name key world error value nameEq keyEq provider k
    (episodeStart providerEpisode) (episodeStart consumerEpisode)
    (episodeEnd consumerEpisode) (episodeEnd providerEpisode)
    (episodeTransitions (episodeBody consumerEpisode))

||| One-step executable check for Equation 59. It applies only to the selected
||| fiber's successful continuing/final iterations.
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

||| Resolution-coherence predicate: every advancing iteration in a Reloading
||| interval uses the committed view as its current target; a changed target can
||| only leave through Divert/Raise and terminal recovery.
public export
data ResolutionCoherent : (name, key, world, error : Type) ->
  (value : key -> Type) -> {start, end : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  name -> Transitions start end -> Type where
  CoherentEnd : ResolutionCoherent name key world error value
    nameEq keyEq selected NoTransitions
  CoherentStep : transitionResolutionCoherent nameEq keyEq selected transition = True ->
    ResolutionCoherent name key world error value nameEq keyEq selected rest ->
    ResolutionCoherent name key world error value nameEq keyEq selected
      (MoreTransitions transition rest)

public export
reloadingAt : DecEq name => name ->
  SystemState name key value world error -> Bool
reloadingAt n state = case lookupFiber n (registry state) of
  Just fiber => case fiberLifecycle fiber of
    Reloading _ _ _ => True
    _ => False
  Nothing => False

public export
activeAt : DecEq name => name ->
  SystemState name key value world error -> Bool
activeAt n state = case lookupFiber n (registry state) of
  Just fiber => isActive (fiberLifecycle fiber)
  Nothing => False

public export
data ReloadingThroughout : (name, key, world, error : Type) ->
  (value : key -> Type) -> (nameEq : DecEq name) -> (selected : name) ->
  {start, end : SystemState name key value world error} ->
  Transitions start end -> Type where
  ReloadingEnd : reloadingAt @{nameEq} selected state = True ->
    ReloadingThroughout name key world error value nameEq selected
      (NoTransitions {state})
  ReloadingStep : reloadingAt @{nameEq} selected first = True ->
    ReloadingThroughout name key world error value nameEq selected rest ->
    ReloadingThroughout name key world error value nameEq selected
      (MoreTransitions transition rest)

public export
data AbortRule : (name, key, world, error : Type) -> (value : key -> Type) ->
  {before, afterState : SystemState name key value world error} ->
  name -> Transition before afterState -> Type where
  AbortedBeforeIteration : transitionAction transition = LDivert selected ->
    transitionTag transition = LDivertTag ->
    AbortRule name key world error value selected transition
  AbortedAfterLanding : transitionAction transition = LAdvance selected ->
    transitionTag transition = LDivertTag ->
    AbortRule name key world error value selected transition
  RaisedDuringIteration : transitionAction transition = LAdvance selected ->
    transitionTag transition = LRaiseTag ->
    AbortRule name key world error value selected transition

public export
data ResolutionExit : (name, key, world, error : Type) ->
  (value : key -> Type) -> (nameEq : DecEq name) -> (selected : name) ->
  (startState, endState, exitBefore, exitAfter :
    SystemState name key value world error) ->
  (whole : Transitions startState endState) ->
  Transition exitBefore exitAfter -> Type where
  FinishedResolution : transitionAction transition = LAdvance selected ->
    transitionTag transition = LFinishTag ->
    activeAt @{nameEq} {key = key} {value = value}
      {world = world} {error = error} selected exitAfter = True ->
    ResolutionExit name key world error value nameEq selected
      startState endState exitBefore exitAfter whole transition
  AbortedResolution : AbortRule name key world error value selected transition ->
    ForeignReplay name key world error value selected whole
      (worldState startState) (worldState endState) ->
    ResolutionExit name key world error value nameEq selected
      startState endState exitBefore exitAfter whole transition

||| The complete Theorem-64 result: an initial Reloading interval satisfying
||| Equation 59, followed by exactly the Finish or Divert/Raise alternative.
public export
record ResolutionOutcome (name, key, world, error : Type)
                         (value : key -> Type) (nameEq : DecEq name)
                         (keyEq : DecEq key) (selected : name)
                         {episodeStart, episodeEnd :
                           SystemState name key value world error}
                         (whole : Transitions episodeStart episodeEnd) where
  constructor MkResolutionOutcome
  exitBefore : SystemState name key value world error
  exitAfter : SystemState name key value world error
  initialInterval : Transitions episodeStart exitBefore
  exitTransition : Transition exitBefore exitAfter
  remainingInterval : Transitions exitAfter episodeEnd
  0 resolutionDecomposition :
    appendTransitions initialInterval
      (MoreTransitions exitTransition remainingInterval) = whole
  intervalReloading : ReloadingThroughout name key world error value
    nameEq selected initialInterval
  intervalCoherent : ResolutionCoherent name key world error value
    nameEq keyEq selected initialInterval
  exitAlternative : ResolutionExit name key world error value nameEq selected
    episodeStart episodeEnd exitBefore exitAfter whole exitTransition

||| Theorem 64. The result states both Equation 59 and the paper's exact exit
||| dichotomy; its abort branch includes Corollary 62's terminal recovery.
||| TODO(proof): split a closed EpisodeTrace at the first transition leaving
||| Reloading, using the one-way lifecycle graph and applyAction's target guards.
public export
resolutionCoherenceTheorem : (name : Type) -> (key : Type) ->
  (value : key -> Type) -> (world, error : Type) -> Type
resolutionCoherenceTheorem name key value world error =
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (n : name) -> (start, end : SystemState name key value world error) ->
  (episode : EpisodeTrace nameEq n start end) ->
  AllComponentsIndependent key world error value ->
  ResolutionOutcome name key world error value nameEq keyEq n
    (episodeTransitions episode)
