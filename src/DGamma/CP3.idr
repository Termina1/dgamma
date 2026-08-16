module DGamma.CP3

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.Unified
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality

listMember : DecEq a => a -> List a -> Bool
listMember wanted [] = False
listMember wanted (current :: rest) = case decEq wanted current of
  Yes Refl => True
  No _ => listMember wanted rest

%default total

||| Definition 65. `provider` precedes `consumer` when a key the former may
||| provide is declared by the latter. This is the finite executable graph used
||| by the Progress and Confluence statements.
public export
precedesFiber : DecEq key =>
  Fiber name key value world error -> Fiber name key value world error -> Bool
precedesFiber provider consumer = any declaredByConsumer
  (dependencies (componentProvisions (fiberComponent provider)))
  where
  declaredByConsumer : key -> Bool
  declaredByConsumer k = listMember k
    (dependencies (componentDependencies (fiberComponent consumer)))

public export
precedesAt : DecEq name => DecEq key => name -> name ->
  SystemState name key value world error -> Bool
precedesAt provider consumer state =
  case lookupFiber provider (registry state) of
    Nothing => False
    Just providerFiber => case lookupFiber consumer (registry state) of
      Nothing => False
      Just consumerFiber => precedesFiber providerFiber consumerFiber

||| One concrete edge of Definition 65. Keeping the witnesses makes later
||| acyclicity and transposition lemmas independent of Boolean reflection.
public export
record PrecedenceEdge {name, key, world, error : Type} {value : key -> Type}
  (nameEq : DecEq name) (provider, consumer : name)
  (state : SystemState name key value world error) where
  constructor MkPrecedenceEdge
  edgeKey : key
  providerFiber : Fiber name key value world error
  consumerFiber : Fiber name key value world error
  providerFound : lookupFiber @{nameEq} provider (registry state) = Just providerFiber
  consumerFound : lookupFiber @{nameEq} consumer (registry state) = Just consumerFiber
  providerDeclares : Elem edgeKey
    (dependencies (componentProvisions (fiberComponent providerFiber)))
  consumerDeclares : Elem edgeKey
    (dependencies (componentDependencies (fiberComponent consumerFiber)))

public export
data PrecedencePath : {name, key, world, error : Type} ->
  {value : key -> Type} -> (nameEq : DecEq name) ->
  (state : SystemState name key value world error) -> name -> name -> Type where
  PrecedenceOne : PrecedenceEdge nameEq from to state ->
    PrecedencePath nameEq state from to
  PrecedenceMore : PrecedenceEdge nameEq from middle state ->
    PrecedencePath nameEq state middle to ->
    PrecedencePath nameEq state from to

||| Paper's acyclicity hypothesis, stated directly on the finite registry.
public export
PrecedenceAcyclic : {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> SystemState name key value world error -> Type
PrecedenceAcyclic {name} nameEq state =
  (n : name) -> PrecedencePath nameEq state n n -> Void

providerFromCandidate : DecEq name => DecEq key => key -> List name ->
  List (Binding name (FiberAt name key value world error)) -> Bool
providerFromCandidate wanted supported [] = False
providerFromCandidate wanted supported (Bind n fiber :: rest) =
  (listMember n supported && listMember wanted
    (dependencies (componentProvisions (fiberComponent fiber)))) ||
  providerFromCandidate wanted supported rest

parentFromCandidate : DecEq name => Parent name -> List name -> Bool
parentFromCandidate Root supported = True
parentFromCandidate (ChildOf parent) supported = listMember parent supported

supportCandidate : DecEq name => DecEq key =>
  List (Binding name (FiberAt name key value world error)) ->
  List name -> Binding name (FiberAt name key value world error) -> Bool
supportCandidate entries supported (Bind n fiber) =
  not (retired fiber) &&
  parentFromCandidate (fiberParent fiber) supported &&
  all (\k => providerFromCandidate k supported entries)
    (dependencies (componentDependencies (fiberComponent fiber)))

supportPass : DecEq name => DecEq key =>
  List (Binding name (FiberAt name key value world error)) ->
  List name -> List name
supportPass entries supported = foldl addIfSupported supported entries
  where
  addIfSupported : List name ->
    Binding name (FiberAt name key value world error) -> List name
  addIfSupported accumulated entry@(Bind n fiber) =
    if listMember n accumulated then accumulated
    else if supportCandidate entries accumulated entry
      then n :: accumulated else accumulated

supportFuel : DecEq name => DecEq key => Nat ->
  List (Binding name (FiberAt name key value world error)) ->
  List name -> List name
supportFuel Z entries supported = supported
supportFuel (S fuel) entries supported =
  supportFuel fuel entries (supportPass entries supported)

||| Definition 67's least support set, computed by bounded fixed-point
||| iteration. A registry has at most `length entries` successful additions.
public export
supportSet : DecEq name => DecEq key =>
  SystemState name key value world error -> List name
supportSet state = let entries = registryFibers (registry state) in
  supportFuel (length entries) entries []

public export
isSupported : DecEq name => DecEq key => name ->
  SystemState name key value world error -> Bool
isSupported n state = listMember n (supportSet state)

||| Definition 69 at one runtime fiber: every Active instance has installed
||| every key in its declared provision.
public export
fiberTotalOnProvision : DecEq key =>
  Fiber name key value world error -> Bool
fiberTotalOnProvision fiber = case fiberLifecycle fiber of
  Active accumulator view => all
    (\k => isJust (lookupBinding k (ownedValues (fiberTable fiber))))
    (dependencies (componentProvisions (fiberComponent fiber)))
  _ => True

public export
allFibersTotalOnProvision : DecEq key =>
  SystemState name key value world error -> Bool
allFibersTotalOnProvision state = all totalEntry
  (registryFibers (registry state))
  where
  totalEntry : Binding name (FiberAt name key value world error) -> Bool
  totalEntry (Bind n fiber) = fiberTotalOnProvision fiber

public export
noFailedFibers : SystemState name key value world error -> Bool
noFailedFibers state = all notFailed (registryFibers (registry state))
  where
  notFailed : Binding name (FiberAt name key value world error) -> Bool
  notFailed (Bind n fiber) = case fiberLifecycle fiber of
    Inactive (Just errorValue) => False
    _ => True

public export
programsBoundedBy : Nat -> SystemState name key value world error -> Bool
programsBoundedBy bound state = all bounded (registryFibers (registry state))
  where
  bounded : Binding name (FiberAt name key value world error) -> Bool
  bounded (Bind n fiber) =
    length (componentProgram (fiberComponent fiber)) <= bound

||| A concrete host lifecycle rule applicable at one state. `LAdvance` covers
||| the landing L-Iter/L-Finish/L-Raise/L-Divert alternatives; the separate
||| `LDivert` constructor is the optional aborting rule.
public export
data LifecycleMove :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  SystemState name key value world error -> Type where
  CanBegin : (actor : name) -> (after : SystemState name key value world error) ->
    applyAction @{nameEq} @{keyEq} (LBegin actor) before = Just (LBeginTag, after) ->
    LifecycleMove nameEq keyEq before
  CanAdvance : (actor : name) -> (tag : RuleTag) ->
    (after : SystemState name key value world error) ->
    applyAction @{nameEq} @{keyEq} (LAdvance actor) before = Just (tag, after) ->
    LifecycleMove nameEq keyEq before
  CanDivert : (actor : name) -> (after : SystemState name key value world error) ->
    applyAction @{nameEq} @{keyEq} (LDivert actor) before = Just (LDivertTag, after) ->
    LifecycleMove nameEq keyEq before
  CanLeave : (actor : name) -> (after : SystemState name key value world error) ->
    applyAction @{nameEq} @{keyEq} (LLeave actor) before = Just (LLeaveTag, after) ->
    LifecycleMove nameEq keyEq before
  CanUnload : (actor : name) -> (after : SystemState name key value world error) ->
    applyAction @{nameEq} @{keyEq} (LUnload actor) before = Just (LUnloadTag, after) ->
    LifecycleMove nameEq keyEq before

tryUnload : DecEq name => DecEq key => (actor : name) ->
  (state : SystemState name key value world error) -> Maybe (LifecycleMove %search %search state)
tryUnload actor state with (applyAction (LUnload actor) state) proof result
  tryUnload actor state | Just (LUnloadTag, after) =
    Just (CanUnload actor after result)
  tryUnload actor state | Just (tag, after) = Nothing
  tryUnload actor state | Nothing = Nothing

tryLeave : DecEq name => DecEq key => (actor : name) ->
  (state : SystemState name key value world error) -> Maybe (LifecycleMove %search %search state)
tryLeave actor state with (applyAction (LLeave actor) state) proof result
  tryLeave actor state | Just (LLeaveTag, after) =
    Just (CanLeave actor after result)
  tryLeave actor state | Just (tag, after) = tryUnload actor state
  tryLeave actor state | Nothing = tryUnload actor state

tryDivert : DecEq name => DecEq key => (actor : name) ->
  (state : SystemState name key value world error) -> Maybe (LifecycleMove %search %search state)
tryDivert actor state with (applyAction (LDivert actor) state) proof result
  tryDivert actor state | Just (LDivertTag, after) =
    Just (CanDivert actor after result)
  tryDivert actor state | Just (tag, after) = tryLeave actor state
  tryDivert actor state | Nothing = tryLeave actor state

tryAdvance : DecEq name => DecEq key => (actor : name) ->
  (state : SystemState name key value world error) -> Maybe (LifecycleMove %search %search state)
tryAdvance actor state with (applyAction (LAdvance actor) state) proof result
  tryAdvance actor state | Just (tag, after) =
    Just (CanAdvance actor tag after result)
  tryAdvance actor state | Nothing = tryDivert actor state

tryLifecycleActor : DecEq name => DecEq key => (actor : name) ->
  (state : SystemState name key value world error) -> Maybe (LifecycleMove %search %search state)
tryLifecycleActor actor state with (applyAction (LBegin actor) state) proof result
  tryLifecycleActor actor state | Just (LBeginTag, after) =
    Just (CanBegin actor after result)
  tryLifecycleActor actor state | Just (tag, after) = tryAdvance actor state
  tryLifecycleActor actor state | Nothing = tryAdvance actor state

firstApplicableFrom : DecEq name => DecEq key =>
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (state : SystemState name key value world error) -> Maybe (LifecycleMove %search %search state)
firstApplicableFrom [] state = Nothing
firstApplicableFrom (Bind actor fiber :: rest) state =
  case tryLifecycleActor actor state of
    Just move => Just move
    Nothing => firstApplicableFrom rest state

||| Executable witness search over exactly the lifecycle rules required by the
||| paper's Progress theorem.
public export
firstApplicableLifecycle : DecEq name => DecEq key =>
  (state : SystemState name key value world error) -> Maybe (LifecycleMove %search %search state)
firstApplicableLifecycle state =
  firstApplicableFrom (registryFibers (registry state)) state

public export
LifecycleMaximal : (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  SystemState name key value world error -> Type
LifecycleMaximal nameEq keyEq state =
  LifecycleMove nameEq keyEq state -> Void

public export
isLifecycleAction : Action name key value world error -> Bool
isLifecycleAction (OInsert n parent component) = False
isLifecycleAction (ORetire n) = False
isLifecycleAction (ORemove n) = False
isLifecycleAction _ = True

public export
data LifecycleOnly :
  {first, last : SystemState name key value world error} ->
  Transitions first last -> Type where
  LifecycleOnlyEnd : LifecycleOnly NoTransitions
  LifecycleOnlyStep :
    (transition : Transition first middle) ->
    (rest : Transitions middle last) ->
    isLifecycleAction (transitionAction transition) = True ->
    LifecycleOnly rest -> LifecycleOnly (MoreTransitions transition rest)

public export
0 stepsActingOn : {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, last : SystemState name key value world error} ->
  DecEq name => name -> Transitions first last -> Nat
stepsActingOn actor NoTransitions = Z
stepsActingOn actor (MoreTransitions transition rest) =
  let later = stepsActingOn actor rest in
  case decEq (transitionActor transition) actor of
    Yes Refl => S later
    No _ => later

sameNameList : DecEq name => List name -> List name -> Bool
sameNameList [] [] = True
sameNameList [] (_ :: _) = False
sameNameList (_ :: _) [] = False
sameNameList (x :: xs) (y :: ys) = case decEq x y of
  Yes Refl => sameNameList xs ys
  No _ => False

public export
targetProvidersAt : DecEq name => DecEq key => name ->
  SystemState name key value world error -> Maybe (List name)
targetProvidersAt actor state = case lookupFiber actor (registry state) of
  Nothing => Nothing
  Just fiber => map viewProviders (targetFiber fiber (registry state))

sameTarget : DecEq name => Maybe (List name) -> Maybe (List name) -> Bool
sameTarget Nothing Nothing = True
sameTarget Nothing (Just _) = False
sameTarget (Just _) Nothing = False
sameTarget (Just left) (Just right) = sameNameList left right

||| Equation 61 as an exact indexed count. Transition endpoint states live in
||| erased indices, so the count is evidence rather than a runtime traversal;
||| `sameTarget` itself remains executable on explicit endpoints.
public export
data TargetTurnCount :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  {first, last : SystemState name key value world error} ->
  Transitions first last -> Nat -> Type where
  NoTargetTurns : TargetTurnCount name key world error value nameEq keyEq actor
    NoTransitions Z
  TargetStayed :
    (transition : Transition first middle) ->
    (rest : Transitions middle finalState) ->
    sameTarget @{nameEq}
      (targetProvidersAt @{nameEq} @{keyEq} actor first)
      (targetProvidersAt @{nameEq} @{keyEq} actor middle) = True ->
    TargetTurnCount name key world error value nameEq keyEq actor rest turns ->
    TargetTurnCount name key world error value nameEq keyEq actor
      (MoreTransitions transition rest) turns
  TargetChanged :
    (transition : Transition first middle) ->
    (rest : Transitions middle finalState) ->
    sameTarget @{nameEq}
      (targetProvidersAt @{nameEq} @{keyEq} actor first)
      (targetProvidersAt @{nameEq} @{keyEq} actor middle) = False ->
    TargetTurnCount name key world error value nameEq keyEq actor rest turns ->
    TargetTurnCount name key world error value nameEq keyEq actor
      (MoreTransitions transition rest) (S turns)

public export
record ProgressResult
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (bound : Nat)
  {first, last : SystemState name key value world error}
  (trace : Transitions first last) where
  constructor MkProgressResult
  noDeadlock : quiet @{nameEq} @{keyEq} last = False -> LifecycleMove nameEq keyEq last
  perFiberBound : (actor : name) -> (turns : Nat) ->
    TargetTurnCount name key world error value nameEq keyEq actor trace turns ->
    LTE (stepsActingOn @{nameEq} actor trace)
      ((bound + 4) * (turns + 1))
  maximalIsQuiet : LifecycleMaximal nameEq keyEq last ->
    quiet @{nameEq} @{keyEq} last = True

||| Theorem 66, faithfully specialized to finite traces and static-list
||| iterators. Finiteness of N is intrinsic in the registry representation.
||| TODO(proof): the unloading-chain case needs the proved global Ordering
||| theorem; the numerical bound then follows by precedence induction.
public export
progressTheorem : (name : Type) -> (key : Type) ->
  (value : key -> Type) -> (world, error : Type) -> Type
progressTheorem name key value world error =
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (bound : Nat) ->
  (first, last : SystemState name key value world error) ->
  (trace : Transitions first last) ->
  LifecycleOnly trace ->
  registryWellFormed @{nameEq} @{keyEq} first = True ->
  PrecedenceAcyclic nameEq first ->
  programsBoundedBy bound first = True ->
  ProgressResult name key world error value nameEq keyEq bound trace

||| Tractable executable core: a successful search result is already the exact
||| indexed applicability witness needed by the no-deadlock conclusion.
public export
0 searchedLifecycleMove :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  (move : LifecycleMove nameEq keyEq state) ->
  firstApplicableLifecycle @{nameEq} @{keyEq} state = Just move ->
  LifecycleMove nameEq keyEq state
searchedLifecycleMove nameEq keyEq state move equation = move

||| The logical consequence in the last sentence of Theorem 66: no-deadlock
||| turns lifecycle maximality into quiescence without an additional axiom.
public export
0 maximalQuietFromNoDeadlock :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  (noDeadlock : quiet @{nameEq} @{keyEq} state = False ->
    LifecycleMove nameEq keyEq state) ->
  LifecycleMaximal nameEq keyEq state ->
  quiet @{nameEq} @{keyEq} state = True
maximalQuietFromNoDeadlock nameEq keyEq state noDeadlock maximal
  with (quiet @{nameEq} @{keyEq} state) proof quietResult
  maximalQuietFromNoDeadlock nameEq keyEq state noDeadlock maximal | True = Refl
  maximalQuietFromNoDeadlock nameEq keyEq state noDeadlock maximal | False =
    void (maximal (noDeadlock Refl))

||| The lifecycle/control observation retained by Section 4's `simeq`. Effect
||| tables and ambient state are deliberately excluded here and compared by
||| `EffectStateRelated` instead.
public export
data LifecycleShape = InactiveCleanShape | InactiveFailedShape |
  ReloadingShape | ActiveShape | UnloadingCleanShape | UnloadingFailedShape

public export
lifecycleShape : Lifecycle key value world error name deps provision -> LifecycleShape
lifecycleShape (Inactive Nothing) = InactiveCleanShape
lifecycleShape (Inactive (Just _)) = InactiveFailedShape
lifecycleShape (Reloading _ _ _) = ReloadingShape
lifecycleShape (Active _ _) = ActiveShape
lifecycleShape (Unloading _ _ Nothing) = UnloadingCleanShape
lifecycleShape (Unloading _ _ (Just _)) = UnloadingFailedShape

public export
record ControlObservation (name : Type) where
  constructor MkControlObservation
  observedRetired : Bool
  observedShape : LifecycleShape
  observedProviders : Maybe (List name)

public export
controlObservationAt : DecEq name => name ->
  SystemState name key value world error -> Maybe (ControlObservation name)
controlObservationAt n state = case lookupFiber n (registry state) of
  Nothing => Nothing
  Just fiber => Just (MkControlObservation (retired fiber)
    (lifecycleShape (fiberLifecycle fiber))
    (map viewProviders (committed (fiberLifecycle fiber))))

||| Section 4's control-field side of observational equality, pointwise to
||| avoid function extensionality.
public export
record ControlEquivalent
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name)
  (left, right : SystemState name key value world error) where
  constructor MkControlEquivalent
  0 controlPointwise : (n : name) ->
    controlObservationAt @{nameEq} n left =
    controlObservationAt @{nameEq} n right

||| Effect/control conjunction used by Lemma 72 and Theorem 73. This finite
||| mechanization uses exact full-effect agreement, which is stronger than the
||| paper's open observational equivalence.
public export
record SystemEquivalent
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (left, right : SystemState name key value world error) where
  constructor MkSystemEquivalent
  0 effectsEquivalent : EffectStateRelated keyEq
    (projectEffectState @{nameEq} left) (projectEffectState @{nameEq} right)
  0 controlsEquivalent : ControlEquivalent name key world error value nameEq
    left right

||| A shared orchestration subsequence. Lifecycle steps may be inserted or
||| deleted independently, while O-Insert/O-Retire/O-Remove actions must occur
||| in the same order and carry the very same runtime component values.
public export
data SameOrchestration :
  {leftFirst, leftLast, rightFirst, rightLast :
    SystemState name key value world error} ->
  Transitions leftFirst leftLast -> Transitions rightFirst rightLast -> Type where
  SameOrchestrationEnd : SameOrchestration NoTransitions NoTransitions
  SkipLeftLifecycle :
    (transition : Transition leftFirst leftMiddle) ->
    (leftRest : Transitions leftMiddle leftLast) ->
    isLifecycleAction (transitionAction transition) = True ->
    SameOrchestration leftRest rightTrace ->
    SameOrchestration (MoreTransitions transition leftRest) rightTrace
  SkipRightLifecycle :
    (transition : Transition rightFirst rightMiddle) ->
    (rightRest : Transitions rightMiddle rightLast) ->
    isLifecycleAction (transitionAction transition) = True ->
    SameOrchestration leftTrace rightRest ->
    SameOrchestration leftTrace (MoreTransitions transition rightRest)
  MatchOrchestration :
    (action : Action name key value world error) ->
    (leftTransition : Transition leftFirst leftMiddle) ->
    (leftRest : Transitions leftMiddle leftLast) ->
    (rightTransition : Transition rightFirst rightMiddle) ->
    (rightRest : Transitions rightMiddle rightLast) ->
    isLifecycleAction action = False ->
    transitionAction leftTransition = action ->
    transitionAction rightTransition = action ->
    SameOrchestration leftRest rightRest ->
    SameOrchestration (MoreTransitions leftTransition leftRest)
      (MoreTransitions rightTransition rightRest)

||| Non-strict support order used by Definition 67's canonical form.
public export
data BeforeIn : a -> a -> List a -> Type where
  BeforeHere : Elem later rest -> BeforeIn earlier later (earlier :: rest)
  BeforeThere : BeforeIn earlier later rest ->
    BeforeIn earlier later (other :: rest)

public export
record LinearizesSupport
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (state : SystemState name key value world error)
  (order : List name) where
  constructor MkLinearizesSupport
  0 orderSound : (n : name) -> Elem n order ->
    isSupported @{nameEq} @{keyEq} n state = True
  0 orderComplete : (n : name) ->
    isSupported @{nameEq} @{keyEq} n state = True -> Elem n order
  0 edgesOrdered : (provider, consumer : name) ->
    PrecedenceEdge nameEq provider consumer state ->
    Elem provider order -> Elem consumer order ->
    BeforeIn provider consumer order

||| An open episode located in a global trace. At a quiescent successful state,
||| Lemma 70 identifies exactly one such final episode for each supported name.
public export
record LocatedEpisodePrefix
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (n : name)
  {initial, final : SystemState name key value world error}
  (global : Transitions initial final) where
  constructor MkLocatedEpisodePrefix
  prefixPreStart : SystemState name key value world error
  prefixCurrent : SystemState name key value world error
  traceBeforePrefix : Transitions initial prefixPreStart
  locatedPrefix : EpisodePrefix name key world error value nameEq keyEq n
    prefixPreStart prefixCurrent
  traceAfterPrefix : Transitions prefixCurrent final
  0 prefixDecomposition :
    appendTransitions traceBeforePrefix
      (MoreTransitions (beginTransition (opening locatedPrefix))
        (appendTransitions (prefixTransitions locatedPrefix) traceAfterPrefix)) = global

public export
record CanonicalSchedule
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, originalFinal : SystemState name key value world error}
  (original : Transitions initial originalFinal) where
  constructor MkCanonicalSchedule
  canonicalFinal : SystemState name key value world error
  canonicalTrace : Transitions initial canonicalFinal
  sameInputs : SameOrchestration original canonicalTrace
  supportOrder : List name
  supportLinearization : LinearizesSupport name key world error value nameEq keyEq
    originalFinal supportOrder
  canonicalEpisode : (n : name) -> Elem n supportOrder ->
    LocatedEpisodePrefix name key world error value nameEq keyEq n canonicalTrace
  canonicalEndpoint : SystemEquivalent name key world error value nameEq keyEq
    originalFinal canonicalFinal

||| Lemma 70, stated as pointwise equality so no finite-set quotient or function
||| extensionality is required.
public export
SupportMatchesActive : {name, key, world, error : Type} ->
  {value : key -> Type} -> (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  SystemState name key value world error -> Type
SupportMatchesActive {name} nameEq keyEq state = (n : name) ->
  isSupported @{nameEq} @{keyEq} n state = activeAt n state
  where
  activeAt : name -> SystemState name key value world error -> Bool
  activeAt n state = case lookupFiber n (registry state) of
    Nothing => False
    Just fiber => isActive (fiberLifecycle fiber)

||| Lemma 70. The statement exposes every paper premise; its full induction on
||| the support relation remains part of the Confluence proof debt.
||| TODO(proof): well-founded support induction and parent-registration frame.
public export
supportAtQuiescenceTheorem : (name : Type) -> (key : Type) ->
  (value : key -> Type) -> (world, error : Type) -> Type
supportAtQuiescenceTheorem name key value world error =
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  PrecedenceAcyclic nameEq state ->
  quiet @{nameEq} @{keyEq} state = True ->
  noFailedFibers state = True ->
  allFibersTotalOnProvision @{keyEq} state = True ->
  SupportMatchesActive nameEq keyEq state

||| Lemma 71's effect-level transposition core. Control-field applicability
||| frames are separate debt, but the endpoint effect diamond is exactly the
||| generated-monoid commutation field of Definition 60.
public export
0 activationEffectTransposition :
  (independent : TraceIndependent name key world error value keyEq trace) ->
  (left, right : name) -> Not (left = right) ->
  (leftT : TraceEffectTransformation name key world error value left trace) ->
  (rightT : TraceEffectTransformation name key world error value right trace) ->
  PartialCommute (EffectStateEquivalence keyEq)
    (runTraceEffectTransformation leftT)
    (runTraceEffectTransformation rightT)
activationEffectTransposition
  (MkTraceIndependent commute yieldsStable) left right distinct leftT rightT =
  commute left right distinct leftT rightT

||| Lemma 72's precise finite deletion statement. `surviving` is an actual
||| checked trace, not a list permutation claim, and the endpoint relation keeps
||| both effect and control observations.
public export
record DeletionResult
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {initial, originalFinal : SystemState name key value world error}
  (original : Transitions initial originalFinal) where
  constructor MkDeletionResult
  survivingFinal : SystemState name key value world error
  surviving : Transitions initial survivingFinal
  endpointPreserved : SystemEquivalent name key world error value nameEq keyEq
    originalFinal survivingFinal

||| Theorem 73. Part 1 returns the canonical schedule promised by the paper;
||| Part 2 states unique quiescent endpoints for any same-input execution, up to
||| the explicit effect/control equivalence. Name-renaming generalization is
||| retained as documented proof debt rather than hidden in exact equality.
||| TODO(proof): Lemma-71 applicability frames, Lemma-72 deletion induction,
||| support well-foundedness, and canonical episode sorting.
public export
confluenceTheorem : (name : Type) -> (key : Type) ->
  (value : key -> Type) -> (world, error : Type) -> Type
confluenceTheorem name key value world error =
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (initial, leftFinal, rightFinal : SystemState name key value world error) ->
  (leftTrace : Transitions initial leftFinal) ->
  (rightTrace : Transitions initial rightFinal) ->
  registryWellFormed @{nameEq} @{keyEq} initial = True ->
  bindings (registry initial) = [] ->
  quiet @{nameEq} @{keyEq} leftFinal = True ->
  quiet @{nameEq} @{keyEq} rightFinal = True ->
  noFailedFibers leftFinal = True ->
  noFailedFibers rightFinal = True ->
  allFibersTotalOnProvision @{keyEq} leftFinal = True ->
  allFibersTotalOnProvision @{keyEq} rightFinal = True ->
  TraceIndependent name key world error value keyEq leftTrace ->
  TraceIndependent name key world error value keyEq rightTrace ->
  SameOrchestration leftTrace rightTrace ->
  (CanonicalSchedule name key world error value nameEq keyEq leftTrace,
   CanonicalSchedule name key world error value nameEq keyEq rightTrace,
   SystemEquivalent name key world error value nameEq keyEq leftFinal rightFinal)

||| Reflexivity sanity check for the orchestration projection: arbitrary
||| lifecycle noise is ignored, while each orchestration action matches itself.
public export
0 sameOrchestrationReflexive :
  (trace : Transitions first last) -> SameOrchestration trace trace
sameOrchestrationReflexive NoTransitions = SameOrchestrationEnd
sameOrchestrationReflexive
  (MoreTransitions transition@(Fired nameEq keyEq (OInsert n parent component)
    tag equation) rest) =
  MatchOrchestration (OInsert n parent component) transition rest transition rest
    Refl Refl Refl (sameOrchestrationReflexive rest)
sameOrchestrationReflexive
  (MoreTransitions transition@(Fired nameEq keyEq (ORetire n) tag equation) rest) =
  MatchOrchestration (ORetire n) transition rest transition rest
    Refl Refl Refl (sameOrchestrationReflexive rest)
sameOrchestrationReflexive
  (MoreTransitions transition@(Fired nameEq keyEq (ORemove n) tag equation) rest) =
  MatchOrchestration (ORemove n) transition rest transition rest
    Refl Refl Refl (sameOrchestrationReflexive rest)
sameOrchestrationReflexive
  (MoreTransitions transition@(Fired nameEq keyEq (LBegin n) tag equation) rest) =
  SkipLeftLifecycle transition rest Refl
    (SkipRightLifecycle transition rest Refl (sameOrchestrationReflexive rest))
sameOrchestrationReflexive
  (MoreTransitions transition@(Fired nameEq keyEq (LAdvance n) tag equation) rest) =
  SkipLeftLifecycle transition rest Refl
    (SkipRightLifecycle transition rest Refl (sameOrchestrationReflexive rest))
sameOrchestrationReflexive
  (MoreTransitions transition@(Fired nameEq keyEq (LDivert n) tag equation) rest) =
  SkipLeftLifecycle transition rest Refl
    (SkipRightLifecycle transition rest Refl (sameOrchestrationReflexive rest))
sameOrchestrationReflexive
  (MoreTransitions transition@(Fired nameEq keyEq (LLeave n) tag equation) rest) =
  SkipLeftLifecycle transition rest Refl
    (SkipRightLifecycle transition rest Refl (sameOrchestrationReflexive rest))
sameOrchestrationReflexive
  (MoreTransitions transition@(Fired nameEq keyEq (LUnload n) tag equation) rest) =
  SkipLeftLifecycle transition rest Refl
    (SkipRightLifecycle transition rest Refl (sameOrchestrationReflexive rest))

public export
0 systemEquivalentReflexive :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (state : SystemState name key value world error) ->
  SystemEquivalent name key world error value nameEq keyEq state state
systemEquivalentReflexive nameEq keyEq state = MkSystemEquivalent
  (MkEffectStateRelated Refl (\selected, k => Refl))
  (MkControlEquivalent (\n => Refl))

||| Four possible installed-bit evolutions for one checked transition. The only
||| changing cases are the two episode boundaries.
public export
data InstallationEvolution :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (action : Action name key value world error) -> (tag : RuleTag) -> Type where
  RemainedUninstalled :
    installedAt @{nameEq} selected before = False ->
    installedAt @{nameEq} selected afterState = False ->
    InstallationEvolution name key world error value nameEq keyEq selected
      before afterState action tag
  RemainedInstalled :
    installedAt @{nameEq} selected before = True ->
    installedAt @{nameEq} selected afterState = True ->
    InstallationEvolution name key world error value nameEq keyEq selected
      before afterState action tag
  OpenedInstallation :
    InstallationEvolution name key world error value nameEq keyEq selected
      before afterState (LBegin selected) LBeginTag
  ClosedInstallation :
    InstallationEvolution name key world error value nameEq keyEq selected
      before afterState (LUnload selected) LUnloadTag

installedMaybe : {name, key, world, error : Type} -> {value : key -> Type} ->
  Maybe (Fiber name key value world error) -> Bool
installedMaybe Nothing = False
installedMaybe (Just fiber) = installed (fiberLifecycle fiber)

0 installedAtLookupEquation :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  installedAt @{nameEq} selected state =
    installedMaybe {name = name} {key = key} {world = world}
      {error = error} {value = value}
      (lookupFiber @{nameEq} selected (registry state))
installedAtLookupEquation nameEq selected
  state@(MkSystemState ambient fibers)
  with (lookupFiber @{nameEq} selected fibers)
  installedAtLookupEquation nameEq selected
    state@(MkSystemState ambient fibers) | Nothing = Refl
  installedAtLookupEquation nameEq selected
    state@(MkSystemState ambient fibers) | Just fiber = Refl

||| Any successful action on another name preserves the selected installed bit.
public export
0 foreignInstalledStable :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected : name) ->
  (action : Action name key value world error) ->
  Not (selected = actionOwner action) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} action before = Just (tag, afterState) ->
  installedAt @{nameEq} selected before =
    installedAt @{nameEq} selected afterState
foreignInstalledStable {name} {key} {world} {error} {value}
  nameEq keyEq selected action distinct before afterState tag equation =
  let update = applyActionLocalUpdate nameEq keyEq action before afterState tag
        equation
      lookupTargetSource = systemLocalUpdateForeign nameEq selected
        (actionOwner action) distinct before afterState update
      maybeTargetSource = cong
        (\found => installedMaybe {name = name} {key = key} {world = world}
          {error = error} {value = value} found)
        lookupTargetSource
      sourceObserved = installedAtLookupEquation nameEq selected before
      targetObserved = installedAtLookupEquation nameEq selected afterState
  in trans sourceObserved (trans (sym maybeTargetSource) (sym targetObserved))

public export
0 foreignInstallationEvolution :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected : name) ->
  (action : Action name key value world error) ->
  Not (selected = actionOwner action) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} action before = Just (tag, afterState) ->
  InstallationEvolution name key world error value nameEq keyEq selected
    before afterState action tag
foreignInstallationEvolution nameEq keyEq selected action distinct before
  afterState tag equation =
  let stable = foreignInstalledStable nameEq keyEq selected action distinct
        before afterState tag equation in
  case boolEquality (installedAt @{nameEq} selected before) of
    Left sourceFalse =>
      RemainedUninstalled sourceFalse (trans (sym stable) sourceFalse)
    Right sourceTrue =>
      RemainedInstalled sourceTrue (trans (sym stable) sourceTrue)
  where
  boolEquality : (observed : Bool) ->
    Either (observed = False) (observed = True)
  boolEquality False = Left Refl
  boolEquality True = Right Refl

public export
0 installedAtFound :
  (nameEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} selected (registry state) = Just fiber ->
  installedAt @{nameEq} selected state = installed (fiberLifecycle fiber)
installedAtFound {name} {key} {world} {error} {value}
  nameEq selected state fiber found =
  trans (installedAtLookupEquation nameEq selected state)
    (cong (installedMaybe {name = name} {key = key} {world = world}
      {error = error} {value = value}) found)

public export
0 installedAtMissing :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  (observed : Maybe (Fiber name key value world error)) ->
  lookupFiber @{nameEq} selected (registry state) = observed ->
  observed = Nothing ->
  installedAt @{nameEq} selected state = False
installedAtMissing {name} {key} {world} {error} {value}
  nameEq selected state observed found missing =
  trans (installedAtLookupEquation nameEq selected state)
    (trans (cong (installedMaybe {name = name} {key = key} {world = world}
      {error = error} {value = value}) found)
      (cong (installedMaybe {name = name} {key = key} {world = world}
        {error = error} {value = value}) missing))

0 activeImpliesInstalled :
  (nameEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  activeAt @{nameEq} selected state = True ->
  installedAt @{nameEq} selected state = True
activeImpliesInstalled nameEq selected state evidence
  with (lookupFiber @{nameEq} selected (registry state)) proof found
  activeImpliesInstalled nameEq selected state evidence | Nothing = absurd evidence
  activeImpliesInstalled nameEq selected state evidence | Just fiber
    with (fiberLifecycle fiber) proof life
    activeImpliesInstalled nameEq selected state evidence | Just fiber |
      Inactive outcome = absurd evidence
    activeImpliesInstalled nameEq selected state evidence | Just fiber |
      Reloading remaining accumulator view = absurd evidence
    activeImpliesInstalled nameEq selected state evidence | Just fiber |
      Active accumulator view =
        Refl
    activeImpliesInstalled nameEq selected state evidence | Just fiber |
      Unloading accumulator view outcome = absurd evidence

0 reloadingImpliesInstalled :
  (nameEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  reloadingAt @{nameEq} selected state = True ->
  installedAt @{nameEq} selected state = True
reloadingImpliesInstalled nameEq selected state evidence
  with (lookupFiber @{nameEq} selected (registry state)) proof found
  reloadingImpliesInstalled nameEq selected state evidence | Nothing = absurd evidence
  reloadingImpliesInstalled nameEq selected state evidence | Just fiber
    with (fiberLifecycle fiber) proof life
    reloadingImpliesInstalled nameEq selected state evidence | Just fiber |
      Inactive outcome = absurd evidence
    reloadingImpliesInstalled nameEq selected state evidence | Just fiber |
      Reloading remaining accumulator view =
        Refl
    reloadingImpliesInstalled nameEq selected state evidence | Just fiber |
      Active accumulator view = absurd evidence
    reloadingImpliesInstalled nameEq selected state evidence | Just fiber |
      Unloading accumulator view outcome = absurd evidence

0 unloadingImpliesInstalled :
  (nameEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  unloadingAt @{nameEq} selected state = True ->
  installedAt @{nameEq} selected state = True
unloadingImpliesInstalled nameEq selected state evidence
  with (lookupFiber @{nameEq} selected (registry state)) proof found
  unloadingImpliesInstalled nameEq selected state evidence | Nothing = absurd evidence
  unloadingImpliesInstalled nameEq selected state evidence | Just fiber
    with (fiberLifecycle fiber) proof life
    unloadingImpliesInstalled nameEq selected state evidence | Just fiber |
      Inactive outcome = absurd evidence
    unloadingImpliesInstalled nameEq selected state evidence | Just fiber |
      Reloading remaining accumulator view = absurd evidence
    unloadingImpliesInstalled nameEq selected state evidence | Just fiber |
      Active accumulator view = absurd evidence
    unloadingImpliesInstalled nameEq selected state evidence | Just fiber |
      Unloading accumulator view outcome =
        Refl

public export
0 installedAtDecEqCoherent :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (leftEq, rightEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  installedAt @{leftEq} selected state = installedAt @{rightEq} selected state
installedAtDecEqCoherent {name} {key} {world} {error} {value}
  leftEq rightEq selected state =
  let lookupCoherent = lookupFiberDecEqCoherent leftEq rightEq selected
        (registry state)
      observedCoherent = cong
        (installedMaybe {name = name} {key = key} {world = world}
          {error = error} {value = value}) lookupCoherent
  in trans (installedAtLookupEquation leftEq selected state)
    (trans observedCoherent
      (sym (installedAtLookupEquation rightEq selected state)))

0 reloadingAnyImpliesInstalled :
  {leftEq : DecEq name} -> (rightEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  reloadingAt @{leftEq} selected state = True ->
  installedAt @{rightEq} selected state = True
reloadingAnyImpliesInstalled {leftEq} rightEq selected state evidence =
  trans (sym (installedAtDecEqCoherent leftEq rightEq selected state))
    (reloadingImpliesInstalled leftEq selected state evidence)

0 activeAnyImpliesInstalled :
  {leftEq : DecEq name} -> (rightEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  activeAt @{leftEq} selected state = True ->
  installedAt @{rightEq} selected state = True
activeAnyImpliesInstalled {leftEq} rightEq selected state evidence =
  trans (sym (installedAtDecEqCoherent leftEq rightEq selected state))
    (activeImpliesInstalled leftEq selected state evidence)

0 unloadingAnyImpliesInstalled :
  {leftEq : DecEq name} -> (rightEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  unloadingAt @{leftEq} selected state = True ->
  installedAt @{rightEq} selected state = True
unloadingAnyImpliesInstalled {leftEq} rightEq selected state evidence =
  trans (sym (installedAtDecEqCoherent leftEq rightEq selected state))
    (unloadingImpliesInstalled leftEq selected state evidence)


0 reloadingEndpointImpliesInstalled :
  (nameEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  reloadingEndpoint @{nameEq} selected state = True ->
  installedAt @{nameEq} selected state = True
reloadingEndpointImpliesInstalled nameEq selected state evidence
  with (lookupFiber @{nameEq} selected (registry state))
  reloadingEndpointImpliesInstalled nameEq selected state evidence | Nothing =
    absurd evidence
  reloadingEndpointImpliesInstalled nameEq selected state evidence | Just fiber
    with (fiberLifecycle fiber)
    reloadingEndpointImpliesInstalled nameEq selected state evidence | Just fiber |
      Inactive outcome = absurd evidence
    reloadingEndpointImpliesInstalled nameEq selected state evidence | Just fiber |
      Reloading remaining accumulator view = Refl
    reloadingEndpointImpliesInstalled nameEq selected state evidence | Just fiber |
      Active accumulator view = absurd evidence
    reloadingEndpointImpliesInstalled nameEq selected state evidence | Just fiber |
      Unloading accumulator view outcome = absurd evidence

0 activeEndpointImpliesInstalled :
  (nameEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  activeEndpoint @{nameEq} selected state = True ->
  installedAt @{nameEq} selected state = True
activeEndpointImpliesInstalled nameEq selected state evidence
  with (lookupFiber @{nameEq} selected (registry state))
  activeEndpointImpliesInstalled nameEq selected state evidence | Nothing =
    absurd evidence
  activeEndpointImpliesInstalled nameEq selected state evidence | Just fiber
    with (fiberLifecycle fiber)
    activeEndpointImpliesInstalled nameEq selected state evidence | Just fiber |
      Inactive outcome = absurd evidence
    activeEndpointImpliesInstalled nameEq selected state evidence | Just fiber |
      Reloading remaining accumulator view = absurd evidence
    activeEndpointImpliesInstalled nameEq selected state evidence | Just fiber |
      Active accumulator view = Refl
    activeEndpointImpliesInstalled nameEq selected state evidence | Just fiber |
      Unloading accumulator view outcome = absurd evidence

0 unloadingEndpointImpliesInstalled :
  (nameEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  unloadingEndpoint @{nameEq} selected state = True ->
  installedAt @{nameEq} selected state = True
unloadingEndpointImpliesInstalled nameEq selected state evidence
  with (lookupFiber @{nameEq} selected (registry state))
  unloadingEndpointImpliesInstalled nameEq selected state evidence | Nothing =
    absurd evidence
  unloadingEndpointImpliesInstalled nameEq selected state evidence | Just fiber
    with (fiberLifecycle fiber)
    unloadingEndpointImpliesInstalled nameEq selected state evidence | Just fiber |
      Inactive outcome = absurd evidence
    unloadingEndpointImpliesInstalled nameEq selected state evidence | Just fiber |
      Reloading remaining accumulator view = absurd evidence
    unloadingEndpointImpliesInstalled nameEq selected state evidence | Just fiber |
      Active accumulator view = absurd evidence
    unloadingEndpointImpliesInstalled nameEq selected state evidence | Just fiber |
      Unloading accumulator view outcome = Refl

0 lAdvanceStartsInstalled :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (LAdvance selected) before =
    Just (tag, afterState) ->
  installedAt @{nameEq} selected before = True
lAdvanceStartsInstalled nameEq keyEq selected before afterState tag equation
  with (lookupFiber @{nameEq} selected (registry before))
  lAdvanceStartsInstalled nameEq keyEq selected before afterState tag equation |
    Nothing = void (nothingIsNotJust equation)
  lAdvanceStartsInstalled nameEq keyEq selected before afterState tag equation |
    Just fiber with (fiberLifecycle fiber)
    lAdvanceStartsInstalled nameEq keyEq selected before afterState tag equation |
      Just fiber | Inactive outcome = void (nothingIsNotJust equation)
    lAdvanceStartsInstalled nameEq keyEq selected before afterState tag equation |
      Just fiber | Reloading remaining accumulator view = Refl
    lAdvanceStartsInstalled nameEq keyEq selected before afterState tag equation |
      Just fiber | Active accumulator view = void (nothingIsNotJust equation)
    lAdvanceStartsInstalled nameEq keyEq selected before afterState tag equation |
      Just fiber | Unloading accumulator view outcome =
        void (nothingIsNotJust equation)

0 lAdvanceEndsInstalled :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (LAdvance selected) before =
    Just (tag, afterState) ->
  installedAt @{nameEq} selected afterState = True
lAdvanceEndsInstalled {name} {key} {world} {error} {value}
  nameEq keyEq selected before afterState tag equation =
  case advanceStructureTheorem nameEq keyEq selected before afterState tag
    equation of
    IterAdvance fiber found package reloading =>
      reloadingEndpointImpliesInstalled nameEq selected afterState reloading
    FinishAdvance fiber found package active =>
      activeEndpointImpliesInstalled nameEq selected afterState active
    DivertAdvance unloading =>
      unloadingEndpointImpliesInstalled nameEq selected afterState unloading
    RaiseAdvance unloading =>
      unloadingEndpointImpliesInstalled nameEq selected afterState unloading

0 lDivertInstalled :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq} (LDivert selected) before =
    Just (LDivertTag, afterState) ->
  (installedAt @{nameEq} selected before = True,
   installedAt @{nameEq} selected afterState = True)
lDivertInstalled {name} {key} {world} {error} {value}
  nameEq keyEq selected before afterState equation =
  case abortDivertStructureTheorem nameEq keyEq selected before afterState
    equation of
    MkAbortDivertStructure fiber found remaining accumulator view reloading
      changed unloading =>
        (trans (installedAtFound nameEq selected before fiber found)
          (cong installed reloading),
         unloadingEndpointImpliesInstalled nameEq selected afterState unloading)

0 installedAtAfterReplace :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) ->
  (sourceFiber, targetFiberValue : Fiber name key value world error) ->
  (fibers : Registry name key value world error) ->
  (ambient : world) ->
  (found : lookupFiber @{nameEq} selected fibers = Just sourceFiber) ->
  installedAt @{nameEq} selected
    (the (SystemState name key value world error)
      (MkSystemState ambient
        (replaceBinding @{nameEq} selected targetFiberValue fibers))) =
    installed (fiberLifecycle targetFiberValue)
installedAtAfterReplace {name} {key} {world} {error} {value}
  nameEq selected sourceFiber targetFiberValue fibers ambient found =
  trans (installedAtLookupEquation nameEq selected
    (MkSystemState ambient
      (replaceBinding @{nameEq} selected targetFiberValue fibers)))
    (cong (installedMaybe {name = name} {key = key} {world = world}
      {error = error} {value = value})
      (lookupReplacedFiber selected sourceFiber targetFiberValue fibers found))

0 installedSetFiberLifecycle :
  (fiber : Fiber name key value world error) ->
  (next : Lifecycle key value world error name
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber))) ->
  installed (fiberLifecycle (setFiberLifecycle fiber next)) = installed next
installedSetFiberLifecycle (MkFiber component parent retired table lifecycle) next =
  Refl

0 installedSetFiberRuntime :
  (fiber : Fiber name key value world error) ->
  (table : OwnedTable key value
    (componentProvisions (fiberComponent fiber))) ->
  (next : Lifecycle key value world error name
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber))) ->
  installed (fiberLifecycle (setFiberRuntime fiber table next)) = installed next
installedSetFiberRuntime (MkFiber component parent retired oldTable lifecycle)
  table next = Refl

0 lLeaveInstalled :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (LLeave selected) before =
    Just (tag, afterState) ->
  (installedAt @{nameEq} selected before = True,
   installedAt @{nameEq} selected afterState = True)
lLeaveInstalled nameEq keyEq selected
  before@(MkSystemState ambient fibers) afterState tag equation
  with (lookupFiber @{nameEq} selected fibers) proof found
  lLeaveInstalled nameEq keyEq selected
    before@(MkSystemState ambient fibers) afterState tag equation | Nothing =
      void (nothingIsNotJust equation)
  lLeaveInstalled nameEq keyEq selected
    before@(MkSystemState ambient fibers) afterState tag equation | Just fiber
    with (fiberLifecycle fiber)
    lLeaveInstalled nameEq keyEq selected
      before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
      Inactive outcome = void (nothingIsNotJust equation)
    lLeaveInstalled nameEq keyEq selected
      before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
      Reloading remaining accumulator view = void (nothingIsNotJust equation)
    lLeaveInstalled nameEq keyEq selected
      before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
      Unloading accumulator view outcome = void (nothingIsNotJust equation)
    lLeaveInstalled nameEq keyEq selected
      before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
      Active accumulator view
      with (targetMatches @{nameEq}
        (targetFiber @{nameEq} @{keyEq} fiber fibers) view)
      lLeaveInstalled nameEq keyEq selected
        before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
        Active accumulator view | True = void (nothingIsNotJust equation)
      lLeaveInstalled nameEq keyEq selected
        before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
        Active accumulator view | False =
          case justInjective equation of
            Refl => let targetObserved = installedAtAfterReplace nameEq selected
                          fiber (setFiberLifecycle fiber
                            (Unloading accumulator view Nothing))
                          fibers ambient found
                        targetInstalled = trans targetObserved
                          (trans (installedSetFiberLifecycle fiber
                            (Unloading accumulator view Nothing)) Refl)
                    in (Refl, targetInstalled)

0 lUnloadBoundary :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (LUnload selected) before =
    Just (tag, afterState) ->
  (tag = LUnloadTag,
   installedAt @{nameEq} selected before = True,
   installedAt @{nameEq} selected afterState = False)
lUnloadBoundary nameEq keyEq selected
  before@(MkSystemState ambient fibers) afterState tag equation
  with (lookupFiber @{nameEq} selected fibers) proof found
  lUnloadBoundary nameEq keyEq selected
    before@(MkSystemState ambient fibers) afterState tag equation | Nothing =
      void (nothingIsNotJust equation)
  lUnloadBoundary nameEq keyEq selected
    before@(MkSystemState ambient fibers) afterState tag equation | Just fiber
    with (fiberLifecycle fiber)
    lUnloadBoundary nameEq keyEq selected
      before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
      Inactive outcome = void (nothingIsNotJust equation)
    lUnloadBoundary nameEq keyEq selected
      before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
      Reloading remaining accumulator view = void (nothingIsNotJust equation)
    lUnloadBoundary nameEq keyEq selected
      before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
      Active accumulator view = void (nothingIsNotJust equation)
    lUnloadBoundary nameEq keyEq selected
      before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
      Unloading accumulator view outcome
      with (relied @{nameEq} selected fibers)
      lUnloadBoundary nameEq keyEq selected
        before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
        Unloading accumulator view outcome | True =
          void (nothingIsNotJust equation)
      lUnloadBoundary nameEq keyEq selected
        before@(MkSystemState ambient fibers) afterState tag equation | Just fiber |
        Unloading accumulator view outcome | False =
          case justInjective equation of
            Refl =>
              let restored = accumulator (MkLocalState ambient (fiberTable fiber))
                  targetObserved = installedAtAfterReplace nameEq selected fiber
                    (setFiberRuntime fiber
                      (localTable (accumulator
                        (MkLocalState ambient (fiberTable fiber))))
                      (Inactive outcome)) fibers
                    (localWorld (accumulator
                      (MkLocalState ambient (fiberTable fiber)))) found
                  targetUninstalled = trans targetObserved
                    (trans (installedSetFiberRuntime fiber
                      (localTable (accumulator
                        (MkLocalState ambient (fiberTable fiber))))
                      (Inactive outcome)) Refl)
              in (Refl, Refl, targetUninstalled)

0 lBeginBoundary :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  checkedApplyAction @{nameEq} @{keyEq} (LBegin selected) before =
    Just (tag, afterState) ->
  (tag = LBeginTag,
   installedAt @{nameEq} selected before = False,
   installedAt @{nameEq} selected afterState = True)
lBeginBoundary nameEq keyEq selected before afterState tag checkedEquation =
  let rawEquation = checkedActionProjects nameEq keyEq (LBegin selected)
        before afterState tag checkedEquation in
  lBeginRaw rawEquation
  where
  lBeginRaw : applyAction @{nameEq} @{keyEq} (LBegin selected) before =
      Just (tag, afterState) ->
    (tag = LBeginTag,
     installedAt @{nameEq} selected before = False,
     installedAt @{nameEq} selected afterState = True)
  lBeginRaw rawEquation
    with (lookupFiber @{nameEq} selected (registry before)) proof found
    lBeginRaw rawEquation | Nothing = void (nothingIsNotJust rawEquation)
    lBeginRaw rawEquation | Just fiber with (fiberLifecycle fiber)
      lBeginRaw rawEquation | Just fiber | Inactive Nothing
        with (targetFiber @{nameEq} @{keyEq} fiber (registry before))
        lBeginRaw rawEquation | Just fiber | Inactive Nothing | Nothing =
          void (nothingIsNotJust rawEquation)
        lBeginRaw rawEquation | Just fiber | Inactive Nothing | Just view =
          case justInjective rawEquation of
            Refl =>
              let targetObserved = installedAtAfterReplace nameEq selected fiber
                    (setFiberLifecycle fiber
                      (Reloading (componentProgram (fiberComponent fiber)) id view))
                    (registry before) (worldState before) found
                  targetInstalled = trans targetObserved
                    (trans (installedSetFiberLifecycle fiber
                      (Reloading (componentProgram (fiberComponent fiber)) id view))
                      Refl)
              in (Refl, Refl, targetInstalled)
      lBeginRaw rawEquation | Just fiber | Inactive (Just err) =
        void (nothingIsNotJust rawEquation)
      lBeginRaw rawEquation | Just fiber |
        Reloading remaining accumulator view = void (nothingIsNotJust rawEquation)
      lBeginRaw rawEquation | Just fiber | Active accumulator view =
        void (nothingIsNotJust rawEquation)
      lBeginRaw rawEquation | Just fiber |
        Unloading accumulator view outcome = void (nothingIsNotJust rawEquation)

0 installedRetireFiber : (fiber : Fiber name key value world error) ->
  installed (fiberLifecycle (retireFiber fiber)) = installed (fiberLifecycle fiber)
installedRetireFiber (MkFiber component parent retired table lifecycle) = Refl

0 oRetireStable :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (ORetire selected) before =
    Just (tag, afterState) ->
  installedAt @{nameEq} selected before =
    installedAt @{nameEq} selected afterState
oRetireStable nameEq keyEq selected
  before@(MkSystemState ambient fibers) afterState tag equation
  with (lookupFiber @{nameEq} selected fibers) proof found
  oRetireStable nameEq keyEq selected before@(MkSystemState ambient fibers)
    afterState tag equation | Nothing = void (nothingIsNotJust equation)
  oRetireStable nameEq keyEq selected before@(MkSystemState ambient fibers)
    afterState tag equation | Just fiber =
      case justInjective equation of
        Refl =>
          let sourceObserved = installedAtFound nameEq selected
                (MkSystemState ambient fibers) fiber found
              targetObserved = installedAtAfterReplace nameEq selected fiber
                (retireFiber fiber) fibers ambient found
          in sym (trans targetObserved (installedRetireFiber fiber))

0 lookupNotElemNothing : DecEq key => (wanted : key) ->
  (entries : List (Binding key value)) ->
  Not (Elem wanted (bindingKeys entries)) ->
  lookupEntries wanted entries = Nothing
lookupNotElemNothing wanted [] absent = Refl
lookupNotElemNothing wanted (Bind current observed :: rest) absent
  with (decEq wanted current)
  lookupNotElemNothing current (Bind current observed :: rest) absent |
    Yes Refl = void (absent Here)
  lookupNotElemNothing wanted (Bind current observed :: rest) absent |
    No distinct = lookupNotElemNothing wanted rest (\later => absent (There later))

0 lookupDeleteSelf : DecEq key => (removed : key) ->
  (table : CoeffectContext key value) ->
  lookupBinding removed (deleteBinding removed table) = Nothing
lookupDeleteSelf removed (MkCoeffectContext entries unique) =
  lookupNotElemNothing removed (deleteEntries removed entries)
    (deletedKeyNotElem removed entries unique)

0 installedAtAfterDelete :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) ->
  (fibers : Registry name key value world error) -> (ambient : world) ->
  installedAt @{nameEq} selected
    (the (SystemState name key value world error)
      (MkSystemState ambient (deleteBinding selected fibers))) = False
installedAtAfterDelete {name} {key} {world} {error} {value}
  nameEq selected fibers ambient =
  trans (installedAtLookupEquation nameEq selected
    (MkSystemState ambient (deleteBinding selected fibers)))
    (cong (installedMaybe {name = name} {key = key} {world = world}
      {error = error} {value = value}) (lookupDeleteSelf selected fibers))

0 oRemoveUninstalled :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (ORemove selected) before =
    Just (tag, afterState) ->
  (installedAt @{nameEq} selected before = False,
   installedAt @{nameEq} selected afterState = False)
oRemoveUninstalled nameEq keyEq selected
  before@(MkSystemState ambient fibers) afterState tag equation
  with (lookupFiber @{nameEq} selected fibers) proof found
  oRemoveUninstalled nameEq keyEq selected before@(MkSystemState ambient fibers)
    afterState tag equation | Nothing = void (nothingIsNotJust equation)
  oRemoveUninstalled nameEq keyEq selected before@(MkSystemState ambient fibers)
    afterState tag equation | Just fiber
    with (retired fiber && isInactive (fiberLifecycle fiber) &&
      not (hasChild @{nameEq} selected fibers)) proof guards
    oRemoveUninstalled nameEq keyEq selected before@(MkSystemState ambient fibers)
      afterState tag equation | Just fiber | False =
        void (nothingIsNotJust equation)
    oRemoveUninstalled nameEq keyEq selected before@(MkSystemState ambient fibers)
      afterState tag equation | Just fiber | True =
        let tailValid = boolAndRight (retired fiber)
              (isInactive (fiberLifecycle fiber) &&
                not (hasChild @{nameEq} selected fibers)) guards
            inactiveValid = boolAndLeft (isInactive (fiberLifecycle fiber))
              (not (hasChild @{nameEq} selected fibers)) tailValid
        in case inactiveLifecycleWitness (fiberLifecycle fiber) inactiveValid of
          (outcome ** lifecycleIsInactive) =>
            case justInjective equation of
              Refl =>
                let sourceUninstalled =
                      trans (cong installed lifecycleIsInactive) Refl
                in (sourceUninstalled,
                  installedAtAfterDelete nameEq selected fibers ambient)

0 lookupInsertedImplicit : DecEq key => (selected : key) ->
  (next : value selected) -> (before : CoeffectContext key value) ->
  {0 absent : lookupBinding selected before = Nothing} ->
  lookupBinding selected (insertBinding selected next before absent) = Just next
lookupInsertedImplicit selected next (MkCoeffectContext entries unique) {absent}
  with (decEq selected selected)
  lookupInsertedImplicit selected next (MkCoeffectContext entries unique)
    {absent} | Yes Refl = Refl
  lookupInsertedImplicit selected next (MkCoeffectContext entries unique)
    {absent} | No contra = void (contra Refl)

0 setFreshSelectedLookup : DecEq key => (selected : key) ->
  (next : value selected) -> (before : CoeffectContext key value) ->
  (applied : CoeffectApplied before) ->
  setFresh selected next before = Just applied ->
  lookupBinding selected (coeffectAfter applied) = Just next
setFreshSelectedLookup selected next before applied success
  with (lookupBinding selected before) proof found
  setFreshSelectedLookup selected next before applied success | Just current =
    void (nothingIsNotJust success)
  setFreshSelectedLookup selected next before applied success | Nothing =
    case justInjective success of
      Refl => lookupInsertedImplicit selected next before

0 oInsertUninstalled :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (parent : Parent name) -> (component : Component key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (OInsert selected parent component) before =
    Just (tag, afterState) ->
  (installedAt @{nameEq} selected before = False,
   installedAt @{nameEq} selected afterState = False)
oInsertUninstalled {name} {key} {world} {error} {value}
  nameEq keyEq selected parent component
  before@(MkSystemState ambient fibers) afterState tag equation
  with (parentPresent @{nameEq} parent fibers &&
    provisionsDisjointFrom @{keyEq} (componentProvisions component)
      (registryFibers fibers))
  oInsertUninstalled {name} {key} {world} {error} {value}
    nameEq keyEq selected parent component before@(MkSystemState ambient fibers)
    afterState tag equation | False = void (nothingIsNotJust equation)
  oInsertUninstalled {name} {key} {world} {error} {value}
    nameEq keyEq selected parent component before@(MkSystemState ambient fibers)
    afterState tag equation | True
    with (setFresh @{nameEq} selected (freshFiber component parent) fibers) proof inserted
    oInsertUninstalled {name} {key} {world} {error} {value}
      nameEq keyEq selected parent component before@(MkSystemState ambient fibers)
      afterState tag equation | True | Nothing = void (nothingIsNotJust equation)
    oInsertUninstalled {name} {key} {world} {error} {value}
      nameEq keyEq selected parent component before@(MkSystemState ambient fibers)
      afterState tag equation | True | Just applied =
        case justInjective equation of
          Refl =>
            let absent = setFreshAbsent nameEq selected
                  (freshFiber component parent) fibers applied inserted
                sourceUninstalled = installedAtMissing nameEq selected
                  (MkSystemState ambient fibers)
                  (lookupFiber @{nameEq} selected fibers) Refl absent
                insertedLookup = setFreshSelectedLookup selected
                  (freshFiber component parent) fibers applied inserted
                targetObserved = installedAtLookupEquation nameEq selected
                  (MkSystemState ambient (coeffectAfter applied))
                targetUninstalled = trans targetObserved
                  (cong (installedMaybe {name = name} {key = key} {world = world}
                    {error = error} {value = value}) insertedLookup)
            in (sourceUninstalled, targetUninstalled)

0 stableInstallationEvolution :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  installedAt @{nameEq} selected before =
    installedAt @{nameEq} selected afterState ->
  InstallationEvolution name key world error value nameEq keyEq selected
    before afterState action tag
stableInstallationEvolution nameEq keyEq selected before afterState action tag stable =
  case boolEquality (installedAt @{nameEq} selected before) of
    Left sourceFalse =>
      RemainedUninstalled sourceFalse (trans (sym stable) sourceFalse)
    Right sourceTrue =>
      RemainedInstalled sourceTrue (trans (sym stable) sourceTrue)
  where
  boolEquality : (observed : Bool) ->
    Either (observed = False) (observed = True)
  boolEquality False = Left Refl
  boolEquality True = Right Refl

0 openedEvolutionFrom :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) -> tag = LBeginTag ->
  (checkedEquation : checkedApplyAction @{nameEq} @{keyEq}
    (LBegin selected) before = Just (tag, afterState)) ->
  installedAt @{nameEq} selected before = False ->
  installedAt @{nameEq} selected afterState = True ->
  InstallationEvolution name key world error value nameEq keyEq selected
    before afterState (LBegin selected) tag
openedEvolutionFrom nameEq keyEq selected before afterState LBeginTag Refl
  checkedEquation sourceFalse targetTrue =
  OpenedInstallation

0 closedEvolutionFrom :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) -> tag = LUnloadTag ->
  (checkedEquation : checkedApplyAction @{nameEq} @{keyEq}
    (LUnload selected) before = Just (tag, afterState)) ->
  installedAt @{nameEq} selected before = True ->
  installedAt @{nameEq} selected afterState = False ->
  InstallationEvolution name key world error value nameEq keyEq selected
    before afterState (LUnload selected) tag
closedEvolutionFrom nameEq keyEq selected before afterState LUnloadTag Refl
  checkedEquation sourceTrue targetFalse =
  ClosedInstallation

0 lDivertInstallationEvolution :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) -> tag = LDivertTag ->
  applyAction @{nameEq} @{keyEq} (LDivert selected) before =
    Just (tag, afterState) ->
  InstallationEvolution name key world error value nameEq keyEq selected
    before afterState (LDivert selected) tag
lDivertInstallationEvolution nameEq keyEq selected before afterState LDivertTag
  Refl equation = case lDivertInstalled nameEq keyEq selected before afterState
    equation of
    (sourceTrue, targetTrue) => RemainedInstalled sourceTrue targetTrue

||| Lemma 54(4), packaged for every checked step: L-Begin and L-Unload are the
||| unique installed-bit boundaries; every other selected or foreign action
||| preserves the bit.
public export
0 installationEvolutionStep :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (before, afterState : SystemState name key value world error) ->
  (checkedEquation : checkedApplyAction @{nameEq} @{keyEq} action before =
    Just (tag, afterState)) ->
  InstallationEvolution name key world error value nameEq keyEq selected
    before afterState action tag
installationEvolutionStep nameEq keyEq selected action tag before afterState
  checkedEquation with (decEq @{nameEq} selected (actionOwner action))
  installationEvolutionStep nameEq keyEq selected action tag before afterState
    checkedEquation | No distinct =
      foreignInstallationEvolution nameEq keyEq selected action distinct before
        afterState tag (checkedActionProjects nameEq keyEq action before afterState
          tag checkedEquation)
  installationEvolutionStep nameEq keyEq selected
    (OInsert selected parent component) tag before afterState checkedEquation |
    Yes Refl = case oInsertUninstalled nameEq keyEq selected parent component before
        afterState tag (checkedActionProjects nameEq keyEq
          (OInsert selected parent component) before afterState tag checkedEquation) of
        (sourceFalse, targetFalse) =>
          RemainedUninstalled sourceFalse targetFalse
  installationEvolutionStep nameEq keyEq selected (ORetire selected) tag before
    afterState checkedEquation | Yes Refl = stableInstallationEvolution nameEq keyEq selected before afterState
        (ORetire selected) tag (oRetireStable nameEq keyEq selected before afterState tag
          (checkedActionProjects nameEq keyEq (ORetire selected) before afterState
            tag checkedEquation))
  installationEvolutionStep nameEq keyEq selected (ORemove selected) tag before
    afterState checkedEquation | Yes Refl = case oRemoveUninstalled nameEq keyEq selected before afterState tag
        (checkedActionProjects nameEq keyEq (ORemove selected) before afterState
          tag checkedEquation) of
        (sourceFalse, targetFalse) =>
          RemainedUninstalled sourceFalse targetFalse
  installationEvolutionStep nameEq keyEq selected (LBegin selected) tag before
    afterState checkedEquation | Yes Refl = case lBeginBoundary nameEq keyEq selected before afterState tag
        checkedEquation of
        (tagShape, sourceFalse, targetTrue) =>
          openedEvolutionFrom nameEq keyEq selected before afterState tag
            tagShape checkedEquation sourceFalse targetTrue
  installationEvolutionStep nameEq keyEq selected (LAdvance selected) tag before
    afterState checkedEquation | Yes Refl =
        let rawEquation = checkedActionProjects nameEq keyEq (LAdvance selected)
              before afterState tag checkedEquation
        in RemainedInstalled
          (lAdvanceStartsInstalled nameEq keyEq selected before afterState tag
            rawEquation)
          (lAdvanceEndsInstalled nameEq keyEq selected before afterState tag
            rawEquation)
  installationEvolutionStep nameEq keyEq selected (LDivert selected) tag before
    afterState checkedEquation | Yes Refl =
        let rawEquation = checkedActionProjects nameEq keyEq (LDivert selected)
              before afterState tag checkedEquation
            tagShape = successfulLDivertTag nameEq keyEq selected before afterState
              tag rawEquation
        in lDivertInstallationEvolution nameEq keyEq selected before afterState
          tag tagShape rawEquation
  installationEvolutionStep nameEq keyEq selected (LLeave selected) tag before
    afterState checkedEquation | Yes Refl = case lLeaveInstalled nameEq keyEq selected before afterState tag
        (checkedActionProjects nameEq keyEq (LLeave selected) before afterState
          tag checkedEquation) of
        (sourceTrue, targetTrue) => RemainedInstalled sourceTrue targetTrue
  installationEvolutionStep nameEq keyEq selected (LUnload selected) tag before
    afterState checkedEquation | Yes Refl = case lUnloadBoundary nameEq keyEq selected before afterState tag
        (checkedActionProjects nameEq keyEq (LUnload selected) before afterState
          tag checkedEquation) of
        (tagShape, sourceTrue, targetFalse) =>
          closedEvolutionFrom nameEq keyEq selected before afterState tag
            tagShape checkedEquation sourceTrue targetFalse

public export
0 alignedAppendSplit :
  (left : Transitions first middle) -> (right : Transitions middle finalState) ->
  AlignedTransitions name key world error value nameEq keyEq
    (appendTransitions left right) ->
  (AlignedTransitions name key world error value nameEq keyEq left,
   AlignedTransitions name key world error value nameEq keyEq right)
alignedAppendSplit NoTransitions right aligned = (AlignedEnd, aligned)
alignedAppendSplit (MoreTransitions (Fired nameEq keyEq action tag equation) rest)
  right (AlignedStep action tag equation
    (appendTransitions rest right) alignedTail) =
  case alignedAppendSplit rest right alignedTail of
    (leftAligned, rightAligned) =>
      (AlignedStep action tag equation rest leftAligned, rightAligned)

public export
0 appendInstalledTrace :
  (left : Transitions first middle) -> (right : Transitions middle finalState) ->
  InstalledTrace name key world error value nameEq keyEq selected left ->
  InstalledTrace name key world error value nameEq keyEq selected right ->
  InstalledTrace name key world error value nameEq keyEq selected
    (appendTransitions left right)
appendInstalledTrace NoTransitions right (InstalledEnd installed) rightInstalled =
  rightInstalled
appendInstalledTrace
  (MoreTransitions (Fired nameEq keyEq action tag equation) rest) right
  (InstalledStep action tag equation rest sourceInstalled tailInstalled)
  rightInstalled =
    InstalledStep action tag equation (appendTransitions rest right)
      sourceInstalled
      (appendInstalledTrace rest right tailInstalled rightInstalled)

public export
data InstalledEnding :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {first, last : SystemState name key value world error} ->
  Transitions first last -> Type where
  EntireTraceInstalled :
    InstalledTrace name key world error value nameEq keyEq selected trace ->
    InstalledEnding name key world error value nameEq keyEq selected trace
  LastOpening :
    (preStart, opened : SystemState name key value world error) ->
    (beforeOpening : Transitions first preStart) ->
    (opening : BeginStep nameEq keyEq selected preStart opened) ->
    (afterOpening : Transitions opened last) ->
    appendTransitions beforeOpening
      (MoreTransitions (beginTransition opening) afterOpening) = trace ->
    InstalledTrace name key world error value nameEq keyEq selected afterOpening ->
    InstalledEnding name key world error value nameEq keyEq selected trace

0 unloadTargetUninstalled :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  UnloadStep nameEq keyEq selected before afterState ->
  installedAt @{nameEq} selected afterState = False
unloadTargetUninstalled nameEq keyEq selected before afterState closing =
  case lUnloadBoundary nameEq keyEq selected before afterState LUnloadTag
    (checkedActionProjects nameEq keyEq (LUnload selected) before afterState
      LUnloadTag (unloadEquation closing)) of
    (tagShape, sourceTrue, targetFalse) => targetFalse

0 installedEnding :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (trace : Transitions first last) ->
  AlignedTransitions name key world error value nameEq keyEq trace ->
  installedAt @{nameEq} selected last = True ->
  InstalledEnding name key world error value nameEq keyEq selected trace
installedEnding nameEq keyEq selected NoTransitions AlignedEnd endpointTrue =
  EntireTraceInstalled (InstalledEnd endpointTrue)
installedEnding nameEq keyEq selected
  trace@(MoreTransitions (Fired nameEq keyEq action tag equation) rest)
  (AlignedStep action tag equation rest alignedRest) endpointTrue =
  case installedEnding nameEq keyEq selected rest alignedRest endpointTrue of
    LastOpening preStart opened beforeOpening opening afterOpening split
      installedAfter =>
        LastOpening preStart opened
          (MoreTransitions (Fired nameEq keyEq action tag equation) beforeOpening)
          opening afterOpening
          (cong (MoreTransitions (Fired nameEq keyEq action tag equation)) split)
          installedAfter
    EntireTraceInstalled installedRest =>
      case installationEvolutionStep nameEq keyEq selected action tag _ _ equation of
        RemainedInstalled sourceTrue targetTrue =>
          EntireTraceInstalled
            (InstalledStep action tag equation rest sourceTrue installedRest)
        OpenedInstallation =>
          LastOpening _ _ NoTransitions (MkBeginStep equation) rest Refl installedRest
        RemainedUninstalled sourceFalse targetFalse =>
          let targetTrue = installedTraceStart installedRest
          in void (falseNotTrue (trans (sym targetFalse) targetTrue))
        ClosedInstallation =>
          let targetFalse = case lUnloadBoundary nameEq keyEq selected _ _
                LUnloadTag (checkedActionProjects nameEq keyEq (LUnload selected)
                  _ _ LUnloadTag equation) of
                (tagShape, sourceTrue, targetFalse) => targetFalse
              targetTrue = installedTraceStart installedRest
          in void (falseNotTrue (trans (sym targetFalse) targetTrue))
  where
  falseNotTrue : False = True -> Void
  falseNotTrue Refl impossible

public export
record LastOpeningResult
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (selected : name)
  {first, last : SystemState name key value world error}
  (trace : Transitions first last) where
  constructor MkLastOpeningResult
  openingPreStart : SystemState name key value world error
  openingStart : SystemState name key value world error
  traceBeforeLastOpening : Transitions first openingPreStart
  lastOpeningStep : BeginStep nameEq keyEq selected openingPreStart openingStart
  traceAfterLastOpening : Transitions openingStart last
  openingSplit : appendTransitions traceBeforeLastOpening
    (MoreTransitions (beginTransition lastOpeningStep) traceAfterLastOpening) = trace
  afterOpeningInstalled : InstalledTrace name key world error value nameEq keyEq
    selected traceAfterLastOpening

public export
0 extractLastOpening :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (trace : Transitions first last) ->
  AlignedTransitions name key world error value nameEq keyEq trace ->
  installedAt @{nameEq} selected first = False ->
  installedAt @{nameEq} selected last = True ->
  LastOpeningResult name key world error value nameEq keyEq selected trace
extractLastOpening nameEq keyEq selected trace aligned sourceFalse targetTrue =
  case installedEnding nameEq keyEq selected trace aligned targetTrue of
    LastOpening preStart opened before opening after split installedAfter =>
      MkLastOpeningResult preStart opened before opening after split installedAfter
    EntireTraceInstalled installedTrace =>
      let sourceTrue = installedTraceStart installedTrace in
      void (falseNotTrue (trans (sym sourceFalse) sourceTrue))
  where
  falseNotTrue : False = True -> Void
  falseNotTrue Refl impossible

public export
record FirstClosingResult
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (selected : name)
  {first, last : SystemState name key value world error}
  (trace : Transitions first last) where
  constructor MkFirstClosingResult
  closingBefore : SystemState name key value world error
  closingAfter : SystemState name key value world error
  traceBeforeFirstClosing : Transitions first closingBefore
  beforeClosingInstalled : InstalledTrace name key world error value nameEq keyEq
    selected traceBeforeFirstClosing
  firstClosingStep : UnloadStep nameEq keyEq selected closingBefore closingAfter
  traceAfterFirstClosing : Transitions closingAfter last
  closingSplit : appendTransitions traceBeforeFirstClosing
    (MoreTransitions (unloadTransition firstClosingStep) traceAfterFirstClosing) = trace

public export
0 extractFirstClosing :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (trace : Transitions first last) ->
  AlignedTransitions name key world error value nameEq keyEq trace ->
  installedAt @{nameEq} selected first = True ->
  installedAt @{nameEq} selected last = False ->
  FirstClosingResult name key world error value nameEq keyEq selected trace
extractFirstClosing nameEq keyEq selected NoTransitions AlignedEnd sourceTrue
  targetFalse = void (falseNotTrue (trans (sym targetFalse) sourceTrue))
  where
  falseNotTrue : False = True -> Void
  falseNotTrue Refl impossible
extractFirstClosing nameEq keyEq selected
  trace@(MoreTransitions (Fired nameEq keyEq action tag equation) rest)
  (AlignedStep action tag equation rest alignedRest) sourceTrue targetFalse =
  case installationEvolutionStep nameEq keyEq selected action tag _ _ equation of
    ClosedInstallation =>
      MkFirstClosingResult _ _ NoTransitions (InstalledEnd sourceTrue)
        (MkUnloadStep equation) rest Refl
    RemainedInstalled stepSource stepTarget =>
      case extractFirstClosing nameEq keyEq selected rest alignedRest stepTarget
        targetFalse of
        MkFirstClosingResult closeBefore closeAfter beforeClosing installedBefore
          closing afterClosing split =>
            MkFirstClosingResult closeBefore closeAfter
              (MoreTransitions (Fired nameEq keyEq action tag equation) beforeClosing)
              (InstalledStep action tag equation beforeClosing stepSource installedBefore)
              closing afterClosing
              (cong (MoreTransitions (Fired nameEq keyEq action tag equation)) split)
    RemainedUninstalled stepSource stepTarget =>
      void (falseNotTrue (trans (sym stepSource) sourceTrue))
    OpenedInstallation =>
      case lBeginBoundary nameEq keyEq selected _ _ LBeginTag equation of
        (tagShape, openingSourceFalse, openingTargetTrue) =>
          void (falseNotTrue (trans (sym openingSourceFalse) sourceTrue))
  where
  falseNotTrue : False = True -> Void
  falseNotTrue Refl impossible
