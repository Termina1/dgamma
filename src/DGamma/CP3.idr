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
  (before, afterState : SystemState name key value world error) -> Type where
  RemainedUninstalled :
    installedAt @{nameEq} selected before = False ->
    installedAt @{nameEq} selected afterState = False ->
    InstallationEvolution name key world error value nameEq keyEq selected
      before afterState
  RemainedInstalled :
    installedAt @{nameEq} selected before = True ->
    installedAt @{nameEq} selected afterState = True ->
    InstallationEvolution name key world error value nameEq keyEq selected
      before afterState
  OpenedInstallation : BeginStep nameEq keyEq selected before afterState ->
    InstallationEvolution name key world error value nameEq keyEq selected
      before afterState
  ClosedInstallation : UnloadStep nameEq keyEq selected before afterState ->
    InstallationEvolution name key world error value nameEq keyEq selected
      before afterState

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
    before afterState
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
