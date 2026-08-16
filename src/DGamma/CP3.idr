module DGamma.CP3

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
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
