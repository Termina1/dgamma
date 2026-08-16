module DGamma.CP3

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import Data.List
import Data.List.Elem
import Data.Maybe
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
