module DGamma.L2R5InsertObserved

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.L2R5Extensional
import Decidable.Equality

%default total
%unbound_implicits off

||| Supervisor-authorized NEW statement after A11: TWO explicit observed
||| decisions and equations, on actual inserted registries (not list heads).
||| Initial freshness produces both alternate freshness certificates by lookup
||| framing; this proves endpoint lookup algebra, not alternate checked edges.
export
0 insertedLookupTwoObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (wanted, root, child : name) ->
  (rootFiber, childFiber : Fiber name key value world error) ->
  (source : Registry name key value world error) ->
  (0 rootAbsent : lookupFiber {name} {key} {value} {world} {error} @{nameEq} root source = Nothing) ->
  (0 childAbsent : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child source = Nothing) ->
  (0 distinct : Not (root = child)) ->
  (d1 : Dec (wanted = root)) -> (0 e1 : decEq @{nameEq} wanted root = d1) ->
  (d2 : Dec (wanted = child)) -> (0 e2 : decEq @{nameEq} wanted child = d2) ->
  lookupFiber {name} {key} {value} {world} {error} @{nameEq} wanted
    (insertBinding @{nameEq} root rootFiber (insertBinding @{nameEq} child childFiber source childAbsent)
      (trans (lookupInsertOther @{nameEq} root child distinct childFiber source childAbsent) rootAbsent)) =
  lookupFiber {name} {key} {value} {world} {error} @{nameEq} wanted
    (insertBinding @{nameEq} child childFiber (insertBinding @{nameEq} root rootFiber source rootAbsent)
      (trans (lookupInsertOther @{nameEq} child root (\same => distinct (sym same)) rootFiber source rootAbsent) childAbsent))
insertedLookupTwoObserved nameEq wanted _ child rootFiber childFiber (MkCoeffectContext entries unique)
  rootAbsent childAbsent distinct (Yes Refl) e1 (Yes same) e2 = void (distinct same)
insertedLookupTwoObserved nameEq wanted _ child rootFiber childFiber (MkCoeffectContext entries unique)
  rootAbsent childAbsent distinct (Yes Refl) e1 (No different) e2 =
    rewrite e1 in rewrite e2 in rewrite e1 in Refl
insertedLookupTwoObserved nameEq wanted root _ rootFiber childFiber (MkCoeffectContext entries unique)
  rootAbsent childAbsent distinct (No different) e1 (Yes Refl) e2 =
    rewrite e1 in rewrite e2 in Refl
insertedLookupTwoObserved nameEq wanted root child rootFiber childFiber (MkCoeffectContext entries unique)
  rootAbsent childAbsent distinct (No notRoot) e1 (No notChild) e2 =
    rewrite e1 in rewrite e2 in rewrite e1 in Refl

||| Distinct fresh insertions have extensionally equal endpoints even though
||| prepending makes their ordered snapshots different. Both second freshness
||| equations are produced. Applicability/provision guards are NOT proved here.
export
0 freshInsertEndpointsExtensional :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (root, child : name) ->
  (rootFiber, childFiber : Fiber name key value world error) -> (ambient : world) ->
  (source : Registry name key value world error) ->
  (0 rootAbsent : lookupFiber {name} {key} {value} {world} {error} @{nameEq} root source = Nothing) ->
  (0 childAbsent : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child source = Nothing) ->
  (0 distinct : Not (root = child)) ->
  RegistryExtensional name key world error value nameEq
    (MkSystemState ambient (insertBinding @{nameEq} root rootFiber (insertBinding @{nameEq} child childFiber source childAbsent)
      (trans (lookupInsertOther @{nameEq} root child distinct childFiber source childAbsent) rootAbsent)))
    (MkSystemState ambient (insertBinding @{nameEq} child childFiber (insertBinding @{nameEq} root rootFiber source rootAbsent)
      (trans (lookupInsertOther @{nameEq} child root (\same => distinct (sym same)) rootFiber source rootAbsent) childAbsent)))
freshInsertEndpointsExtensional nameEq root child rootFiber childFiber ambient source rootAbsent childAbsent distinct =
  MkRegistryExtensional Refl (\wanted => insertedLookupTwoObserved nameEq wanted root child
    rootFiber childFiber source rootAbsent childAbsent distinct
    (decEq @{nameEq} wanted root) Refl (decEq @{nameEq} wanted child) Refl)
