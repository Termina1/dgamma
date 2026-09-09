module DGamma.L2R9ProviderRetirement

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.L2R9ProviderHead
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| NEW actual native replacement-head step, not the frozen bare provider
||| head statement. Source lookup authenticates the replaced fiber. The
||| observed name Dec either hits this head (D3/D5 provide the native head
||| fact) or preserves it and consumes a smaller-tail induction hypothesis.
||| The No branch observes the library provider guard with its OWN equation.
export
0 providerRetirementAtName :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (wanted : key) -> (child, current : name) ->
  (component : Component key value world error) -> (parent : Parent name) -> (flag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (lifecycle : Lifecycle key value world error name
    (dependencies (componentDependencies component)) (componentProvisions component)) ->
  (rest : List (Binding name (FiberAt name key value world error))) ->
  (0 tail : (fiber : Fiber name key value world error) ->
    (0 found : lookupEntries {key = name} {value = FiberAt name key value world error} @{nameEq} child rest = Just fiber) ->
    providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted rest =
    providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted (replaceEntries @{nameEq} child (retireFiber fiber) rest)) ->
  (decision : Dec (child = current)) -> (0 decisionEquation : decEq @{nameEq} child current = decision) ->
  (fiber : Fiber name key value world error) ->
  (0 found : lookupEntries {key = name} {value = FiberAt name key value world error} @{nameEq} child
    (Bind current (MkFiber component parent flag table lifecycle) :: rest) = Just fiber) ->
  providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted
    (Bind current (MkFiber component parent flag table lifecycle) :: rest) =
  providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted
    (replaceEntries @{nameEq} child (retireFiber fiber) (Bind current (MkFiber component parent flag table lifecycle) :: rest))
providerRetirementAtName {name} {key} {world} {error} {value} nameEq keyEq wanted child _
  component parent flag table lifecycle rest tail (Yes Refl) decisionEquation fiber found =
  rewrite decisionEquation in
  replace {p = \replacement =>
    providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted
      (Bind child (MkFiber component parent flag table lifecycle) :: rest) =
    providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted
      (Bind child (retireFiber replacement) :: rest)}
    (justInjective (trans (sym (the
      (lookupEntries {key = name} {value = FiberAt name key value world error} @{nameEq} child
        (Bind child (MkFiber component parent flag table lifecycle) :: rest) = Just (MkFiber component parent flag table lifecycle))
      (rewrite decisionEquation in Refl))) found))
    (laneProviderHeadSame nameEq keyEq wanted child component parent flag table lifecycle rest
      (laneProviderHeadObserved nameEq keyEq wanted child component parent flag table lifecycle rest))
providerRetirementAtName {name} {key} {world} {error} {value} nameEq keyEq wanted child current
  component parent flag table lifecycle rest tail (No different) decisionEquation fiber found =
  rewrite decisionEquation in
  laneObservedBoolEliminate
    (\observed => (0 shape : (isActive lifecycle && memberKey @{keyEq} wanted (ownedValues table)) = observed) ->
      providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted
        (Bind current (MkFiber component parent flag table lifecycle) :: rest) =
      providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted
        (Bind current (MkFiber component parent flag table lifecycle) :: replaceEntries @{nameEq} child (retireFiber fiber) rest))
    (\shape => rewrite shape in tail fiber
      (trans (sym (the
        (lookupEntries {key = name} {value = FiberAt name key value world error} @{nameEq} child
          (Bind current (MkFiber component parent flag table lifecycle) :: rest) =
         lookupEntries {key = name} {value = FiberAt name key value world error} @{nameEq} child rest)
        (rewrite decisionEquation in Refl))) found))
    (\shape => rewrite shape in Refl)
    (isActive lifecycle && memberKey @{keyEq} wanted (ownedValues table)) Refl

||| Expose this ACTUAL head fiber once; the name Dec is observed at this
||| own call site, then D7 handles one replacement step using native evidence.
export
0 providerRetirementAtHead :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (wanted : key) -> (child, current : name) ->
  (head : Fiber name key value world error) ->
  (rest : List (Binding name (FiberAt name key value world error))) ->
  (0 tail : (fiber : Fiber name key value world error) ->
    (0 found : lookupEntries {key = name} {value = FiberAt name key value world error} @{nameEq} child rest = Just fiber) ->
    providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted rest =
    providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted (replaceEntries @{nameEq} child (retireFiber fiber) rest)) ->
  (fiber : Fiber name key value world error) ->
  (0 found : lookupEntries {key = name} {value = FiberAt name key value world error} @{nameEq} child
    (Bind current head :: rest) = Just fiber) ->
  providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted (Bind current head :: rest) =
  providerIn {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted
    (replaceEntries @{nameEq} child (retireFiber fiber) (Bind current head :: rest))
providerRetirementAtHead nameEq keyEq wanted child current (MkFiber component parent flag table lifecycle) rest tail fiber found =
  providerRetirementAtName nameEq keyEq wanted child current component parent flag table lifecycle rest tail
    (decEq @{nameEq} child current) Refl fiber found
