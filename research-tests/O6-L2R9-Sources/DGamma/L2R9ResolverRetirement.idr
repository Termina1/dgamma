module DGamma.L2R9ResolverRetirement

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.L2R5RetirementFrame
import DGamma.L2R9ProviderRetirement
import Data.List
import Data.List.Elem
import Data.Maybe
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| One native resolver dependency step on an observed provider Maybe. This
||| is the induction step, not a caller-supplied whole resolver theorem.
export
0 resolveAtObservedProvider :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (wanted : key) -> (deps : List key) ->
  (before, after : Registry name key value world error) -> (observed : Maybe name) ->
  (0 beforeEquation : providerOf {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted before = observed) ->
  (0 afterEquation : providerOf {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted after = observed) ->
  (0 tail : resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq} deps before =
    resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq} deps after) ->
  resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (wanted :: deps) before =
  resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (wanted :: deps) after
resolveAtObservedProvider nameEq keyEq wanted deps before after Nothing beforeEquation afterEquation tail =
  rewrite beforeEquation in rewrite afterEquation in Refl
resolveAtObservedProvider {name} {key} nameEq keyEq wanted deps before after (Just provider) beforeEquation afterEquation tail =
  rewrite beforeEquation in rewrite afterEquation in
  cong (map (ProviderView {name} {k = wanted} {rest = deps} provider)) tail

||| GENERAL native resolver invariance for installed retirement. The list
||| proof D9 supplies each actual provider equality; D10 observes the actual
||| provider at its own call site. Structural induction on dependencies.
export
0 resolveRetirementEntries :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (deps : List key) -> (child : name) ->
  (fiber : Fiber name key value world error) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (0 unique : UniqueKeys (bindingKeys entries)) ->
  (0 found : lookupEntries {key = name} {value = FiberAt name key value world error} @{nameEq} child entries = Just fiber) ->
  resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq} deps (MkCoeffectContext entries unique) =
  resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq} deps
    (replaceBinding @{nameEq} child (retireFiber fiber) (MkCoeffectContext entries unique))
resolveRetirementEntries nameEq keyEq [] child fiber entries unique found = Refl
resolveRetirementEntries {name} {key} {world} {error} {value} nameEq keyEq (wanted :: deps) child fiber entries unique found =
  resolveAtObservedProvider nameEq keyEq wanted deps (MkCoeffectContext entries unique)
    (replaceBinding @{nameEq} child (retireFiber fiber) (MkCoeffectContext entries unique))
    (providerOf {name} {key} {value} {world} {error} @{nameEq} @{keyEq} wanted (MkCoeffectContext entries unique)) Refl
    (sym (providerRetirementEntries nameEq keyEq wanted child entries fiber found))
    (resolveRetirementEntries nameEq keyEq deps child fiber entries unique found)

||| GENERAL native plus observed resolver equality from an ACTUAL
||| RetirementProviderFrame. No resolver equality/changed=False oracle is an
||| input; only the existing authenticated lookup fields feed D11's fold.
||| This does NOT yet produce a lifecycle checked edge or its snapshot.
export
0 retirementFrameResolverSame :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (child, parent, actor : name) ->
  (childFiber, actorFiber : Fiber name key value world error) ->
  (source : Registry name key value world error) ->
  (frame : RetirementProviderFrame name key world error value nameEq keyEq child parent actor childFiber actorFiber source) ->
  (resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
      (dependencies (componentDependencies (fiberComponent actorFiber))) source =
    resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
      (dependencies (componentDependencies (fiberComponent actorFiber)))
      (replaceBinding @{nameEq} child (retireFiber childFiber) source),
   resolverBefore frame = resolverAfter frame)
retirementFrameResolverSame nameEq keyEq child parent actor childFiber actorFiber (MkCoeffectContext entries unique) frame =
  (resolveRetirementEntries nameEq keyEq (dependencies (componentDependencies (fiberComponent actorFiber)))
    child childFiber entries unique (frameChildFound frame),
   trans (sym (resolverBeforeEquation frame))
     (trans
       (resolveRetirementEntries nameEq keyEq (dependencies (componentDependencies (fiberComponent actorFiber)))
         child childFiber entries unique (frameChildFound frame))
       (resolverAfterEquation frame)))
