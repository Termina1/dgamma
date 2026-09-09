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
