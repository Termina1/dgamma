module DGamma.CP5RetiredFlagEvaluationSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4Support
import Decidable.Equality

%default total
%unbound_implicits off

||| Operational result predicate for the precise retirement flag. Failure is
||| Unit, success owns actual lookup plus flag equality; not a success axiom.
0 RetiredResultOwner :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) ->
  (actor : name) -> (flag : Bool) -> Maybe (RuleTag, SystemState name key value world error) -> Type
RetiredResultOwner name key world error value nameEq actor flag Nothing = ()
RetiredResultOwner name key world error value nameEq actor flag (Just (tag, state)) =
  (fiber : Fiber name key value world error **
    (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
      @{nameEq} actor (registry state) = Just fiber, retired fiber = flag))

0 retiredResultOwnerReplace :
  (name, key, world, error : Type) -> (value : key -> Type) -> (nameEq : DecEq name) ->
  (actor : name) -> (flag : Bool) -> (source : Registry name key value world error) ->
  (old, next : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} actor source = Just old) -> (ambient : world) -> (tag : RuleTag) -> (retired next = flag) ->
  RetiredResultOwner name key world error value nameEq actor flag
    (Just (tag, MkSystemState ambient (replaceBinding @{nameEq} actor next source)))
retiredResultOwnerReplace name key world error value nameEq actor flag source old next found ambient tag exact =
  (next ** (lookupReplacedFiber @{nameEq} actor old next source found, exact))
