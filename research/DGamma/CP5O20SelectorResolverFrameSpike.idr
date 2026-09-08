module DGamma.CP5O20SelectorResolverFrameSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5O20SupportedReferenceSpike
import DGamma.CP5O19ActivationResolutionSpike
import DGamma.CP5O20RightOpeningTransportSpike
import DGamma.CP5O20BeginObservationSpike
import DGamma.CP4DeletionFrameCore
import DGamma.CP4DeletionSelectedForeignLifecycleCore
import Data.List.Elem
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| Supported-reference incomparability excludes actual declaration overlap.
||| This uses Equation62's declaration edge, not provider availability or a
||| fabricated resolver equality. Both reference lookups are authenticated.
export
0 o20IncomparableDeclarations :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (reference : SystemState name key value world error) -> (left, right : name) ->
  (leftFiber, rightFiber : Fiber name key value world error) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} left (registry reference) = Just leftFiber) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} right (registry reference) = Just rightFiber) ->
  (isSupported {name} {key} {value} {world} {error} @{nameEq} @{keyEq} left reference = True) ->
  (isSupported {name} {key} {value} {world} {error} @{nameEq} @{keyEq} right reference = True) ->
  Not (O20SupportedPath name key world error value nameEq keyEq reference left right) ->
  (wanted : key) -> Elem wanted (dependencies (componentDependencies (fiberComponent rightFiber))) ->
  Not (Elem wanted (dependencies (componentProvisions (fiberComponent leftFiber))))
o20IncomparableDeclarations nameEq keyEq reference left right leftFiber rightFiber leftFound rightFound leftSupported rightSupported noPath wanted needed provided =
  noPath (O20SupportedOne leftSupported rightSupported
    (SupportPrecedence (MkPrecedenceEdge wanted leftFiber rightFiber leftFound rightFound provided needed)))

||| ACTUAL surviving native update cannot change the incomparable consumer's
||| resolver. Only immutable component transport from the fixed reference is
||| explicit; no provider candidate, resolver frame or post-cut equality is.
export
0 o20IncomparableNativeResolver :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (reference : SystemState name key value world error) -> (right : name) ->
  (leftFiber, rightFiber : Fiber name key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} action before = Just (tag, afterState)) ->
  (old : Fiber name key value world error) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (actionOwner action) (registry before) = Just old) ->
  (isJust (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (actionOwner action) (registry afterState)) = True) ->
  (fiberComponent old = fiberComponent leftFiber) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (actionOwner action) (registry reference) = Just leftFiber) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} right (registry reference) = Just rightFiber) ->
  (isSupported {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (actionOwner action) reference = True) ->
  (isSupported {name} {key} {value} {world} {error} @{nameEq} @{keyEq} right reference = True) ->
  Not (O20SupportedPath name key world error value nameEq keyEq reference (actionOwner action) right) ->
  (resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (dependencies (componentDependencies (fiberComponent rightFiber))) (registry afterState) =
   resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (dependencies (componentDependencies (fiberComponent rightFiber))) (registry before))
o20IncomparableNativeResolver nameEq keyEq reference right leftFiber rightFiber before afterState action tag checked old oldFound survives static leftFound rightFound leftSupported rightSupported noPath =
  o19ResolvePresentLocalUpdate nameEq keyEq (dependencies (componentDependencies (fiberComponent rightFiber)))
    (actionOwner action) (registry before) (registry afterState) old oldFound survives
    (systemRegistryUpdate (applyActionLocalUpdate nameEq keyEq action before afterState tag
      (checkedActionProjects nameEq keyEq action before afterState tag checked)))
    (\wanted, needed, provided => o20IncomparableDeclarations nameEq keyEq reference (actionOwner action) right
      leftFiber rightFiber leftFound rightFound leftSupported rightSupported noPath wanted needed
      (replace {p = \component => Elem wanted (dependencies (componentProvisions component))} static provided))
