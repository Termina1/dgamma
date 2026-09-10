module DGamma.CP5O20SelectorResolverFrameSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5O20SupportedReferenceSpike
import DGamma.CP5O19ActivationResolutionSpike
import DGamma.CP5O20RightOpeningTransportSpike
import DGamma.CP5O20BeginObservationSpike
import DGamma.CP5RankedEarlyApplicabilitySpike
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

||| Backward checked Begin across an actual incomparable native update. The
||| owner frame and resolver are BOTH derived, not input. This one-edge
||| transport still requires exact immutable reference components and owner
||| survival; whole-block extraction of those facts is a separate obligation.
export
0 o20IncomparableEarlierBegin :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (reference : SystemState name key value world error) -> (right : name) ->
  (leftFiber, rightFiber : Fiber name key value world error) ->
  (before, middle, rightAfter : SystemState name key value world error) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (checkedApplyAction {name} {key} {value} {world} {error} @{nameEq} @{keyEq} action before = Just (tag, middle)) ->
  (observation : O20BeginObservation name key world error value nameEq keyEq right middle rightAfter) ->
  (old : Fiber name key value world error) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (actionOwner action) (registry before) = Just old) ->
  (isJust (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (actionOwner action) (registry middle)) = True) ->
  (fiberComponent old = fiberComponent leftFiber) ->
  (fiberComponent rightFiber = beginObservedComponent observation) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} (actionOwner action) (registry reference) = Just leftFiber) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} right (registry reference) = Just rightFiber) ->
  (isSupported {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (actionOwner action) reference = True) ->
  (isSupported {name} {key} {value} {world} {error} @{nameEq} @{keyEq} right reference = True) ->
  Not (O20SupportedPath name key world error value nameEq keyEq reference (actionOwner action) right) ->
  Not (right = actionOwner action) -> (registryWellFormed @{nameEq} @{keyEq} before = True) ->
  CheckedEarlyApplication name key world error value nameEq keyEq before (LBegin right) LBeginTag
o20IncomparableEarlierBegin {name} {key} {value} {world} {error} nameEq keyEq reference right leftFiber rightFiber before middle rightAfter action tag checked observation old oldFound survives leftStatic rightStatic leftFound rightFound leftSupported rightSupported noPath distinct wellFormed =
  o20RightBeginAtEarlierObservation nameEq keyEq right before middle rightAfter observation wellFormed
    (sym (systemLocalUpdateForeign nameEq right (actionOwner action) distinct before middle
      (applyActionLocalUpdate nameEq keyEq action before middle tag
        (checkedActionProjects nameEq keyEq action before middle tag checked))))
    (replace {p = \component =>
      (resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (dependencies (componentDependencies component)) (registry before) =
       resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq} (dependencies (componentDependencies component)) (registry middle))}
      rightStatic (sym (o20IncomparableNativeResolver nameEq keyEq reference right leftFiber rightFiber before middle action tag checked old oldFound survives leftStatic leftFound rightFound leftSupported rightSupported noPath)))
