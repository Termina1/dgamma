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
