module DGamma.L2R5RetirementFrame

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import Data.List
import Decidable.Equality

%default total
%unbound_implicits off

||| Executable equality observation on two optional resolver views over the
||| SAME dependency list. This Bool is an observation, not an equality proof.
public export
sameOptionalView : {name, key : Type} -> {deps : List key} ->
  (nameEq : DecEq name) -> Maybe (View name deps) -> Maybe (View name deps) -> Bool
sameOptionalView nameEq Nothing Nothing = True
sameOptionalView nameEq Nothing (Just right) = False
sameOptionalView nameEq (Just left) Nothing = False
sameOptionalView nameEq (Just left) (Just right) = viewEq @{nameEq} left right

||| Retirement-provider observations at an ACTUAL source and its native
||| replacement registry. Every Bool has its defining equation. Intersecting
||| declared keys do not imply a resolver change: retirement retains tables
||| and activity. No field assumes unchanged views or a replayed lifecycle edge.
public export
record RetirementProviderFrame
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (child, parent, actor : name)
  (childFiber, actorFiber : Fiber name key value world error)
  (source : Registry name key value world error) where
  constructor MkRetirementProviderFrame
  0 frameChildFound : lookupFiber {name} {key} {value} {world} {error} @{nameEq} child source = Just childFiber
  0 frameOwnChild : fiberParent childFiber = ChildOf parent
  0 frameActorFound : lookupFiber {name} {key} {value} {world} {error} @{nameEq} actor source = Just actorFiber
  childRetiredObserved : Bool
  0 childRetiredEquation : retired childFiber = childRetiredObserved
  childActiveObserved : Bool
  0 childActiveEquation : isActive (fiberLifecycle childFiber) = childActiveObserved
  actorRetiredObserved : Bool
  0 actorRetiredEquation : retired actorFiber = actorRetiredObserved
  declaredIntersects : Bool
  0 declaredIntersectsEquation : provisionOverlap @{keyEq}
    (componentProvisions (fiberComponent childFiber))
    (componentDependencies (fiberComponent actorFiber)) = declaredIntersects
  resolverBefore : Maybe (View name (dependencies (componentDependencies (fiberComponent actorFiber))))
  resolverAfter : Maybe (View name (dependencies (componentDependencies (fiberComponent actorFiber))))
  0 resolverBeforeEquation : resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (dependencies (componentDependencies (fiberComponent actorFiber))) source = resolverBefore
  0 resolverAfterEquation : resolveView {name} {key} {value} {world} {error} @{nameEq} @{keyEq}
    (dependencies (componentDependencies (fiberComponent actorFiber)))
    (replaceBinding @{nameEq} child (retireFiber childFiber) source) = resolverAfter
  resolverChanged : Bool
  0 resolverChangedEquation : not (sameOptionalView nameEq resolverBefore resolverAfter) = resolverChanged
