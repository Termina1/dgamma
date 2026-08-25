module DGamma.R34RemoveChildOrientationNegative

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import Data.Maybe
import Decidable.Equality

%default total

||| Expected failure pin for O6 revision 34.  Even after splitting the three
||| executable guards and using the successful False-branch proof symmetrically,
||| elaboration does not identify the `hasChild` view with the tuple field.
0 removeChildOrientationProbe :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (afterState : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq} (ORemove actor)
    (MkSystemState ambient source) = Just (ORemoveTag, afterState) ->
  (oldFiber : Fiber name key value world error **
    (lookupFiber @{nameEq} {name = name} {key = key} {value = value}
       {world = world} {error = error} actor source = Just oldFiber,
     retired {name = name} {key = key} {value = value} {world = world}
       {error = error} oldFiber = True,
     isInactive (fiberLifecycle {name = name} {key = key} {value = value}
       {world = world} {error = error} oldFiber) = True,
     hasChild @{nameEq} {name = name} {key = key} {value = value}
       {world = world} {error = error} actor source = False,
     MkSystemState ambient (deleteBinding @{nameEq} actor source) = afterState))
removeChildOrientationProbe nameEq keyEq actor ambient source afterState raw
  with (lookupFiber @{nameEq} actor source) proof found
  removeChildOrientationProbe nameEq keyEq actor ambient source afterState raw |
    Nothing = case raw of Refl impossible
  removeChildOrientationProbe nameEq keyEq actor ambient source afterState raw |
    Just oldFiber with (retired oldFiber) proof retiredView
    removeChildOrientationProbe nameEq keyEq actor ambient source afterState raw |
      Just oldFiber | False = case raw of Refl impossible
    removeChildOrientationProbe nameEq keyEq actor ambient source afterState raw |
      Just oldFiber | True
      with (isInactive (fiberLifecycle oldFiber)) proof inactiveView
      removeChildOrientationProbe nameEq keyEq actor ambient source afterState raw |
        Just oldFiber | True | False = case raw of Refl impossible
      removeChildOrientationProbe nameEq keyEq actor ambient source afterState raw |
        Just oldFiber | True | True
        with (hasChild @{nameEq} actor source) proof childView
        removeChildOrientationProbe nameEq keyEq actor ambient source afterState raw |
          Just oldFiber | True | True | True = case raw of Refl impossible
        removeChildOrientationProbe nameEq keyEq actor ambient source afterState raw |
          Just oldFiber | True | True | False =
            case justInjective raw of
              Refl => (oldFiber ** (found, retiredView, inactiveView,
                sym childView, Refl))
