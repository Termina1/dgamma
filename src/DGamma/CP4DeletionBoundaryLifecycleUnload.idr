module DGamma.CP4DeletionBoundaryLifecycleUnload

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP4DeletionBoundaryLifecycleCore
import DGamma.CP4DeletionControlCore
import Decidable.Equality

%default total

0 nothingNotJustLifecycleUnload : Nothing = Just item -> Void
nothingNotJustLifecycleUnload Refl impossible

||| Exact one-leaf L-Unload commutation.  Inactive deletion preserves the
||| reliance guard; the same accumulator receives the same normalized local
||| state, so world, owned table, failure outcome, and Inactive control coincide.
public export
0 unloadOneDeleteRuntimeCommute :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  LifecycleOneDeleteCommuter name key world error value nameEq keyEq
    (the (Action name key value world error) (LUnload actor)) tag
unloadOneDeleteRuntimeCommute {name} {key} {world} {error} {value}
  nameEq keyEq actor ambient source removed removedComponent removedParent
  removedRetired removedTable removedOutcome removedFound removedNoChild
  actorDistinct sourceWellFormed raw
  with (lookupFiber @{nameEq} actor source) proof actorFound
  unloadOneDeleteRuntimeCommute nameEq keyEq actor ambient source removed
    removedComponent removedParent removedRetired removedTable removedOutcome
    removedFound removedNoChild actorDistinct sourceWellFormed raw | Nothing =
      void (nothingNotJustLifecycleUnload raw)
  unloadOneDeleteRuntimeCommute nameEq keyEq actor ambient source removed
    removedComponent removedParent removedRetired removedTable removedOutcome
    removedFound removedNoChild actorDistinct sourceWellFormed raw |
    Just actorFiber with (fiberLifecycle actorFiber) proof actorLife
    unloadOneDeleteRuntimeCommute nameEq keyEq actor ambient source removed
      removedComponent removedParent removedRetired removedTable removedOutcome
      removedFound removedNoChild actorDistinct sourceWellFormed raw |
      Just actorFiber | Inactive outcome =
        void (nothingNotJustLifecycleUnload raw)
    unloadOneDeleteRuntimeCommute nameEq keyEq actor ambient source removed
      removedComponent removedParent removedRetired removedTable removedOutcome
      removedFound removedNoChild actorDistinct sourceWellFormed raw |
      Just actorFiber | Reloading remaining accumulator view =
        void (nothingNotJustLifecycleUnload raw)
    unloadOneDeleteRuntimeCommute nameEq keyEq actor ambient source removed
      removedComponent removedParent removedRetired removedTable removedOutcome
      removedFound removedNoChild actorDistinct sourceWellFormed raw |
      Just actorFiber | Active accumulator view =
        void (nothingNotJustLifecycleUnload raw)
    unloadOneDeleteRuntimeCommute nameEq keyEq actor ambient source removed
      removedComponent removedParent removedRetired removedTable removedOutcome
      removedFound removedNoChild actorDistinct sourceWellFormed raw |
      Just actorFiber | Unloading accumulator view outcome
      with (relied @{nameEq} actor source) proof sourceRelied
      unloadOneDeleteRuntimeCommute nameEq keyEq actor ambient source removed
        removedComponent removedParent removedRetired removedTable removedOutcome
        removedFound removedNoChild actorDistinct sourceWellFormed raw |
        Just actorFiber | Unloading accumulator view outcome | True =
          void (nothingNotJustLifecycleUnload raw)
      unloadOneDeleteRuntimeCommute nameEq keyEq actor ambient source removed
        removedComponent removedParent removedRetired removedTable removedOutcome
        removedFound removedNoChild actorDistinct sourceWellFormed raw |
        Just actorFiber | Unloading accumulator view outcome | False =
          let replayFound = trans
                (lookupDeleteOther actor removed actorDistinct source) actorFound
              replayRelied = trans
                (reliedInactiveDelete nameEq actor removed removedComponent
                  removedParent removedRetired removedTable removedOutcome source
                  removedFound) sourceRelied
              0 replayRaw : (applyAction @{nameEq} @{keyEq}
                (the (Action name key value world error) (LUnload actor))
                (MkSystemState ambient (deleteBinding @{nameEq} removed source)) =
                Just (LUnloadTag,
                  MkSystemState
                    (localWorld (accumulator
                      (MkLocalState ambient
                        (restrictOwnedPreservingOrder @{keyEq}
                          (componentProvisions (fiberComponent actorFiber))
                          (ownedValues (fiberTable actorFiber))))))
                    (replaceBinding @{nameEq} actor
                      (setFiberRuntime actorFiber
                        (localTable (accumulator
                          (MkLocalState ambient
                            (restrictOwnedPreservingOrder @{keyEq}
                              (componentProvisions
                                (fiberComponent actorFiber))
                              (ownedValues (fiberTable actorFiber))))))
                        (Inactive outcome))
                      (deleteBinding @{nameEq} removed source))))
              replayRaw = rewrite replayFound in rewrite actorLife in
                rewrite replayRelied in Refl
          in case justInjective raw of
            Refl => replacementDeleteRuntimeCommute nameEq keyEq
              (LUnload actor) LUnloadTag actor removed actorDistinct ambient
              (localWorld (accumulator
                (MkLocalState ambient
                  (restrictOwnedPreservingOrder @{keyEq}
                    (componentProvisions (fiberComponent actorFiber))
                    (ownedValues (fiberTable actorFiber)))))) source
              (setFiberRuntime actorFiber
                (localTable (accumulator
                  (MkLocalState ambient
                    (restrictOwnedPreservingOrder @{keyEq}
                      (componentProvisions (fiberComponent actorFiber))
                      (ownedValues (fiberTable actorFiber))))))
                (Inactive outcome)) replayRaw
