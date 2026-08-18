module DGamma.CP4DeletionBoundaryLifecycleDivert

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP4DeletionBoundaryLifecycleCore
import DGamma.CP4DeletionControlCore
import Decidable.Equality

%default total

0 nothingNotJustLifecycleDivert : Nothing = Just item -> Void
nothingNotJustLifecycleDivert Refl impossible

||| Exact one-leaf explicit L-Divert commutation.  Inactive deletion preserves
||| the stale-target decision and therefore the same Unloading control value.
public export
0 divertOneDeleteRuntimeCommute :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  LifecycleOneDeleteCommuter name key world error value nameEq keyEq
    (the (Action name key value world error) (LDivert actor)) tag
divertOneDeleteRuntimeCommute {name} {key} {world} {error} {value}
  nameEq keyEq actor ambient source removed removedComponent removedParent
  removedRetired removedTable removedOutcome removedFound removedNoChild
  actorDistinct sourceWellFormed raw
  with (lookupFiber @{nameEq} actor source) proof actorFound
  divertOneDeleteRuntimeCommute nameEq keyEq actor ambient source removed
    removedComponent removedParent removedRetired removedTable removedOutcome
    removedFound removedNoChild actorDistinct sourceWellFormed raw | Nothing =
      void (nothingNotJustLifecycleDivert raw)
  divertOneDeleteRuntimeCommute nameEq keyEq actor ambient source removed
    removedComponent removedParent removedRetired removedTable removedOutcome
    removedFound removedNoChild actorDistinct sourceWellFormed raw |
    Just actorFiber with (fiberLifecycle actorFiber) proof actorLife
    divertOneDeleteRuntimeCommute nameEq keyEq actor ambient source removed
      removedComponent removedParent removedRetired removedTable removedOutcome
      removedFound removedNoChild actorDistinct sourceWellFormed raw |
      Just actorFiber | Inactive outcome =
        void (nothingNotJustLifecycleDivert raw)
    divertOneDeleteRuntimeCommute nameEq keyEq actor ambient source removed
      removedComponent removedParent removedRetired removedTable removedOutcome
      removedFound removedNoChild actorDistinct sourceWellFormed raw |
      Just actorFiber | Active accumulator view =
        void (nothingNotJustLifecycleDivert raw)
    divertOneDeleteRuntimeCommute nameEq keyEq actor ambient source removed
      removedComponent removedParent removedRetired removedTable removedOutcome
      removedFound removedNoChild actorDistinct sourceWellFormed raw |
      Just actorFiber | Unloading accumulator view outcome =
        void (nothingNotJustLifecycleDivert raw)
    divertOneDeleteRuntimeCommute nameEq keyEq actor ambient source removed
      removedComponent removedParent removedRetired removedTable removedOutcome
      removedFound removedNoChild actorDistinct sourceWellFormed raw |
      Just actorFiber | Reloading remaining accumulator view
      with (targetMatches @{nameEq}
        (targetFiber @{nameEq} @{keyEq} actorFiber source) view) proof matches
      divertOneDeleteRuntimeCommute nameEq keyEq actor ambient source removed
        removedComponent removedParent removedRetired removedTable removedOutcome
        removedFound removedNoChild actorDistinct sourceWellFormed raw |
        Just actorFiber | Reloading remaining accumulator view | True =
          void (nothingNotJustLifecycleDivert raw)
      divertOneDeleteRuntimeCommute nameEq keyEq actor ambient source removed
        removedComponent removedParent removedRetired removedTable removedOutcome
        removedFound removedNoChild actorDistinct sourceWellFormed raw |
        Just actorFiber | Reloading remaining accumulator view | False =
          let replayFound = trans
                (lookupDeleteOther actor removed actorDistinct source) actorFound
              replayTarget = targetFiberInactiveDelete nameEq keyEq actorFiber
                removed removedComponent removedParent removedRetired removedTable
                removedOutcome source removedFound
              0 replayRaw : (applyAction @{nameEq} @{keyEq}
                (the (Action name key value world error) (LDivert actor))
                (MkSystemState ambient (deleteBinding @{nameEq} removed source)) =
                Just (LDivertTag, MkSystemState ambient
                  (replaceBinding @{nameEq} actor
                    (setFiberRuntime actorFiber (fiberTable actorFiber)
                      (Unloading accumulator view Nothing))
                    (deleteBinding @{nameEq} removed source))))
              replayRaw = rewrite replayFound in rewrite actorLife in
                rewrite replayTarget in rewrite matches in Refl
          in case justInjective raw of
            Refl => replacementDeleteRuntimeCommute nameEq keyEq
              (LDivert actor) LDivertTag actor removed actorDistinct ambient
              ambient source
              (setFiberRuntime actorFiber (fiberTable actorFiber)
                (Unloading accumulator view Nothing)) replayRaw
