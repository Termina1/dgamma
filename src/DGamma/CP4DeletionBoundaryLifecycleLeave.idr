module DGamma.CP4DeletionBoundaryLifecycleLeave

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP4DeletionBoundaryLifecycleCore
import DGamma.CP4DeletionControlCore
import Decidable.Equality

%default total

0 nothingNotJustLifecycleLeave : Nothing = Just item -> Void
nothingNotJustLifecycleLeave Refl impossible

||| Exact one-leaf L-Leave commutation.  Inactive deletion preserves the
||| active fiber's stale-target decision and exact Unloading control.
public export
0 leaveOneDeleteRuntimeCommute :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  LifecycleOneDeleteCommuter name key world error value nameEq keyEq
    (the (Action name key value world error) (LLeave actor)) tag
leaveOneDeleteRuntimeCommute {name} {key} {world} {error} {value}
  nameEq keyEq actor ambient source removed removedComponent removedParent
  removedRetired removedTable removedOutcome removedFound removedNoChild
  actorDistinct sourceWellFormed raw
  with (lookupFiber @{nameEq} actor source) proof actorFound
  leaveOneDeleteRuntimeCommute nameEq keyEq actor ambient source removed
    removedComponent removedParent removedRetired removedTable removedOutcome
    removedFound removedNoChild actorDistinct sourceWellFormed raw | Nothing =
      void (nothingNotJustLifecycleLeave raw)
  leaveOneDeleteRuntimeCommute nameEq keyEq actor ambient source removed
    removedComponent removedParent removedRetired removedTable removedOutcome
    removedFound removedNoChild actorDistinct sourceWellFormed raw |
    Just actorFiber with (fiberLifecycle actorFiber) proof actorLife
    leaveOneDeleteRuntimeCommute nameEq keyEq actor ambient source removed
      removedComponent removedParent removedRetired removedTable removedOutcome
      removedFound removedNoChild actorDistinct sourceWellFormed raw |
      Just actorFiber | Inactive outcome =
        void (nothingNotJustLifecycleLeave raw)
    leaveOneDeleteRuntimeCommute nameEq keyEq actor ambient source removed
      removedComponent removedParent removedRetired removedTable removedOutcome
      removedFound removedNoChild actorDistinct sourceWellFormed raw |
      Just actorFiber | Reloading remaining accumulator view =
        void (nothingNotJustLifecycleLeave raw)
    leaveOneDeleteRuntimeCommute nameEq keyEq actor ambient source removed
      removedComponent removedParent removedRetired removedTable removedOutcome
      removedFound removedNoChild actorDistinct sourceWellFormed raw |
      Just actorFiber | Unloading accumulator view outcome =
        void (nothingNotJustLifecycleLeave raw)
    leaveOneDeleteRuntimeCommute nameEq keyEq actor ambient source removed
      removedComponent removedParent removedRetired removedTable removedOutcome
      removedFound removedNoChild actorDistinct sourceWellFormed raw |
      Just actorFiber | Active accumulator view
      with (targetMatches @{nameEq}
        (targetFiber @{nameEq} @{keyEq} actorFiber source) view) proof matches
      leaveOneDeleteRuntimeCommute nameEq keyEq actor ambient source removed
        removedComponent removedParent removedRetired removedTable removedOutcome
        removedFound removedNoChild actorDistinct sourceWellFormed raw |
        Just actorFiber | Active accumulator view | True =
          void (nothingNotJustLifecycleLeave raw)
      leaveOneDeleteRuntimeCommute nameEq keyEq actor ambient source removed
        removedComponent removedParent removedRetired removedTable removedOutcome
        removedFound removedNoChild actorDistinct sourceWellFormed raw |
        Just actorFiber | Active accumulator view | False =
          let replayFound = trans
                (lookupDeleteOther actor removed actorDistinct source) actorFound
              replayTarget = targetFiberInactiveDelete nameEq keyEq actorFiber
                removed removedComponent removedParent removedRetired removedTable
                removedOutcome source removedFound
              0 replayRaw : (applyAction @{nameEq} @{keyEq}
                (the (Action name key value world error) (LLeave actor))
                (MkSystemState ambient (deleteBinding @{nameEq} removed source)) =
                Just (LLeaveTag, MkSystemState ambient
                  (replaceBinding @{nameEq} actor
                    (setFiberRuntime actorFiber (fiberTable actorFiber)
                      (Unloading accumulator view Nothing))
                    (deleteBinding @{nameEq} removed source))))
              replayRaw = rewrite replayFound in rewrite actorLife in
                rewrite replayTarget in rewrite matches in Refl
          in case justInjective raw of
            Refl => replacementDeleteRuntimeCommute nameEq keyEq
              (LLeave actor) LLeaveTag actor removed actorDistinct ambient ambient
              source (setFiberRuntime actorFiber (fiberTable actorFiber)
                (Unloading accumulator view Nothing)) replayRaw
