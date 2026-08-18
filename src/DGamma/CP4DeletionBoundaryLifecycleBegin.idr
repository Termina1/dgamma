module DGamma.CP4DeletionBoundaryLifecycleBegin

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP4DeletionBoundaryLifecycleCore
import DGamma.CP4DeletionControlCore
import Decidable.Equality

%default total

0 nothingNotJustLifecycleBegin : Nothing = Just item -> Void
nothingNotJustLifecycleBegin Refl impossible

||| Exact one-leaf L-Begin commutation.  The target view is unchanged by an
||| Inactive deletion, so both evaluators install the same Reloading control.
public export
0 beginOneDeleteRuntimeCommute :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  LifecycleOneDeleteCommuter name key world error value nameEq keyEq
    (the (Action name key value world error) (LBegin actor)) tag
beginOneDeleteRuntimeCommute {name} {key} {world} {error} {value}
  nameEq keyEq actor ambient source removed component parent retiredFlag table
  outcome removedFound removedNoChild actorDistinct sourceWellFormed raw
  with (lookupFiber @{nameEq} actor source) proof actorFound
  beginOneDeleteRuntimeCommute nameEq keyEq actor ambient source removed component
    parent retiredFlag table outcome removedFound removedNoChild actorDistinct
    sourceWellFormed raw | Nothing = void (nothingNotJustLifecycleBegin raw)
  beginOneDeleteRuntimeCommute nameEq keyEq actor ambient source removed component
    parent retiredFlag table outcome removedFound removedNoChild actorDistinct
    sourceWellFormed raw | Just actorFiber
    with (fiberLifecycle actorFiber) proof actorLife
    beginOneDeleteRuntimeCommute nameEq keyEq actor ambient source removed
      component parent retiredFlag table outcome removedFound removedNoChild
      actorDistinct sourceWellFormed raw | Just actorFiber | Inactive Nothing
      with (targetFiber @{nameEq} @{keyEq} actorFiber source) proof target
      beginOneDeleteRuntimeCommute nameEq keyEq actor ambient source removed
        component parent retiredFlag table outcome removedFound removedNoChild
        actorDistinct sourceWellFormed raw | Just actorFiber | Inactive Nothing |
        Nothing = void (nothingNotJustLifecycleBegin raw)
      beginOneDeleteRuntimeCommute nameEq keyEq actor ambient source removed
        component parent retiredFlag table outcome removedFound removedNoChild
        actorDistinct sourceWellFormed raw | Just actorFiber | Inactive Nothing |
        Just view =
          let replayFound = trans
                (lookupDeleteOther actor removed actorDistinct source) actorFound
              replayTarget = trans
                (targetFiberInactiveDelete nameEq keyEq actorFiber removed
                  component parent retiredFlag table outcome source removedFound)
                target
              0 replayRaw : (applyAction @{nameEq} @{keyEq}
                (the (Action name key value world error) (LBegin actor))
                (MkSystemState ambient (deleteBinding @{nameEq} removed source)) =
                Just (LBeginTag,
                  MkSystemState ambient
                    (replaceBinding @{nameEq} actor
                      (setFiberLifecycle actorFiber
                        (Reloading
                          (componentProgram (fiberComponent actorFiber))
                          (\local => local) view))
                      (deleteBinding @{nameEq} removed source))))
              replayRaw = rewrite replayFound in rewrite actorLife in
                rewrite replayTarget in Refl
          in case justInjective raw of
            Refl => replacementDeleteRuntimeCommute nameEq keyEq
              (LBegin actor) LBeginTag actor removed actorDistinct ambient ambient
              source
              (setFiberLifecycle actorFiber
                (Reloading (componentProgram (fiberComponent actorFiber))
                  (\local => local) view)) replayRaw
    beginOneDeleteRuntimeCommute nameEq keyEq actor ambient source removed
      component parent retiredFlag table outcome removedFound removedNoChild
      actorDistinct sourceWellFormed raw | Just actorFiber |
      Inactive (Just failure) = void (nothingNotJustLifecycleBegin raw)
    beginOneDeleteRuntimeCommute nameEq keyEq actor ambient source removed
      component parent retiredFlag table outcome removedFound removedNoChild
      actorDistinct sourceWellFormed raw | Just actorFiber |
      Reloading remaining accumulator view =
        void (nothingNotJustLifecycleBegin raw)
    beginOneDeleteRuntimeCommute nameEq keyEq actor ambient source removed
      component parent retiredFlag table outcome removedFound removedNoChild
      actorDistinct sourceWellFormed raw | Just actorFiber |
      Active accumulator view = void (nothingNotJustLifecycleBegin raw)
    beginOneDeleteRuntimeCommute nameEq keyEq actor ambient source removed
      component parent retiredFlag table outcome removedFound removedNoChild
      actorDistinct sourceWellFormed raw | Just actorFiber |
      Unloading accumulator view failure =
        void (nothingNotJustLifecycleBegin raw)
