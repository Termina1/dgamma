module DGamma.CP4DeletionBoundaryLifecycleAdvance

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP4DeletionBoundaryLifecycleCore
import DGamma.CP4DeletionControlCore
import Decidable.Equality

%default total

0 nothingNotJustLifecycleAdvance : Nothing = Just item -> Void
nothingNotJustLifecycleAdvance Refl impossible

0 boolAndLeftAdvance : (left, right : Bool) -> left && right = True -> left = True
boolAndLeftAdvance False right valid = case valid of Refl impossible
boolAndLeftAdvance True right valid = Refl

0 reloadingProvidersValidAdvance :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (fiber : Fiber name key value world error) ->
  (remaining : List (StepEffect key value world error
    (dependencies (componentDependencies (fiberComponent fiber)))
    (componentProvisions (fiberComponent fiber)))) ->
  (accumulator : LocalState key value world
      (componentProvisions (fiberComponent fiber)) ->
    LocalState key value world
      (componentProvisions (fiberComponent fiber))) ->
  (view : View name
    (dependencies (componentDependencies (fiberComponent fiber)))) ->
  (source : Registry name key value world error) ->
  fiberLifecycle fiber = Reloading remaining accumulator view ->
  fiberViewInvariant @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} fiber source = True ->
  viewProvidersInvariant @{nameEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} source view = True
reloadingProvidersValidAdvance nameEq keyEq
  (MkFiber component parent retiredFlag table (Inactive outcome)) remaining
  accumulator view source life valid = case life of Refl impossible
reloadingProvidersValidAdvance nameEq keyEq
  (MkFiber component parent retiredFlag table
    (Reloading actualRemaining actualAccumulator actualView)) remaining
  accumulator view source life valid = case life of
    Refl => boolAndLeftAdvance _ _ valid
reloadingProvidersValidAdvance nameEq keyEq
  (MkFiber component parent retiredFlag table (Active actualAccumulator actualView))
  remaining accumulator view source life valid = case life of Refl impossible
reloadingProvidersValidAdvance nameEq keyEq
  (MkFiber component parent retiredFlag table
    (Unloading actualAccumulator actualView actualOutcome)) remaining accumulator
  view source life valid = case life of Refl impossible

||| Exact one-leaf L-Advance commutation, including empty finish/divert,
||| failure, iterator, effectful finish, and landing-divert branches.
public export
0 advanceOneDeleteRuntimeCommute :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  LifecycleOneDeleteCommuter name key world error value nameEq keyEq
    (the (Action name key value world error) (LAdvance actor)) tag
advanceOneDeleteRuntimeCommute {name} {key} {world} {error} {value}
  nameEq keyEq actor ambient source removed removedComponent removedParent
  removedRetired removedTable removedOutcome removedFound removedNoChild
  actorDistinct sourceWellFormed raw
  with (lookupFiber @{nameEq} actor source) proof actorFound
  advanceOneDeleteRuntimeCommute nameEq keyEq actor ambient source removed
    removedComponent removedParent removedRetired removedTable removedOutcome
    removedFound removedNoChild actorDistinct sourceWellFormed raw | Nothing =
      void (nothingNotJustLifecycleAdvance raw)
  advanceOneDeleteRuntimeCommute nameEq keyEq actor ambient source removed
    removedComponent removedParent removedRetired removedTable removedOutcome
    removedFound removedNoChild actorDistinct sourceWellFormed raw |
    Just actorFiber with (fiberLifecycle actorFiber) proof actorLife
    advanceOneDeleteRuntimeCommute nameEq keyEq actor ambient source removed
      removedComponent removedParent removedRetired removedTable removedOutcome
      removedFound removedNoChild actorDistinct sourceWellFormed raw |
      Just actorFiber | Inactive outcome =
        void (nothingNotJustLifecycleAdvance raw)
    advanceOneDeleteRuntimeCommute nameEq keyEq actor ambient source removed
      removedComponent removedParent removedRetired removedTable removedOutcome
      removedFound removedNoChild actorDistinct sourceWellFormed raw |
      Just actorFiber | Active accumulator view =
        void (nothingNotJustLifecycleAdvance raw)
    advanceOneDeleteRuntimeCommute nameEq keyEq actor ambient source removed
      removedComponent removedParent removedRetired removedTable removedOutcome
      removedFound removedNoChild actorDistinct sourceWellFormed raw |
      Just actorFiber | Unloading accumulator view outcome =
        void (nothingNotJustLifecycleAdvance raw)
    advanceOneDeleteRuntimeCommute nameEq keyEq actor ambient source removed
      removedComponent removedParent removedRetired removedTable removedOutcome
      removedFound removedNoChild actorDistinct sourceWellFormed raw |
      Just actorFiber | Reloading [] accumulator view
      with (targetMatches @{nameEq}
        (targetFiber @{nameEq} @{keyEq} actorFiber source) view) proof matches
      advanceOneDeleteRuntimeCommute nameEq keyEq actor ambient source removed
        removedComponent removedParent removedRetired removedTable removedOutcome
        removedFound removedNoChild actorDistinct sourceWellFormed raw |
        Just actorFiber | Reloading [] accumulator view | True =
          let replayFound = trans
                (lookupDeleteOther actor removed actorDistinct source) actorFound
              replayTarget = targetFiberInactiveDelete nameEq keyEq actorFiber
                removed removedComponent removedParent removedRetired removedTable
                removedOutcome source removedFound
              0 replayRaw : (applyAction @{nameEq} @{keyEq}
                (the (Action name key value world error) (LAdvance actor))
                (MkSystemState ambient (deleteBinding @{nameEq} removed source)) =
                Just (LFinishTag, MkSystemState ambient
                  (replaceBinding @{nameEq} actor
                    (setFiberRuntime actorFiber (fiberTable actorFiber)
                      (Active accumulator view))
                    (deleteBinding @{nameEq} removed source))))
              replayRaw = rewrite replayFound in rewrite actorLife in
                rewrite replayTarget in rewrite matches in Refl
          in case justInjective raw of
            Refl => replacementDeleteRuntimeCommute nameEq keyEq
              (LAdvance actor) LFinishTag actor removed actorDistinct ambient
              ambient source
              (setFiberRuntime actorFiber (fiberTable actorFiber)
                (Active accumulator view)) replayRaw
      advanceOneDeleteRuntimeCommute nameEq keyEq actor ambient source removed
        removedComponent removedParent removedRetired removedTable removedOutcome
        removedFound removedNoChild actorDistinct sourceWellFormed raw |
        Just actorFiber | Reloading [] accumulator view | False =
          let replayFound = trans
                (lookupDeleteOther actor removed actorDistinct source) actorFound
              replayTarget = targetFiberInactiveDelete nameEq keyEq actorFiber
                removed removedComponent removedParent removedRetired removedTable
                removedOutcome source removedFound
              0 replayRaw : (applyAction @{nameEq} @{keyEq}
                (the (Action name key value world error) (LAdvance actor))
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
              (LAdvance actor) LDivertTag actor removed actorDistinct ambient
              ambient source
              (setFiberRuntime actorFiber (fiberTable actorFiber)
                (Unloading accumulator view Nothing)) replayRaw
    advanceOneDeleteRuntimeCommute nameEq keyEq actor ambient source removed
      removedComponent removedParent removedRetired removedTable removedOutcome
      removedFound removedNoChild actorDistinct sourceWellFormed raw |
      Just actorFiber | Reloading (step :: rest) accumulator view
      with (resolveCommittedValues @{nameEq} @{keyEq}
        (dependencies (componentDependencies (fiberComponent actorFiber))) view
        source) proof resolved
      advanceOneDeleteRuntimeCommute nameEq keyEq actor ambient source removed
        removedComponent removedParent removedRetired removedTable removedOutcome
        removedFound removedNoChild actorDistinct sourceWellFormed raw |
        Just actorFiber | Reloading (step :: rest) accumulator view | Nothing =
          void (nothingNotJustLifecycleAdvance raw)
      advanceOneDeleteRuntimeCommute nameEq keyEq actor ambient source removed
        removedComponent removedParent removedRetired removedTable removedOutcome
        removedFound removedNoChild actorDistinct sourceWellFormed raw |
        Just actorFiber | Reloading (step :: rest) accumulator view |
        Just capability
        with (runStepEffect step capability
          (MkLocalState ambient
            (restrictOwnedPreservingOrder @{keyEq}
              (componentProvisions (fiberComponent actorFiber))
              (ownedValues (fiberTable actorFiber))))) proof ran
        advanceOneDeleteRuntimeCommute nameEq keyEq actor ambient source removed
          removedComponent removedParent removedRetired removedTable
          removedOutcome removedFound removedNoChild actorDistinct
          sourceWellFormed raw | Just actorFiber |
          Reloading (step :: rest) accumulator view | Just capability |
          Left failure =
            let actorView = wellFormedFiberView nameEq keyEq actor
                  (MkSystemState ambient source) actorFiber actorFound
                  sourceWellFormed
                providersValid = reloadingProvidersValidAdvance nameEq keyEq
                  actorFiber (step :: rest) accumulator view source actorLife
                  actorView
                replayResolved = trans
                  (resolveCommittedValuesInactiveDelete nameEq keyEq
                    (dependencies
                      (componentDependencies (fiberComponent actorFiber))) view
                    removed removedComponent removedParent removedRetired
                    removedTable removedOutcome source removedFound providersValid)
                  resolved
                replayFound = trans
                  (lookupDeleteOther actor removed actorDistinct source) actorFound
                0 replayRaw : (applyAction @{nameEq} @{keyEq}
                  (the (Action name key value world error) (LAdvance actor))
                  (MkSystemState ambient
                    (deleteBinding @{nameEq} removed source)) =
                  Just (LRaiseTag, MkSystemState ambient
                    (replaceBinding @{nameEq} actor
                      (setFiberRuntime actorFiber (fiberTable actorFiber)
                        (Unloading accumulator view (Just failure)))
                      (deleteBinding @{nameEq} removed source))))
                replayRaw = rewrite replayFound in rewrite actorLife in
                  rewrite replayResolved in rewrite ran in Refl
            in case justInjective raw of
              Refl => replacementDeleteRuntimeCommute nameEq keyEq
                (LAdvance actor) LRaiseTag actor removed actorDistinct ambient
                ambient source
                (setFiberRuntime actorFiber (fiberTable actorFiber)
                  (Unloading accumulator view (Just failure))) replayRaw
        advanceOneDeleteRuntimeCommute nameEq keyEq actor ambient source removed
          removedComponent removedParent removedRetired removedTable
          removedOutcome removedFound removedNoChild actorDistinct
          sourceWellFormed raw | Just actorFiber |
          Reloading (step :: rest) accumulator view | Just capability |
          Right (localAfter, undo)
          with (targetMatches @{nameEq}
            (targetFiber @{nameEq} @{keyEq} actorFiber source) view)
            proof stable
          advanceOneDeleteRuntimeCommute nameEq keyEq actor ambient source removed
            removedComponent removedParent removedRetired removedTable
            removedOutcome removedFound removedNoChild actorDistinct
            sourceWellFormed raw | Just actorFiber |
            Reloading (step :: rest) accumulator view | Just capability |
            Right (localAfter, undo) | False =
              let actorView = wellFormedFiberView nameEq keyEq actor
                    (MkSystemState ambient source) actorFiber actorFound
                    sourceWellFormed
                  providersValid = reloadingProvidersValidAdvance nameEq keyEq
                    actorFiber (step :: rest) accumulator view source actorLife
                    actorView
                  replayResolved = trans
                    (resolveCommittedValuesInactiveDelete nameEq keyEq
                      (dependencies
                        (componentDependencies (fiberComponent actorFiber))) view
                      removed removedComponent removedParent removedRetired
                      removedTable removedOutcome source removedFound
                      providersValid) resolved
                  replayFound = trans
                    (lookupDeleteOther actor removed actorDistinct source)
                    actorFound
                  replayTarget = targetFiberInactiveDelete nameEq keyEq actorFiber
                    removed removedComponent removedParent removedRetired
                    removedTable removedOutcome source removedFound
                  nextAccumulator = pushLocalUndo
                    (componentProvisions (fiberComponent actorFiber)) accumulator
                    undo
                  0 replayRaw : (applyAction @{nameEq} @{keyEq}
                    (the (Action name key value world error) (LAdvance actor))
                    (MkSystemState ambient
                      (deleteBinding @{nameEq} removed source)) =
                    Just (LDivertTag, MkSystemState (localWorld localAfter)
                      (replaceBinding @{nameEq} actor
                        (setFiberRuntime actorFiber (localTable localAfter)
                          (Unloading
                            (pushLocalUndo
                              (componentProvisions
                                (fiberComponent actorFiber)) accumulator undo)
                            view Nothing))
                        (deleteBinding @{nameEq} removed source))))
                  replayRaw = rewrite replayFound in rewrite actorLife in
                    rewrite replayResolved in rewrite ran in rewrite replayTarget
                    in rewrite stable in Refl
              in case justInjective raw of
                Refl => replacementDeleteRuntimeCommute nameEq keyEq
                  (LAdvance actor) LDivertTag actor removed actorDistinct ambient
                  (localWorld localAfter) source
                  (setFiberRuntime actorFiber (localTable localAfter)
                    (Unloading
                      (pushLocalUndo
                        (componentProvisions (fiberComponent actorFiber))
                        accumulator undo) view Nothing)) replayRaw
          advanceOneDeleteRuntimeCommute nameEq keyEq actor ambient source removed
            removedComponent removedParent removedRetired removedTable
            removedOutcome removedFound removedNoChild actorDistinct
            sourceWellFormed raw | Just actorFiber |
            Reloading (step :: []) accumulator view | Just capability |
            Right (localAfter, undo) | True =
              let actorView = wellFormedFiberView nameEq keyEq actor
                    (MkSystemState ambient source) actorFiber actorFound
                    sourceWellFormed
                  providersValid = reloadingProvidersValidAdvance nameEq keyEq
                    actorFiber [step] accumulator view source actorLife actorView
                  replayResolved = trans
                    (resolveCommittedValuesInactiveDelete nameEq keyEq
                      (dependencies
                        (componentDependencies (fiberComponent actorFiber))) view
                      removed removedComponent removedParent removedRetired
                      removedTable removedOutcome source removedFound
                      providersValid) resolved
                  replayFound = trans
                    (lookupDeleteOther actor removed actorDistinct source)
                    actorFound
                  replayTarget = targetFiberInactiveDelete nameEq keyEq actorFiber
                    removed removedComponent removedParent removedRetired
                    removedTable removedOutcome source removedFound
                  nextAccumulator = pushLocalUndo
                    (componentProvisions (fiberComponent actorFiber)) accumulator
                    undo
                  0 replayRaw : (applyAction @{nameEq} @{keyEq}
                    (the (Action name key value world error) (LAdvance actor))
                    (MkSystemState ambient
                      (deleteBinding @{nameEq} removed source)) =
                    Just (LFinishTag, MkSystemState (localWorld localAfter)
                      (replaceBinding @{nameEq} actor
                        (setFiberRuntime actorFiber (localTable localAfter)
                          (Active
                            (pushLocalUndo
                              (componentProvisions
                                (fiberComponent actorFiber)) accumulator undo)
                            view))
                        (deleteBinding @{nameEq} removed source))))
                  replayRaw = rewrite replayFound in rewrite actorLife in
                    rewrite replayResolved in rewrite ran in rewrite replayTarget
                    in rewrite stable in Refl
              in case justInjective raw of
                Refl => replacementDeleteRuntimeCommute nameEq keyEq
                  (LAdvance actor) LFinishTag actor removed actorDistinct ambient
                  (localWorld localAfter) source
                  (setFiberRuntime actorFiber (localTable localAfter)
                    (Active
                      (pushLocalUndo
                        (componentProvisions (fiberComponent actorFiber))
                        accumulator undo) view)) replayRaw
          advanceOneDeleteRuntimeCommute nameEq keyEq actor ambient source removed
            removedComponent removedParent removedRetired removedTable
            removedOutcome removedFound removedNoChild actorDistinct
            sourceWellFormed raw | Just actorFiber |
            Reloading (step :: nextStep :: later) accumulator view |
            Just capability | Right (localAfter, undo) | True =
              let actorView = wellFormedFiberView nameEq keyEq actor
                    (MkSystemState ambient source) actorFiber actorFound
                    sourceWellFormed
                  providersValid = reloadingProvidersValidAdvance nameEq keyEq
                    actorFiber (step :: nextStep :: later) accumulator view source
                    actorLife actorView
                  replayResolved = trans
                    (resolveCommittedValuesInactiveDelete nameEq keyEq
                      (dependencies
                        (componentDependencies (fiberComponent actorFiber))) view
                      removed removedComponent removedParent removedRetired
                      removedTable removedOutcome source removedFound
                      providersValid) resolved
                  replayFound = trans
                    (lookupDeleteOther actor removed actorDistinct source)
                    actorFound
                  replayTarget = targetFiberInactiveDelete nameEq keyEq actorFiber
                    removed removedComponent removedParent removedRetired
                    removedTable removedOutcome source removedFound
                  nextAccumulator = pushLocalUndo
                    (componentProvisions (fiberComponent actorFiber)) accumulator
                    undo
                  0 replayRaw : (applyAction @{nameEq} @{keyEq}
                    (the (Action name key value world error) (LAdvance actor))
                    (MkSystemState ambient
                      (deleteBinding @{nameEq} removed source)) =
                    Just (LIterTag, MkSystemState (localWorld localAfter)
                      (replaceBinding @{nameEq} actor
                        (setFiberRuntime actorFiber (localTable localAfter)
                          (Reloading (nextStep :: later)
                            (pushLocalUndo
                              (componentProvisions
                                (fiberComponent actorFiber)) accumulator undo)
                            view))
                        (deleteBinding @{nameEq} removed source))))
                  replayRaw = rewrite replayFound in rewrite actorLife in
                    rewrite replayResolved in rewrite ran in rewrite replayTarget
                    in rewrite stable in Refl
              in case justInjective raw of
                Refl => replacementDeleteRuntimeCommute nameEq keyEq
                  (LAdvance actor) LIterTag actor removed actorDistinct ambient
                  (localWorld localAfter) source
                  (setFiberRuntime actorFiber (localTable localAfter)
                    (Reloading (nextStep :: later)
                      (pushLocalUndo
                        (componentProvisions (fiberComponent actorFiber))
                        accumulator undo) view)) replayRaw
