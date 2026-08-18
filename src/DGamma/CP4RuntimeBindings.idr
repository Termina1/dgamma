module DGamma.CP4RuntimeBindings

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import Data.Maybe
import Decidable.Equality

%default total

||| Host-observable runtime state.  The intrinsic `UniqueKeys` certificate is
||| erased representation evidence, so it is deliberately absent here.
public export
record RuntimeSnapshot
  (name, key, world, error : Type) (value : key -> Type) where
  constructor MkRuntimeSnapshot
  snapshotWorld : world
  snapshotBindings : List (Binding name (FiberAt name key value world error))

public export
runtimeSnapshot : SystemState name key value world error ->
  RuntimeSnapshot name key world error value
runtimeSnapshot state = MkRuntimeSnapshot (worldState state)
  (bindings (registry state))

public export
observeActionResult :
  Maybe (RuleTag, SystemState name key value world error) ->
  Maybe (RuleTag, RuntimeSnapshot name key world error value)
observeActionResult Nothing = Nothing
observeActionResult (Just (tag, state)) = Just (tag, runtimeSnapshot state)

0 transportRight : {left, right, result : item} ->
  left = right -> left = result -> right = result
transportRight same observed = trans (sym same) observed

0 resolveViewReproof :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (deps : List key) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (leftUnique, rightUnique : UniqueKeys (bindingKeys entries)) ->
  resolveView @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} deps
    (MkCoeffectContext entries leftUnique) =
  resolveView @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} deps
    (MkCoeffectContext entries rightUnique)
resolveViewReproof nameEq keyEq [] entries leftUnique rightUnique = Refl
resolveViewReproof nameEq keyEq (wanted :: rest) entries leftUnique rightUnique
  with (providerIn @{nameEq} @{keyEq} wanted entries)
  resolveViewReproof nameEq keyEq (wanted :: rest) entries leftUnique
    rightUnique | Nothing = Refl
  resolveViewReproof nameEq keyEq (wanted :: rest) entries leftUnique
    rightUnique | Just provider = cong (map (ProviderView provider))
      (resolveViewReproof nameEq keyEq rest entries leftUnique rightUnique)

0 resolveCommittedValuesReproof :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (deps : List key) -> (view : View name deps) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (leftUnique, rightUnique : UniqueKeys (bindingKeys entries)) ->
  resolveCommittedValues @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} deps view
    (MkCoeffectContext entries leftUnique) =
  resolveCommittedValues @{nameEq} @{keyEq} {name = name} {key = key}
    {value = value} {world = world} {error = error} deps view
    (MkCoeffectContext entries rightUnique)
resolveCommittedValuesReproof nameEq keyEq [] EmptyView entries leftUnique
  rightUnique = Refl
resolveCommittedValuesReproof nameEq keyEq (wanted :: rest)
  (ProviderView provider tailView) entries leftUnique rightUnique
  with (lookupEntries @{nameEq} provider entries)
  resolveCommittedValuesReproof nameEq keyEq (wanted :: rest)
    (ProviderView provider tailView) entries leftUnique rightUnique | Nothing =
      Refl
  resolveCommittedValuesReproof nameEq keyEq (wanted :: rest)
    (ProviderView provider tailView) entries leftUnique rightUnique |
    Just providerFiber
    with (lookupBinding @{keyEq} wanted
      (ownedValues (fiberTable providerFiber)))
    resolveCommittedValuesReproof nameEq keyEq (wanted :: rest)
      (ProviderView provider tailView) entries leftUnique rightUnique |
      Just providerFiber | Nothing = Refl
    resolveCommittedValuesReproof nameEq keyEq (wanted :: rest)
      (ProviderView provider tailView) entries leftUnique rightUnique |
      Just providerFiber | Just provided = cong (map (OneDepValue provided))
        (resolveCommittedValuesReproof nameEq keyEq rest tailView entries
          leftUnique rightUnique)

0 targetFiberReproof :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (fiber : Fiber name key value world error) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (leftUnique, rightUnique : UniqueKeys (bindingKeys entries)) ->
  targetFiber @{nameEq} @{keyEq} fiber
    (MkCoeffectContext entries leftUnique) =
  targetFiber @{nameEq} @{keyEq} fiber
    (MkCoeffectContext entries rightUnique)
targetFiberReproof nameEq keyEq
  (MkFiber component parent False table lifecycle) entries leftUnique
  rightUnique = resolveViewReproof nameEq keyEq
    (dependencies (componentDependencies component)) entries leftUnique
    rightUnique
targetFiberReproof nameEq keyEq
  (MkFiber component parent True table lifecycle) entries leftUnique
  rightUnique = Refl

0 targetMatchesReproof :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (fiber : Fiber name key value world error) ->
  (view : View name
    (dependencies (componentDependencies (fiberComponent fiber)))) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (leftUnique, rightUnique : UniqueKeys (bindingKeys entries)) ->
  targetMatches @{nameEq}
    (targetFiber @{nameEq} @{keyEq} fiber
      (MkCoeffectContext entries leftUnique)) view =
  targetMatches @{nameEq}
    (targetFiber @{nameEq} @{keyEq} fiber
      (MkCoeffectContext entries rightUnique)) view
targetMatchesReproof nameEq keyEq fiber view entries leftUnique rightUnique =
  cong (\target => targetMatches @{nameEq} target view)
    (targetFiberReproof nameEq keyEq fiber entries leftUnique rightUnique)

||| The raw evaluator is insensitive to proof-only changes of a registry's
||| `UniqueKeys` witness.  Results are compared by exact world and ordered
||| binding list, which is the complete host-observable runtime representation.
0 applyActionReproofCoherent :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  (ambient : world) ->
  (entries : List (Binding name (FiberAt name key value world error))) ->
  (leftUnique, rightUnique : UniqueKeys (bindingKeys entries)) ->
  observeActionResult (applyAction @{nameEq} @{keyEq} action
    (MkSystemState ambient (MkCoeffectContext entries leftUnique))) =
  observeActionResult (applyAction @{nameEq} @{keyEq} action
    (MkSystemState ambient (MkCoeffectContext entries rightUnique)))
applyActionReproofCoherent nameEq keyEq (OInsert actor Root component) ambient
  entries leftUnique rightUnique
  with (provisionsDisjointFrom @{keyEq} (componentProvisions component) entries)
  applyActionReproofCoherent nameEq keyEq (OInsert actor Root component) ambient
    entries leftUnique rightUnique | False = Refl
  applyActionReproofCoherent nameEq keyEq (OInsert actor Root component) ambient
    entries leftUnique rightUnique | True
    with (lookupEntries @{nameEq} actor entries)
    applyActionReproofCoherent nameEq keyEq (OInsert actor Root component)
      ambient entries leftUnique rightUnique | True | Nothing = Refl
    applyActionReproofCoherent nameEq keyEq (OInsert actor Root component)
      ambient entries leftUnique rightUnique | True | Just fiber = Refl
applyActionReproofCoherent nameEq keyEq
  (OInsert actor parent@(ChildOf parentName) component) ambient entries leftUnique
  rightUnique with
  (parentPresent @{nameEq} parent (MkCoeffectContext entries leftUnique) &&
    provisionsDisjointFrom @{keyEq} (componentProvisions component) entries)
    proof leftGuards
  applyActionReproofCoherent nameEq keyEq
    (OInsert actor parent@(ChildOf parentName) component) ambient entries
    leftUnique rightUnique | False = Refl
  applyActionReproofCoherent nameEq keyEq
    (OInsert actor parent@(ChildOf parentName) component) ambient entries
    leftUnique rightUnique | True with (lookupEntries @{nameEq} actor entries)
    applyActionReproofCoherent nameEq keyEq
      (OInsert actor parent@(ChildOf parentName) component) ambient entries
      leftUnique rightUnique | True | Nothing = Refl
    applyActionReproofCoherent nameEq keyEq
      (OInsert actor parent@(ChildOf parentName) component) ambient entries
      leftUnique rightUnique | True | Just fiber = Refl
applyActionReproofCoherent nameEq keyEq (ORetire actor) ambient entries
  leftUnique rightUnique with (lookupEntries @{nameEq} actor entries)
  applyActionReproofCoherent nameEq keyEq (ORetire actor) ambient entries
    leftUnique rightUnique | Nothing = Refl
  applyActionReproofCoherent nameEq keyEq (ORetire actor) ambient entries
    leftUnique rightUnique | Just fiber = Refl
applyActionReproofCoherent nameEq keyEq (ORemove actor) ambient entries
  leftUnique rightUnique with (lookupEntries @{nameEq} actor entries)
  applyActionReproofCoherent nameEq keyEq (ORemove actor) ambient entries
    leftUnique rightUnique | Nothing = Refl
  applyActionReproofCoherent nameEq keyEq (ORemove actor) ambient entries
    leftUnique rightUnique | Just fiber
    with (retired fiber && isInactive (fiberLifecycle fiber) &&
      not (hasChildIn @{nameEq} actor entries))
    applyActionReproofCoherent nameEq keyEq (ORemove actor) ambient entries
      leftUnique rightUnique | Just fiber | False = Refl
    applyActionReproofCoherent nameEq keyEq (ORemove actor) ambient entries
      leftUnique rightUnique | Just fiber | True = Refl
applyActionReproofCoherent nameEq keyEq (LBegin actor) ambient entries leftUnique
  rightUnique with (lookupEntries @{nameEq} actor entries)
  applyActionReproofCoherent nameEq keyEq (LBegin actor) ambient entries
    leftUnique rightUnique | Nothing = Refl
  applyActionReproofCoherent nameEq keyEq (LBegin actor) ambient entries
    leftUnique rightUnique | Just fiber with (fiberLifecycle fiber)
    applyActionReproofCoherent nameEq keyEq (LBegin actor) ambient entries
      leftUnique rightUnique | Just fiber | Inactive Nothing
      with (targetFiber @{nameEq} @{keyEq} fiber
        (MkCoeffectContext entries leftUnique)) proof leftTarget
      applyActionReproofCoherent nameEq keyEq (LBegin actor) ambient entries
        leftUnique rightUnique | Just fiber | Inactive Nothing | Nothing =
          let rightTarget = transportRight
                (targetFiberReproof nameEq keyEq fiber entries leftUnique
                  rightUnique) leftTarget
          in rewrite rightTarget in Refl
      applyActionReproofCoherent nameEq keyEq (LBegin actor) ambient entries
        leftUnique rightUnique | Just fiber | Inactive Nothing | Just view =
          let rightTarget = transportRight
                (targetFiberReproof nameEq keyEq fiber entries leftUnique
                  rightUnique) leftTarget
          in rewrite rightTarget in Refl
    applyActionReproofCoherent nameEq keyEq (LBegin actor) ambient entries
      leftUnique rightUnique | Just fiber | Inactive (Just failure) = Refl
    applyActionReproofCoherent nameEq keyEq (LBegin actor) ambient entries
      leftUnique rightUnique | Just fiber |
      Reloading remaining accumulator view = Refl
    applyActionReproofCoherent nameEq keyEq (LBegin actor) ambient entries
      leftUnique rightUnique | Just fiber | Active accumulator view = Refl
    applyActionReproofCoherent nameEq keyEq (LBegin actor) ambient entries
      leftUnique rightUnique | Just fiber | Unloading accumulator view outcome =
        Refl
applyActionReproofCoherent nameEq keyEq (LAdvance actor) ambient entries
  leftUnique rightUnique with (lookupEntries @{nameEq} actor entries)
  applyActionReproofCoherent nameEq keyEq (LAdvance actor) ambient entries
    leftUnique rightUnique | Nothing = Refl
  applyActionReproofCoherent nameEq keyEq (LAdvance actor) ambient entries
    leftUnique rightUnique | Just fiber with (fiberLifecycle fiber)
    applyActionReproofCoherent nameEq keyEq (LAdvance actor) ambient entries
      leftUnique rightUnique | Just fiber | Inactive outcome = Refl
    applyActionReproofCoherent nameEq keyEq (LAdvance actor) ambient entries
      leftUnique rightUnique | Just fiber | Reloading [] accumulator view
      with (targetMatches @{nameEq}
        (targetFiber @{nameEq} @{keyEq} fiber
          (MkCoeffectContext entries leftUnique)) view) proof leftMatches
      applyActionReproofCoherent nameEq keyEq (LAdvance actor) ambient entries
        leftUnique rightUnique | Just fiber | Reloading [] accumulator view |
        False =
          let rightMatches = transportRight
                (targetMatchesReproof nameEq keyEq fiber view entries leftUnique
                  rightUnique) leftMatches
          in rewrite rightMatches in Refl
      applyActionReproofCoherent nameEq keyEq (LAdvance actor) ambient entries
        leftUnique rightUnique | Just fiber | Reloading [] accumulator view |
        True =
          let rightMatches = transportRight
                (targetMatchesReproof nameEq keyEq fiber view entries leftUnique
                  rightUnique) leftMatches
          in rewrite rightMatches in Refl
    applyActionReproofCoherent nameEq keyEq (LAdvance actor) ambient entries
      leftUnique rightUnique | Just fiber |
      Reloading (step :: remaining) accumulator view
      with (resolveCommittedValues @{nameEq} @{keyEq}
        (dependencies (componentDependencies (fiberComponent fiber))) view
        (MkCoeffectContext entries leftUnique)) proof leftCapability
      applyActionReproofCoherent nameEq keyEq (LAdvance actor) ambient entries
        leftUnique rightUnique | Just fiber |
        Reloading (step :: remaining) accumulator view | Nothing =
          let rightCapability = transportRight
                (resolveCommittedValuesReproof {name = name} {key = key} {value = value} {world = world} {error = error} nameEq keyEq
                  (dependencies
                    (componentDependencies (fiberComponent fiber))) view entries
                  leftUnique rightUnique) leftCapability
          in rewrite rightCapability in Refl
      applyActionReproofCoherent nameEq keyEq (LAdvance actor) ambient entries
        leftUnique rightUnique | Just fiber |
        Reloading (step :: remaining) accumulator view | Just capability
        with (runStepEffect step capability
          (MkLocalState ambient
            (restrictOwnedPreservingOrder
              (componentProvisions (fiberComponent fiber))
              (ownedValues (fiberTable fiber))))) proof leftStep
        applyActionReproofCoherent nameEq keyEq (LAdvance actor) ambient entries
          leftUnique rightUnique | Just fiber |
          Reloading (step :: remaining) accumulator view | Just capability |
          Left failure =
            let rightCapability = transportRight
                  (resolveCommittedValuesReproof {name = name} {key = key} {value = value} {world = world} {error = error} nameEq keyEq
                    (dependencies
                      (componentDependencies (fiberComponent fiber))) view
                    entries leftUnique rightUnique) leftCapability
            in rewrite rightCapability in rewrite leftStep in Refl
        applyActionReproofCoherent nameEq keyEq (LAdvance actor) ambient entries
          leftUnique rightUnique | Just fiber |
          Reloading (step :: remaining) accumulator view | Just capability |
          Right (localAfter, undo)
          with (targetMatches @{nameEq}
            (targetFiber @{nameEq} @{keyEq} fiber
              (MkCoeffectContext entries leftUnique)) view) proof leftMatches
          applyActionReproofCoherent nameEq keyEq (LAdvance actor) ambient entries
            leftUnique rightUnique | Just fiber |
            Reloading (step :: remaining) accumulator view | Just capability |
            Right (localAfter, undo) | False =
              let rightCapability = transportRight
                    (resolveCommittedValuesReproof {name = name} {key = key} {value = value} {world = world} {error = error} nameEq keyEq
                      (dependencies
                        (componentDependencies (fiberComponent fiber))) view
                      entries leftUnique rightUnique) leftCapability
                  rightMatches = transportRight
                    (targetMatchesReproof nameEq keyEq fiber view entries
                      leftUnique rightUnique) leftMatches
              in rewrite rightCapability in rewrite leftStep in
                rewrite rightMatches in Refl
          applyActionReproofCoherent nameEq keyEq (LAdvance actor) ambient entries
            leftUnique rightUnique | Just fiber |
            Reloading (step :: remaining) accumulator view | Just capability |
            Right (localAfter, undo) | True =
              let rightCapability = transportRight
                    (resolveCommittedValuesReproof {name = name} {key = key}
                      {value = value} {world = world} {error = error} nameEq keyEq
                      (dependencies
                        (componentDependencies (fiberComponent fiber))) view
                      entries leftUnique rightUnique) leftCapability
                  rightMatches = transportRight
                    (targetMatchesReproof nameEq keyEq fiber view entries
                      leftUnique rightUnique) leftMatches
              in rewrite rightCapability in rewrite leftStep in
                rewrite rightMatches in case remaining of
                  [] => Refl
                  next :: later => Refl
    applyActionReproofCoherent nameEq keyEq (LAdvance actor) ambient entries
      leftUnique rightUnique | Just fiber | Active accumulator view = Refl
    applyActionReproofCoherent nameEq keyEq (LAdvance actor) ambient entries
      leftUnique rightUnique | Just fiber | Unloading accumulator view outcome =
        Refl
applyActionReproofCoherent nameEq keyEq (LDivert actor) ambient entries
  leftUnique rightUnique with (lookupEntries @{nameEq} actor entries)
  applyActionReproofCoherent nameEq keyEq (LDivert actor) ambient entries
    leftUnique rightUnique | Nothing = Refl
  applyActionReproofCoherent nameEq keyEq (LDivert actor) ambient entries
    leftUnique rightUnique | Just fiber with (fiberLifecycle fiber)
    applyActionReproofCoherent nameEq keyEq (LDivert actor) ambient entries
      leftUnique rightUnique | Just fiber | Inactive outcome = Refl
    applyActionReproofCoherent nameEq keyEq (LDivert actor) ambient entries
      leftUnique rightUnique | Just fiber |
      Reloading remaining accumulator view
      with (targetMatches @{nameEq}
        (targetFiber @{nameEq} @{keyEq} fiber
          (MkCoeffectContext entries leftUnique)) view) proof leftMatches
      applyActionReproofCoherent nameEq keyEq (LDivert actor) ambient entries
        leftUnique rightUnique | Just fiber |
        Reloading remaining accumulator view | False =
          let rightMatches = transportRight
                (targetMatchesReproof nameEq keyEq fiber view entries leftUnique
                  rightUnique) leftMatches
          in rewrite rightMatches in Refl
      applyActionReproofCoherent nameEq keyEq (LDivert actor) ambient entries
        leftUnique rightUnique | Just fiber |
        Reloading remaining accumulator view | True =
          let rightMatches = transportRight
                (targetMatchesReproof nameEq keyEq fiber view entries leftUnique
                  rightUnique) leftMatches
          in rewrite rightMatches in Refl
    applyActionReproofCoherent nameEq keyEq (LDivert actor) ambient entries
      leftUnique rightUnique | Just fiber | Active accumulator view = Refl
    applyActionReproofCoherent nameEq keyEq (LDivert actor) ambient entries
      leftUnique rightUnique | Just fiber | Unloading accumulator view outcome =
        Refl
applyActionReproofCoherent nameEq keyEq (LLeave actor) ambient entries leftUnique
  rightUnique with (lookupEntries @{nameEq} actor entries)
  applyActionReproofCoherent nameEq keyEq (LLeave actor) ambient entries
    leftUnique rightUnique | Nothing = Refl
  applyActionReproofCoherent nameEq keyEq (LLeave actor) ambient entries
    leftUnique rightUnique | Just fiber with (fiberLifecycle fiber)
    applyActionReproofCoherent nameEq keyEq (LLeave actor) ambient entries
      leftUnique rightUnique | Just fiber | Inactive outcome = Refl
    applyActionReproofCoherent nameEq keyEq (LLeave actor) ambient entries
      leftUnique rightUnique | Just fiber |
      Reloading remaining accumulator view = Refl
    applyActionReproofCoherent nameEq keyEq (LLeave actor) ambient entries
      leftUnique rightUnique | Just fiber | Active accumulator view
      with (targetMatches @{nameEq}
        (targetFiber @{nameEq} @{keyEq} fiber
          (MkCoeffectContext entries leftUnique)) view) proof leftMatches
      applyActionReproofCoherent nameEq keyEq (LLeave actor) ambient entries
        leftUnique rightUnique | Just fiber | Active accumulator view | False =
          let rightMatches = transportRight
                (targetMatchesReproof nameEq keyEq fiber view entries leftUnique
                  rightUnique) leftMatches
          in rewrite rightMatches in Refl
      applyActionReproofCoherent nameEq keyEq (LLeave actor) ambient entries
        leftUnique rightUnique | Just fiber | Active accumulator view | True =
          let rightMatches = transportRight
                (targetMatchesReproof nameEq keyEq fiber view entries leftUnique
                  rightUnique) leftMatches
          in rewrite rightMatches in Refl
    applyActionReproofCoherent nameEq keyEq (LLeave actor) ambient entries
      leftUnique rightUnique | Just fiber | Unloading accumulator view outcome =
        Refl
applyActionReproofCoherent nameEq keyEq (LUnload actor) ambient entries
  leftUnique rightUnique with (lookupEntries @{nameEq} actor entries)
  applyActionReproofCoherent nameEq keyEq (LUnload actor) ambient entries
    leftUnique rightUnique | Nothing = Refl
  applyActionReproofCoherent nameEq keyEq (LUnload actor) ambient entries
    leftUnique rightUnique | Just fiber with (fiberLifecycle fiber)
    applyActionReproofCoherent nameEq keyEq (LUnload actor) ambient entries
      leftUnique rightUnique | Just fiber | Inactive outcome = Refl
    applyActionReproofCoherent nameEq keyEq (LUnload actor) ambient entries
      leftUnique rightUnique | Just fiber |
      Reloading remaining accumulator view = Refl
    applyActionReproofCoherent nameEq keyEq (LUnload actor) ambient entries
      leftUnique rightUnique | Just fiber | Active accumulator view = Refl
    applyActionReproofCoherent nameEq keyEq (LUnload actor) ambient entries
      leftUnique rightUnique | Just fiber | Unloading accumulator view outcome
      with (reliedOnBy @{nameEq} actor actor entries)
      applyActionReproofCoherent nameEq keyEq (LUnload actor) ambient entries
        leftUnique rightUnique | Just fiber |
        Unloading accumulator view outcome | False = Refl
      applyActionReproofCoherent nameEq keyEq (LUnload actor) ambient entries
        leftUnique rightUnique | Just fiber |
        Unloading accumulator view outcome | True = Refl

||| Reproof coherence lifted from identical binding lists to arbitrary states
||| with the same exact runtime snapshot.
public export
0 applyActionObservationCoherent :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  (left, right : SystemState name key value world error) ->
  runtimeSnapshot left = runtimeSnapshot right ->
  observeActionResult (applyAction @{nameEq} @{keyEq} action left) =
  observeActionResult (applyAction @{nameEq} @{keyEq} action right)
applyActionObservationCoherent nameEq keyEq action
  (MkSystemState leftWorld (MkCoeffectContext leftEntries leftUnique))
  (MkSystemState rightWorld (MkCoeffectContext rightEntries rightUnique)) same =
    case same of
      Refl => applyActionReproofCoherent nameEq keyEq action leftWorld
        rightEntries leftUnique rightUnique

||| Total transport package for one successful evaluator step.  The tag is
||| preserved exactly; the target is preserved at the runtime snapshot level.
public export
record ActionRuntimeTransport
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (action : Action name key value world error)
  (source : SystemState name key value world error)
  (tag : RuleTag)
  (originalAfter : SystemState name key value world error) where
  constructor MkActionRuntimeTransport
  transportedAfter : SystemState name key value world error
  0 transportedRaw : applyAction @{nameEq} @{keyEq} action source =
    Just (tag, transportedAfter)
  0 transportedSnapshot : runtimeSnapshot originalAfter =
    runtimeSnapshot transportedAfter

||| Keystone transport lemma used by replay boundaries: raw evaluator success
||| crosses exact ambient/ordered-binding equality without asking for equality
||| of erased `UniqueKeys` proofs.
public export
0 transportApplyActionAcrossRuntimeSnapshot :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  (originalSource, transportedSource :
    SystemState name key value world error) ->
  runtimeSnapshot originalSource = runtimeSnapshot transportedSource ->
  (tag : RuleTag) ->
  (originalAfter : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq} action originalSource =
    Just (tag, originalAfter) ->
  ActionRuntimeTransport name key world error value nameEq keyEq action
    transportedSource tag originalAfter
transportApplyActionAcrossRuntimeSnapshot nameEq keyEq action originalSource
  transportedSource sourcesSame tag originalAfter originalRaw
  with (applyAction @{nameEq} @{keyEq} action transportedSource) proof transported
  transportApplyActionAcrossRuntimeSnapshot nameEq keyEq action originalSource
    transportedSource sourcesSame tag originalAfter originalRaw | Nothing =
      let coherent = applyActionObservationCoherent nameEq keyEq action
            originalSource transportedSource sourcesSame
      in void (nothingIsNotJust (sym
        (trans (sym (cong observeActionResult originalRaw))
          (trans coherent (cong observeActionResult transported)))))
  transportApplyActionAcrossRuntimeSnapshot nameEq keyEq action originalSource
    transportedSource sourcesSame tag originalAfter originalRaw |
    Just (transportedTag, transportedAfter) =
      let coherent = applyActionObservationCoherent nameEq keyEq action
            originalSource transportedSource sourcesSame
          observed = trans (sym (cong observeActionResult originalRaw))
            (trans coherent (cong observeActionResult transported))
          samePair = justInjective observed
          sameTag = cong fst samePair
          sameSnapshot = cong snd samePair
      in case sameTag of
        Refl => MkActionRuntimeTransport transportedAfter transported sameSnapshot
