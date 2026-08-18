module DGamma.CP4DeletionBoundaryDeleted

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionBoundaryPlan
import DGamma.CP4DeletionControlPlan
import DGamma.CP4DeletionGenerationUnique
import DGamma.CP4DeletionInactiveInvariant
import DGamma.CP4DeletionNoEpisodeReplay
import DGamma.CP4DeletionPlanBuilder
import DGamma.CP4DeletionPlanCommute
import DGamma.CP4DeletionPlanComplete
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total

0 nothingNotJustBoundary : Nothing = Just item -> Void
nothingNotJustBoundary Refl impossible

0 noChildFromRemovalGuardBoundary :
  (retiredFlag, inactiveFlag, childPresent : Bool) ->
  retiredFlag && inactiveFlag && not childPresent = True ->
  childPresent = False
noChildFromRemovalGuardBoundary retiredFlag inactiveFlag False valid = Refl
noChildFromRemovalGuardBoundary False inactiveFlag True valid =
  case valid of Refl impossible
noChildFromRemovalGuardBoundary True False True valid =
  case valid of Refl impossible
noChildFromRemovalGuardBoundary True True True valid =
  case valid of Refl impossible

public export
data RetireSuccessView :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (actor : name) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  RuleTag -> SystemState name key value world error -> Type where
  MkRetireSuccessView :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {actor : name} -> {ambient : world} ->
    {source : Registry name key value world error} ->
    (oldFiber : Fiber name key value world error) ->
    lookupFiber @{nameEq} actor source = Just oldFiber ->
    RetireSuccessView name key world error value nameEq actor ambient source
      ORetireTag
      (MkSystemState ambient
        (replaceBinding @{nameEq} actor (retireFiber oldFiber) source))

public export
0 retireSuccessView :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor : name) -> (ambient : world) ->
  (source : Registry name key value world error) ->
  (tag : RuleTag) ->
  (afterState : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq}
    (the (Action name key value world error) (ORetire actor))
    (MkSystemState ambient source) = Just (tag, afterState) ->
  RetireSuccessView name key world error value nameEq actor ambient source tag
    afterState
retireSuccessView nameEq keyEq actor ambient source tag afterState raw
  with (lookupFiber @{nameEq} actor source) proof found
  retireSuccessView nameEq keyEq actor ambient source tag afterState raw |
    Nothing = void (nothingNotJustBoundary raw)
  retireSuccessView nameEq keyEq actor ambient source tag afterState raw |
    Just oldFiber = case justInjective raw of
      Refl => MkRetireSuccessView oldFiber found

public export
data RemoveSuccessView :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (actor : name) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  RuleTag -> SystemState name key value world error -> Type where
  MkRemoveSuccessView :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {actor : name} -> {ambient : world} ->
    {source : Registry name key value world error} ->
    (oldFiber : Fiber name key value world error) ->
    lookupFiber @{nameEq} actor source = Just oldFiber ->
    (retired oldFiber && isInactive (fiberLifecycle oldFiber) &&
      not (hasChild @{nameEq} {name = name} {key = key} {value = value}
        {world = world} {error = error} actor source) = True) ->
    hasChild @{nameEq} {name = name} {key = key} {value = value}
      {world = world} {error = error} actor source = False ->
    RemoveSuccessView name key world error value nameEq actor ambient source
      ORemoveTag (MkSystemState ambient (deleteBinding @{nameEq} actor source))

public export
0 removeSuccessView :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor : name) -> (ambient : world) ->
  (source : Registry name key value world error) ->
  (tag : RuleTag) ->
  (afterState : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq}
    (the (Action name key value world error) (ORemove actor))
    (MkSystemState ambient source) = Just (tag, afterState) ->
  RemoveSuccessView name key world error value nameEq actor ambient source tag
    afterState
removeSuccessView nameEq keyEq actor ambient source tag afterState raw
  with (lookupFiber @{nameEq} actor source) proof found
  removeSuccessView nameEq keyEq actor ambient source tag afterState raw |
    Nothing = void (nothingNotJustBoundary raw)
  removeSuccessView nameEq keyEq actor ambient source tag afterState raw |
    Just oldFiber with (retired oldFiber &&
      isInactive (fiberLifecycle oldFiber) &&
      not (hasChild @{nameEq} actor source)) proof removable
    removeSuccessView nameEq keyEq actor ambient source tag afterState raw |
      Just oldFiber | False = void (nothingNotJustBoundary raw)
    removeSuccessView nameEq keyEq actor ambient source tag afterState raw |
      Just oldFiber | True = case justInjective raw of
        Refl => MkRemoveSuccessView oldFiber found removable
          (noChildFromRemovalGuardBoundary (retired oldFiber)
            (isInactive (fiberLifecycle oldFiber))
            (hasChild @{nameEq} actor source) removable)

||| A deleted exact-generation O-Retire is not replayed in the survivor.  The
||| evaluator permits idempotent retirement, so the corresponding plan leaf is
||| updated in place and still deletes to the same survivor snapshot.
public export
0 deletedRetirePreservesNoEpisodeBoundary :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (actor : name) ->
  (original, survivor : SystemState name key value world error) ->
  (boundary : NoEpisodeReplayBoundary name key world error value nameEq keyEq
    registered live original survivor) ->
  {originalAfter : SystemState name key value world error} ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq}
    (the (Action name key value world error) (ORetire actor)) original =
    Just (tag, originalAfter)) ->
  GenerationOwnedActor nameEq registered ordinal live
    (the (Action name key value world error) (ORetire actor)) ->
  NoEpisodeReplayBoundary name key world error value nameEq keyEq registered
    (advanceGenerationEnvironment @{nameEq} ordinal
      (the (Action name key value world error) (ORetire actor)) live)
    originalAfter survivor
deletedRetirePreservesNoEpisodeBoundary {name} {key} {world} {error} {value}
  nameEq keyEq registered ordinal live actor original survivor
  (MkNoEpisodeReplayBoundary ambient source originalShape
    (MkCompleteCurrentRegisteredPlanResult
      oldPlan@(MkCurrentRegisteredPlanResult oldTarget oldInactive oldOutside)
      oldComplete)
    survivorAmbient survivorBindings unique sourceWellFormed survivorWellFormed)
  tag checked (generation ** (owned, member)) =
    case originalShape of
      Refl =>
        let 0 raw = checkedActionProjects nameEq keyEq (ORetire actor)
              (MkSystemState ambient source) originalAfter tag checked
            0 currentEntry = currentGenerationEntryFromLookup nameEq actor
              generation live owned
            0 planMember = oldComplete actor generation currentEntry member
        in case retireSuccessView nameEq keyEq actor ambient source tag
          originalAfter raw of
          MkRetireSuccessView oldFiber found =>
            case retireExactActorInInactivePlan nameEq actor oldFiber source
              oldTarget oldInactive planMember found of
              MkInactivePlanPreservingUpdateCommute
                (MkInactivePlanUpdateCommute nextTarget nextInactive
                  nextTargetBindings nextOutside)
                actorsSame =>
                  let nextPlan : CurrentRegisteredPlanResult name key world
                        error value nameEq registered live
                        (replaceBinding @{nameEq} actor
                          (retireFiber oldFiber) source)
                      nextPlan = MkCurrentRegisteredPlanResult nextTarget
                        nextInactive
                        (\observed, outside => nextOutside observed
                          (oldOutside observed outside))
                      0 nextComplete : CurrentRegisteredPlanComplete name key
                        world error value nameEq registered live nextPlan
                      nextComplete selected observedGeneration present
                        observedMember = replace {p = Elem selected}
                          (sym actorsSame)
                          (oldComplete selected observedGeneration present
                            observedMember)
                      0 targetWellFormed : (registryWellFormed @{nameEq}
                        @{keyEq} (the (SystemState name key value world error)
                          (MkSystemState ambient
                            (replaceBinding @{nameEq} actor
                              (retireFiber oldFiber) source))) = True)
                      targetWellFormed = preservationTheoremProof nameEq keyEq
                        (ORetire actor) (MkSystemState ambient source)
                        (MkSystemState ambient
                          (replaceBinding @{nameEq} actor
                            (retireFiber oldFiber) source))
                        ORetireTag sourceWellFormed raw
                      0 nextSurvivorBindings : bindings (registry survivor) =
                        bindings nextTarget
                      nextSurvivorBindings = trans survivorBindings
                        (sym nextTargetBindings)
                  in MkNoEpisodeReplayBoundary ambient
                    (replaceBinding @{nameEq} actor (retireFiber oldFiber)
                      source)
                    Refl
                    (MkCompleteCurrentRegisteredPlanResult nextPlan nextComplete)
                    survivorAmbient nextSurvivorBindings unique targetWellFormed
                    survivorWellFormed

||| A deleted exact-generation O-Remove has already been realized by the
||| survivor plan.  The original step removes the same plan occurrence; the
||| survivor remains fixed while completeness is reindexed to the environment
||| with that generation closed.
public export
0 deletedRemovePreservesNoEpisodeBoundary :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (actor : name) ->
  (original, survivor : SystemState name key value world error) ->
  (boundary : NoEpisodeReplayBoundary name key world error value nameEq keyEq
    registered live original survivor) ->
  {originalAfter : SystemState name key value world error} ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq}
    (the (Action name key value world error) (ORemove actor)) original =
    Just (tag, originalAfter)) ->
  GenerationOwnedActor nameEq registered ordinal live
    (the (Action name key value world error) (ORemove actor)) ->
  NoEpisodeReplayBoundary name key world error value nameEq keyEq registered
    (advanceGenerationEnvironment @{nameEq} ordinal
      (the (Action name key value world error) (ORemove actor)) live)
    originalAfter survivor
deletedRemovePreservesNoEpisodeBoundary {name} {key} {world} {error} {value}
  nameEq keyEq registered ordinal live actor original survivor
  (MkNoEpisodeReplayBoundary ambient source originalShape
    (MkCompleteCurrentRegisteredPlanResult
      oldPlan@(MkCurrentRegisteredPlanResult oldTarget oldInactive oldOutside)
      oldComplete)
    survivorAmbient survivorBindings unique sourceWellFormed survivorWellFormed)
  tag checked (generation ** (owned, member)) =
    case originalShape of
      Refl =>
        let 0 raw = checkedActionProjects nameEq keyEq (ORemove actor)
              (MkSystemState ambient source) originalAfter tag checked
            0 currentEntry = currentGenerationEntryFromLookup nameEq actor
              generation live owned
            0 planMember = oldComplete actor generation currentEntry member
        in case removeSuccessView nameEq keyEq actor ambient source tag
          originalAfter raw of
          MkRemoveSuccessView oldFiber found removable noChild =>
            case removeExactActorFromInactivePlan nameEq actor source oldTarget
              oldInactive planMember noChild of
              removingStrong@(MkInactivePlanRemovingUpdateCommute
                (MkInactivePlanUpdateCommute nextTarget nextInactive
                  nextTargetBindings nextOutside)
                removedOutside retainedOther) =>
                  let 0 outsideNew : (observed : name) ->
                        ActorOutsideCurrentRegistered observed registered
                          (deleteCurrentGeneration @{nameEq} actor live) ->
                        ActorOutsideDeletionPlan observed nextInactive
                      outsideNew observed outside with
                        (decEq @{nameEq} observed actor)
                        outsideNew _ outside | Yes Refl = removedOutside
                        outsideNew observed outside | No observedDistinct =
                          nextOutside observed
                            (oldOutside observed
                              (\selected, observedGeneration, present,
                                observedMember =>
                                  case decEq @{nameEq} actor selected of
                                    Yes Refl => \same => observedDistinct same
                                    No actorDistinct => outside selected
                                      observedGeneration
                                      (deletePreservesOtherEntry nameEq actor
                                        selected actorDistinct observedGeneration
                                        live present) observedMember))
                      nextPlan : CurrentRegisteredPlanResult name key world error
                        value nameEq registered
                        (deleteCurrentGeneration @{nameEq} actor live)
                        (deleteBinding @{nameEq} actor source)
                      nextPlan = MkCurrentRegisteredPlanResult nextTarget
                        nextInactive outsideNew
                      0 nextComplete : CurrentRegisteredPlanComplete name key
                        world error value nameEq registered
                        (deleteCurrentGeneration @{nameEq} actor live) nextPlan
                      nextComplete selected observedGeneration present
                        observedMember = retainedOther selected
                          (entryAfterDeleteActorDistinct nameEq actor live unique
                            selected observedGeneration present)
                          (oldComplete selected observedGeneration
                            (entryAfterDeleteComesFromOld nameEq actor live
                              selected observedGeneration present)
                            observedMember)
                      0 targetWellFormed : (registryWellFormed @{nameEq}
                        @{keyEq}
                        (the (SystemState name key value world error)
                          (MkSystemState ambient
                            (deleteBinding @{nameEq} actor source))) = True)
                      targetWellFormed = preservationTheoremProof nameEq keyEq
                        (ORemove actor) (MkSystemState ambient source)
                        (MkSystemState ambient
                          (deleteBinding @{nameEq} actor source))
                        ORemoveTag sourceWellFormed raw
                      0 nextSurvivorBindings : bindings (registry survivor) =
                        bindings nextTarget
                      nextSurvivorBindings = trans survivorBindings
                        (sym nextTargetBindings)
                      0 nextUnique : GenerationEnvironmentNamesUnique
                        (deleteCurrentGeneration @{nameEq} actor live)
                      nextUnique = advanceGenerationEnvironmentPreservesUnique
                        nameEq ordinal
                        (the (Action name key value world error) (ORemove actor))
                        live unique
                  in MkNoEpisodeReplayBoundary ambient
                    (deleteBinding @{nameEq} actor source) Refl
                    (MkCompleteCurrentRegisteredPlanResult nextPlan nextComplete)
                    survivorAmbient nextSurvivorBindings nextUnique
                    targetWellFormed survivorWellFormed

record InactiveRegistryFiberAt
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (actor : name)
  (source : Registry name key value world error) where
  constructor MkInactiveRegistryFiberAt
  inactiveRegistryComponent : Component key value world error
  inactiveRegistryParent : Parent name
  inactiveRegistryRetired : Bool
  inactiveRegistryTable : OwnedTable key value
    (componentProvisions inactiveRegistryComponent)
  inactiveRegistryOutcome : Maybe error
  0 inactiveRegistryFound : lookupFiber @{nameEq} actor source =
    Just (MkFiber inactiveRegistryComponent inactiveRegistryParent
      inactiveRegistryRetired inactiveRegistryTable
      (Inactive inactiveRegistryOutcome))

0 lookupNotElemNothingDeletedBoundary : DecEq key => (wanted : key) ->
  (entries : List (Binding key value)) ->
  Not (Elem wanted (bindingKeys entries)) ->
  lookupEntries wanted entries = Nothing
lookupNotElemNothingDeletedBoundary wanted [] absent = Refl
lookupNotElemNothingDeletedBoundary wanted (Bind current next :: rest) absent
  with (decEq wanted current)
  lookupNotElemNothingDeletedBoundary current (Bind current next :: rest) absent |
    Yes Refl = void (absent Here)
  lookupNotElemNothingDeletedBoundary wanted (Bind current next :: rest) absent |
    No distinct = lookupNotElemNothingDeletedBoundary wanted rest
      (\later => absent (There later))

0 lookupDeleteSelfDeletedBoundary : DecEq key => (removed : key) ->
  (table : CoeffectContext key value) ->
  lookupBinding removed (deleteBinding removed table) = Nothing
lookupDeleteSelfDeletedBoundary removed (MkCoeffectContext entries unique) =
  lookupNotElemNothingDeletedBoundary removed (deleteEntries removed entries)
    (deletedKeyNotElem removed entries unique)

0 inactiveRegistryFromPlanMember :
  (nameEq : DecEq name) -> (actor : name) ->
  (source, target : Registry name key value world error) ->
  (plan : InactiveLeafDeletionPlan {name = name} {key = key} {value = value}
    {world = world} {error = error} nameEq source target) ->
  Elem actor (inactivePlanActors plan) ->
  InactiveRegistryFiberAt name key world error value nameEq actor source
inactiveRegistryFromPlanMember nameEq actor source source NoInactiveLeafDeletion
  present = case present of Here impossible; There later impossible
inactiveRegistryFromPlanMember nameEq actor source target
  (DeleteInactiveLeaf removed component parent retiredFlag table outcome found
    noChild rest) present with (decEq @{nameEq} actor removed)
  inactiveRegistryFromPlanMember nameEq removed source target
    (DeleteInactiveLeaf removed component parent retiredFlag table outcome found
      noChild rest) present | Yes Refl = case present of
        Here => MkInactiveRegistryFiberAt component parent retiredFlag table
          outcome found
        There later =>
          let tailInactive = inactiveRegistryFromPlanMember nameEq removed
                (deleteBinding @{nameEq} removed source) target rest later
          in void (nothingNotJustBoundary
            (trans (sym (lookupDeleteSelfDeletedBoundary removed source))
              (inactiveRegistryFound tailInactive)))
  inactiveRegistryFromPlanMember nameEq actor source target
    (DeleteInactiveLeaf removed component parent retiredFlag table outcome found
      noChild rest) present | No distinct = case present of
        Here => void (distinct Refl)
        There later => case inactiveRegistryFromPlanMember nameEq actor
          (deleteBinding @{nameEq} removed source) target rest later of
          MkInactiveRegistryFiberAt observedComponent observedParent
            observedRetired observedTable observedOutcome tailFound =>
              MkInactiveRegistryFiberAt observedComponent observedParent
                observedRetired observedTable observedOutcome
                (trans (sym (lookupDeleteOther actor removed distinct source))
                  tailFound)

0 advanceInactiveImpossible :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (tag : RuleTag) -> (afterState : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq}
    (the (Action name key value world error) (LAdvance actor))
    (MkSystemState ambient source) = Just (tag, afterState) ->
  InactiveRegistryFiberAt name key world error value nameEq actor source -> Void
advanceInactiveImpossible nameEq keyEq actor ambient source tag afterState raw
  (MkInactiveRegistryFiberAt component parent retiredFlag table outcome found) =
    let 0 reduced : (applyAction @{nameEq} @{keyEq}
          (the (Action name key value world error) (LAdvance actor))
          (MkSystemState ambient source) = Nothing)
        reduced = rewrite found in Refl
    in nothingNotJustBoundary (trans (sym reduced) raw)

0 divertInactiveImpossible :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (tag : RuleTag) -> (afterState : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq}
    (the (Action name key value world error) (LDivert actor))
    (MkSystemState ambient source) = Just (tag, afterState) ->
  InactiveRegistryFiberAt name key world error value nameEq actor source -> Void
divertInactiveImpossible nameEq keyEq actor ambient source tag afterState raw
  (MkInactiveRegistryFiberAt component parent retiredFlag table outcome found) =
    let 0 reduced : (applyAction @{nameEq} @{keyEq}
          (the (Action name key value world error) (LDivert actor))
          (MkSystemState ambient source) = Nothing)
        reduced = rewrite found in Refl
    in nothingNotJustBoundary (trans (sym reduced) raw)

0 leaveInactiveImpossible :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (tag : RuleTag) -> (afterState : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq}
    (the (Action name key value world error) (LLeave actor))
    (MkSystemState ambient source) = Just (tag, afterState) ->
  InactiveRegistryFiberAt name key world error value nameEq actor source -> Void
leaveInactiveImpossible nameEq keyEq actor ambient source tag afterState raw
  (MkInactiveRegistryFiberAt component parent retiredFlag table outcome found) =
    let 0 reduced : (applyAction @{nameEq} @{keyEq}
          (the (Action name key value world error) (LLeave actor))
          (MkSystemState ambient source) = Nothing)
        reduced = rewrite found in Refl
    in nothingNotJustBoundary (trans (sym reduced) raw)

0 unloadInactiveImpossible :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (ambient : world) -> (source : Registry name key value world error) ->
  (tag : RuleTag) -> (afterState : SystemState name key value world error) ->
  applyAction @{nameEq} @{keyEq}
    (the (Action name key value world error) (LUnload actor))
    (MkSystemState ambient source) = Just (tag, afterState) ->
  InactiveRegistryFiberAt name key world error value nameEq actor source -> Void
unloadInactiveImpossible nameEq keyEq actor ambient source tag afterState raw
  (MkInactiveRegistryFiberAt component parent retiredFlag table outcome found) =
    let 0 reduced : (applyAction @{nameEq} @{keyEq}
          (the (Action name key value world error) (LUnload actor))
          (MkSystemState ambient source) = Nothing)
        reduced = rewrite found in Refl
    in nothingNotJustBoundary (trans (sym reduced) raw)

0 ltIrreflexiveDeletedBoundary : (n : Nat) -> LT n n -> Void
ltIrreflexiveDeletedBoundary Z less impossible
ltIrreflexiveDeletedBoundary (S n) (LTESucc less) =
  ltIrreflexiveDeletedBoundary n less

0 inactiveDeletedSuffixImpossible :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (actor : name) -> (generation : RegistrationGeneration name) ->
  lookupCurrentGeneration @{nameEq} actor live = Just generation ->
  Elem generation registered ->
  (blockedAction : Action name key value world error) ->
  (original, survivor : SystemState name key value world error) ->
  (boundary : NoEpisodeReplayBoundary name key world error value nameEq keyEq
    registered live original survivor) ->
  {originalAfter : SystemState name key value world error} ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} blockedAction original =
    Just (tag, originalAfter)) ->
  ((ambient : world) -> (source : Registry name key value world error) ->
    applyAction @{nameEq} @{keyEq} blockedAction
      (MkSystemState ambient source) = Just (tag, originalAfter) ->
    InactiveRegistryFiberAt name key world error value nameEq actor source ->
    Void) ->
  NoEpisodeReplayBoundary name key world error value nameEq keyEq registered
    live originalAfter survivor
inactiveDeletedSuffixImpossible nameEq keyEq registered ordinal live actor
  generation owned member blockedAction original survivor boundary tag checked
  contradiction = case boundary of
    MkNoEpisodeReplayBoundary ambient source originalShape
      (MkCompleteCurrentRegisteredPlanResult
        planResult@(MkCurrentRegisteredPlanResult target plan outside) complete)
      survivorAmbient survivorBindings unique sourceWellFormed
      survivorWellFormed => case originalShape of
        Refl =>
          let 0 currentEntry = currentGenerationEntryFromLookup nameEq actor
                generation live owned
              0 planMember = complete actor generation currentEntry member
              0 inactive = inactiveRegistryFromPlanMember nameEq actor source
                target plan planMember
              0 raw = checkedActionProjects nameEq keyEq blockedAction
                (MkSystemState ambient source) originalAfter tag checked
          in void (contradiction ambient source raw inactive)

||| Exhaustive deleted-head boundary step for the no-selected-episode suffix.
||| Fresh insertion contradicts the registered birth bound; L-Begin contradicts
||| `NoRegisteredEpisode`; the other lifecycle actions cannot fire from the
||| exact Inactive plan leaf.  Only idempotent O-Retire and exact O-Remove remain.
public export
0 deletedSuffixHeadPreservesNoEpisodeBoundary :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  RegisteredGenerationsBornBefore registered ordinal ->
  (action : Action name key value world error) ->
  (original, survivor : SystemState name key value world error) ->
  (boundary : NoEpisodeReplayBoundary name key world error value nameEq keyEq
    registered live original survivor) ->
  {originalAfter : SystemState name key value world error} ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action original =
    Just (tag, originalAfter)) ->
  (deleted : GenerationOwnedActor nameEq registered ordinal live action) ->
  (noBegin : IsBeginAction action ->
    GenerationOwnedActor nameEq registered ordinal live action -> Void) ->
  NoEpisodeReplayBoundary name key world error value nameEq keyEq registered
    (advanceGenerationEnvironment @{nameEq} ordinal action live)
    originalAfter survivor
deletedSuffixHeadPreservesNoEpisodeBoundary {name} {key} {world} {error} {value}
  nameEq keyEq registered ordinal live bornBefore action original survivor
  boundary tag checked deleted noBegin = case action of
    OInsert inserted parent component =>
      case deleted of
        (generation ** (owned, member)) => case justInjective owned of
          Refl => void (ltIrreflexiveDeletedBoundary ordinal
            (bornBefore (MkRegistrationGeneration inserted ordinal) member))
    ORetire actor => deletedRetirePreservesNoEpisodeBoundary nameEq keyEq
      registered ordinal live actor original survivor boundary tag checked deleted
    ORemove actor => deletedRemovePreservesNoEpisodeBoundary nameEq keyEq
      registered ordinal live actor original survivor boundary tag checked deleted
    LBegin actor => void (noBegin ItIsLBegin deleted)
    LAdvance actor => case deleted of
      (generation ** (owned, member)) => inactiveDeletedSuffixImpossible nameEq
        keyEq registered ordinal live actor generation owned member
        (LAdvance actor) original survivor boundary tag checked
        (\ambient, source, raw, inactive =>
          advanceInactiveImpossible nameEq keyEq actor ambient source tag
            originalAfter raw inactive)
    LDivert actor => case deleted of
      (generation ** (owned, member)) => inactiveDeletedSuffixImpossible nameEq
        keyEq registered ordinal live actor generation owned member
        (LDivert actor) original survivor boundary tag checked
        (\ambient, source, raw, inactive =>
          divertInactiveImpossible nameEq keyEq actor ambient source tag
            originalAfter raw inactive)
    LLeave actor => case deleted of
      (generation ** (owned, member)) => inactiveDeletedSuffixImpossible nameEq
        keyEq registered ordinal live actor generation owned member
        (LLeave actor) original survivor boundary tag checked
        (\ambient, source, raw, inactive =>
          leaveInactiveImpossible nameEq keyEq actor ambient source tag
            originalAfter raw inactive)
    LUnload actor => case deleted of
      (generation ** (owned, member)) => inactiveDeletedSuffixImpossible nameEq
        keyEq registered ordinal live actor generation owned member
        (LUnload actor) original survivor boundary tag checked
        (\ambient, source, raw, inactive =>
          unloadInactiveImpossible nameEq keyEq actor ambient source tag
            originalAfter raw inactive)
