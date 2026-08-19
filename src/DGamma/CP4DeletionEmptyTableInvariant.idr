module DGamma.CP4DeletionEmptyTableInvariant

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionGenerationUnique
import DGamma.CP4DeletionInactiveInvariant
import Data.List.Elem
import Decidable.Equality

%default total

||| Every currently live exact R generation has an empty runtime table.  The
||| formulation is conditional on the concrete lookup so it remains stable when
||| the same finite environment is viewed after one of its actors is deleted.
public export
0 CurrentRegisteredEmptyTables :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) ->
  List (RegistrationGeneration name) -> GenerationEnvironment name ->
  SystemState name key value world error -> Type
CurrentRegisteredEmptyTables name key world error value nameEq registered live
  state =
    (selected : name) -> (generation : RegistrationGeneration name) ->
    Elem generation registered ->
    lookupCurrentGeneration @{nameEq} selected live = Just generation ->
    (fiber : Fiber name key value world error) ->
    lookupFiber @{nameEq} selected (registry state) = Just fiber ->
    bindings (ownedValues (fiberTable fiber)) = []

0 emptyTableForeignStep :
  (nameEq : DecEq name) -> (selected : name) ->
  (action : Action name key value world error) ->
  Not (selected = actionOwner action) ->
  (before, afterState : SystemState name key value world error) ->
  (update : SystemLocalUpdate name key world error value nameEq
    (actionOwner action) before afterState) ->
  (sourceEmpty : (fiber : Fiber name key value world error) ->
    lookupFiber @{nameEq} selected (registry before) = Just fiber ->
    bindings (ownedValues (fiberTable fiber)) = []) ->
  (targetFiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} selected (registry afterState) = Just targetFiber ->
  bindings (ownedValues (fiberTable targetFiber)) = []
emptyTableForeignStep nameEq selected action distinct before afterState update
  sourceEmpty targetFiber targetFound =
    let 0 lookupSame = systemLocalUpdateForeign nameEq selected
          (actionOwner action) distinct before afterState update
        0 sourceFound : (lookupFiber @{nameEq} selected (registry before) =
          Just targetFiber)
        sourceFound = trans (sym lookupSame) targetFound
    in sourceEmpty targetFiber sourceFound

0 insertedTargetEmpty :
  (nameEq : DecEq name) -> (selected : name) ->
  (component : Component key value world error) -> (parent : Parent name) ->
  (source : Registry name key value world error) ->
  (absent : lookupFiber @{nameEq} selected source = Nothing) ->
  (targetFiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} selected
    (insertBinding @{nameEq} selected (freshFiber component parent) source
      absent) = Just targetFiber ->
  bindings (ownedValues (fiberTable targetFiber)) = []
insertedTargetEmpty nameEq selected component parent source absent targetFiber
  targetFound =
    let 0 insertedFound = lookupInserted selected (freshFiber component parent)
          source absent
        0 targetSame : (freshFiber component parent = targetFiber)
        targetSame = justInjective (trans (sym insertedFound) targetFound)
    in case targetSame of Refl => Refl

0 retireExactTargetLookup :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (fiber : Fiber name key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  lookupFiber @{nameEq} selected (registry before) = Just fiber ->
  applyAction @{nameEq} @{keyEq} (ORetire selected) before =
    Just (tag, afterState) ->
  lookupFiber @{nameEq} selected (registry afterState) =
    Just (retireFiber fiber)
retireExactTargetLookup nameEq keyEq selected fiber
  (MkSystemState ambient source) afterState tag found raw
  with (lookupFiber @{nameEq} selected source) proof observed
  retireExactTargetLookup nameEq keyEq selected fiber
    (MkSystemState ambient source) afterState tag found raw | Nothing =
      void (nothingIsNotJust raw)
  retireExactTargetLookup nameEq keyEq selected fiber
    (MkSystemState ambient source) afterState tag found raw |
    Just oldFiber =
      let 0 oldSame : (oldFiber = fiber)
          oldSame = justInjective found
          0 pairSame : ((ORetireTag,
                MkSystemState ambient
                  (replaceBinding @{nameEq} selected (retireFiber oldFiber)
                    source)) = (tag, afterState))
          pairSame = justInjective raw
      in case oldSame of
        Refl => case pairSame of
          Refl => lookupReplacedFiber selected fiber (retireFiber fiber) source
            observed

0 retiredFiberTableBindings :
  (fiber : Fiber name key value world error) ->
  bindings (ownedValues (fiberTable (retireFiber fiber))) =
    bindings (ownedValues (fiberTable fiber))
retiredFiberTableBindings
  (MkFiber component parent retiredFlag table lifecycle) = Refl

0 retiredTargetEmpty :
  (nameEq : DecEq name) -> (selected : name) ->
  (source : Registry name key value world error) ->
  (oldFiber : Fiber name key value world error) ->
  (oldFound : lookupFiber @{nameEq} selected source = Just oldFiber) ->
  bindings (ownedValues (fiberTable oldFiber)) = [] ->
  (targetFiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} selected
    (replaceBinding @{nameEq} selected (retireFiber oldFiber) source) =
      Just targetFiber ->
  bindings (ownedValues (fiberTable targetFiber)) = []
retiredTargetEmpty nameEq selected source oldFiber oldFound oldEmpty targetFiber
  targetFound =
    let 0 retiredFound = lookupReplacedFiber selected oldFiber
          (retireFiber oldFiber) source oldFound
        0 targetSame : (retireFiber oldFiber = targetFiber)
        targetSame = justInjective (trans (sym retiredFound) targetFound)
    in case targetSame of
      Refl => trans (retiredFiberTableBindings oldFiber) oldEmpty

||| One checked head preserves exact-R table emptiness.  The existing Inactive
||| invariant eliminates every R-owned lifecycle rule, while O-Insert creates
||| the canonical empty table and O-Retire leaves table bindings untouched.
public export
0 currentRegisteredEmptyTableStep :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  GenerationEnvironmentNamesUnique live ->
  (action : Action name key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} action before = Just (tag, afterState) ->
  (noBegin : IsBeginAction action ->
    GenerationOwnedActor nameEq registered ordinal live action -> Void) ->
  CurrentRegisteredInactiveFibers name key world error value nameEq registered
    live before ->
  CurrentRegisteredEmptyTables name key world error value nameEq registered live
    before ->
  CurrentRegisteredEmptyTables name key world error value nameEq registered
    (advanceGenerationEnvironment @{nameEq} ordinal action live) afterState
currentRegisteredEmptyTableStep nameEq keyEq registered ordinal live unique
  action before afterState tag raw noBegin sourceInactive sourceEmpty selected
  generation member current targetFiber targetFound
  with (decEq @{nameEq} selected (actionOwner action))
  currentRegisteredEmptyTableStep nameEq keyEq registered ordinal live unique
    action before afterState tag raw noBegin sourceInactive sourceEmpty selected
    generation member current targetFiber targetFound | No distinct =
      let 0 sourceCurrent : (lookupCurrentGeneration @{nameEq} selected live =
            Just generation)
          sourceCurrent = trans
            (sym (lookupAdvanceGenerationOther nameEq ordinal action selected
              distinct live)) current
          0 update : SystemLocalUpdate name key world error value nameEq
            (actionOwner action) before afterState
          update = applyActionLocalUpdate nameEq keyEq action before afterState
            tag raw
      in emptyTableForeignStep nameEq selected action distinct before afterState
        update (\fiber, found => sourceEmpty selected generation member
          sourceCurrent fiber found) targetFiber targetFound
  currentRegisteredEmptyTableStep nameEq keyEq registered ordinal live unique
    (OInsert selected parent component) before afterState tag raw noBegin
    sourceInactive sourceEmpty selected generation member current targetFiber
    targetFound | Yes Refl =
      let 0 insertedFound = oInsertResultLookup nameEq keyEq selected parent
            component before afterState tag raw
          0 targetSame : (freshFiber component parent = targetFiber)
          targetSame = justInjective (trans (sym insertedFound) targetFound)
      in case targetSame of Refl => Refl
  currentRegisteredEmptyTableStep nameEq keyEq registered ordinal live unique
    (ORetire selected) before afterState tag raw noBegin sourceInactive
    sourceEmpty selected generation member current targetFiber targetFound |
    Yes Refl =
      case sourceInactive selected generation member current of
        MkInactiveFiberAt component parent retiredFlag table outcome oldFound =>
          let 0 retiredFound = retireExactTargetLookup nameEq keyEq selected
                (MkFiber component parent retiredFlag table (Inactive outcome))
                before afterState tag oldFound raw
              0 targetSame :
                (retireFiber
                  (MkFiber component parent retiredFlag table (Inactive outcome))
                 = targetFiber)
              targetSame = justInjective
                (trans (sym retiredFound) targetFound)
              0 oldEmpty : bindings (ownedValues table) = []
              oldEmpty = sourceEmpty selected generation member current
                (MkFiber component parent retiredFlag table (Inactive outcome))
                oldFound
          in case targetSame of
            Refl => trans
              (retiredFiberTableBindings
                (MkFiber component parent retiredFlag table (Inactive outcome)))
              oldEmpty
  currentRegisteredEmptyTableStep nameEq keyEq registered ordinal live unique
    (ORemove selected) before afterState tag raw noBegin sourceInactive
    sourceEmpty selected generation member current targetFiber targetFound |
    Yes Refl =
      void (nothingIsNotJust
        (trans (sym (lookupDeleteCurrentSelf nameEq selected live unique))
          current))
  currentRegisteredEmptyTableStep nameEq keyEq registered ordinal live unique
    (LBegin selected) before afterState tag raw noBegin sourceInactive sourceEmpty
    selected generation member current targetFiber targetFound | Yes Refl =
      void (noBegin ItIsLBegin (generation ** (current, member)))
  currentRegisteredEmptyTableStep nameEq keyEq registered ordinal live unique
    (LAdvance selected) before afterState tag raw noBegin sourceInactive
    sourceEmpty selected generation member current targetFiber targetFound |
    Yes Refl = void (inactiveCannotAdvance nameEq keyEq selected before afterState
      tag raw (sourceInactive selected generation member current))
  currentRegisteredEmptyTableStep nameEq keyEq registered ordinal live unique
    (LDivert selected) before afterState tag raw noBegin sourceInactive
    sourceEmpty selected generation member current targetFiber targetFound |
    Yes Refl = void (inactiveCannotDivert nameEq keyEq selected before afterState
      tag raw (sourceInactive selected generation member current))
  currentRegisteredEmptyTableStep nameEq keyEq registered ordinal live unique
    (LLeave selected) before afterState tag raw noBegin sourceInactive sourceEmpty
    selected generation member current targetFiber targetFound | Yes Refl =
      void (inactiveCannotLeave nameEq keyEq selected before afterState tag raw
        (sourceInactive selected generation member current))
  currentRegisteredEmptyTableStep nameEq keyEq registered ordinal live unique
    (LUnload selected) before afterState tag raw noBegin sourceInactive
    sourceEmpty selected generation member current targetFiber targetFound |
    Yes Refl = void (inactiveCannotUnload nameEq keyEq selected before afterState
      tag raw (sourceInactive selected generation member current))

||| Simultaneous trace induction with the proved Inactive invariant.
public export
0 currentRegisteredEmptyTableTrace :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  GenerationEnvironmentNamesUnique live ->
  (trace : Transitions first finalState) ->
  (finalOrdinal : Nat) -> (finalLive : GenerationEnvironment name) ->
  GenerationTraceScan nameEq ordinal live trace finalOrdinal finalLive ->
  AlignedTransitions name key world error value nameEq keyEq trace ->
  NoRegisteredEpisode nameEq registered ordinal live trace ->
  CurrentRegisteredInactiveFibers name key world error value nameEq registered
    live first ->
  CurrentRegisteredEmptyTables name key world error value nameEq registered live
    first ->
  CurrentRegisteredEmptyTables name key world error value nameEq registered
    finalLive finalState
currentRegisteredEmptyTableTrace nameEq keyEq registered ordinal live unique
  NoTransitions ordinal live GenerationTraceScanEnd AlignedEnd
  NoRegisteredEpisodeEnd sourceInactive sourceEmpty = sourceEmpty
currentRegisteredEmptyTableTrace nameEq keyEq registered ordinal live unique
  (MoreTransitions (Fired nameEq keyEq action tag checked) rest)
  finalOrdinal finalLive
  (GenerationTraceScanStep (Fired nameEq keyEq action tag checked) rest scanTail)
  (AlignedStep action tag checked rest alignedTail)
  (NoRegisteredEpisodeStep (Fired nameEq keyEq action tag checked) rest noBegin
    noEpisodeTail)
  sourceInactive sourceEmpty =
    let 0 raw = checkedActionProjects nameEq keyEq action _ _ tag checked
        0 nextInactive = currentRegisteredInactiveStep nameEq keyEq registered
          ordinal live unique action _ _ tag raw noBegin sourceInactive
        0 nextEmpty = currentRegisteredEmptyTableStep nameEq keyEq registered
          ordinal live unique action _ _ tag raw noBegin sourceInactive
          sourceEmpty
        0 nextUnique = advanceGenerationEnvironmentPreservesUnique nameEq ordinal
          action live unique
    in currentRegisteredEmptyTableTrace nameEq keyEq registered (S ordinal)
      (advanceGenerationEnvironment @{nameEq} ordinal action live) nextUnique rest
      finalOrdinal finalLive scanTail alignedTail noEpisodeTail nextInactive
      nextEmpty

0 emptyCurrentRegisteredTables :
  CurrentRegisteredEmptyTables name key world error value nameEq registered []
    state
emptyCurrentRegisteredTables selected generation member current fiber found =
  case current of Refl impossible

||| Public empty-start specialization used directly by Lemma 72.
public export
0 reachedCurrentRegisteredEmptyTables :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (registered : List (RegistrationGeneration name)) ->
  (trace : Transitions initial finalState) ->
  (finalOrdinal : Nat) -> (finalLive : GenerationEnvironment name) ->
  GenerationTraceScan nameEq 0 [] trace finalOrdinal finalLive ->
  AlignedTransitions name key world error value nameEq keyEq trace ->
  NoRegisteredEpisode nameEq registered 0 [] trace ->
  CurrentRegisteredEmptyTables name key world error value nameEq registered
    finalLive finalState
reachedCurrentRegisteredEmptyTables nameEq keyEq registered trace finalOrdinal
  finalLive scan aligned noEpisodes =
    currentRegisteredEmptyTableTrace nameEq keyEq registered 0 [] UniqueNil trace
      finalOrdinal finalLive scan aligned noEpisodes
      (\selected, generation, member, current => case current of Refl impossible)
      emptyCurrentRegisteredTables
