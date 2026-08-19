module DGamma.CP4DeletionInactiveInvariant

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionGenerationUnique
import Data.List.Elem
import Decidable.Equality

%default total

0 justInjectiveInactive : Just left = Just right -> left = right
justInjectiveInactive Refl = Refl

public export
0 lookupPutCurrentSelf :
  (nameEq : DecEq name) -> (selected : name) ->
  (generation : RegistrationGeneration name) ->
  (live : GenerationEnvironment name) ->
  lookupCurrentGeneration @{nameEq} selected
    (putCurrentGeneration @{nameEq} selected generation live) = Just generation
lookupPutCurrentSelf nameEq selected generation []
  with (decEq @{nameEq} selected selected)
  lookupPutCurrentSelf nameEq selected generation [] | Yes Refl = Refl
  lookupPutCurrentSelf nameEq selected generation [] | No contra =
    void (contra Refl)
lookupPutCurrentSelf nameEq selected generation
  ((candidate, current) :: rest)
  with (decEq @{nameEq} selected candidate) proof decision
  lookupPutCurrentSelf nameEq candidate generation
    ((candidate, current) :: rest) | Yes Refl
    with (decEq @{nameEq} candidate candidate)
    lookupPutCurrentSelf nameEq candidate generation
      ((candidate, current) :: rest) | Yes Refl | Yes Refl = Refl
    lookupPutCurrentSelf nameEq candidate generation
      ((candidate, current) :: rest) | Yes Refl | No contra = void (contra Refl)
  lookupPutCurrentSelf nameEq selected generation
    ((candidate, current) :: rest) | No different =
      rewrite decision in lookupPutCurrentSelf nameEq selected generation rest

public export
0 lookupPutCurrentOther :
  (nameEq : DecEq name) -> (observed, inserted : name) ->
  Not (observed = inserted) ->
  (generation : RegistrationGeneration name) ->
  (live : GenerationEnvironment name) ->
  lookupCurrentGeneration @{nameEq} observed
    (putCurrentGeneration @{nameEq} inserted generation live) =
  lookupCurrentGeneration @{nameEq} observed live
lookupPutCurrentOther nameEq observed inserted distinct generation []
  with (decEq @{nameEq} observed inserted)
  lookupPutCurrentOther nameEq inserted inserted distinct generation [] |
    Yes Refl = void (distinct Refl)
  lookupPutCurrentOther nameEq observed inserted distinct generation [] |
    No different = Refl
lookupPutCurrentOther nameEq observed inserted distinct generation
  ((candidate, current) :: rest) with (decEq @{nameEq} inserted candidate)
  lookupPutCurrentOther nameEq observed candidate distinct generation
    ((candidate, current) :: rest) | Yes Refl
    with (decEq @{nameEq} observed candidate)
    lookupPutCurrentOther nameEq candidate candidate distinct generation
      ((candidate, current) :: rest) | Yes Refl | Yes Refl = void (distinct Refl)
    lookupPutCurrentOther nameEq observed candidate distinct generation
      ((candidate, current) :: rest) | Yes Refl | No observedDifferent = Refl
  lookupPutCurrentOther nameEq observed inserted distinct generation
    ((candidate, current) :: rest) | No insertedDifferent
    with (decEq @{nameEq} observed candidate)
    lookupPutCurrentOther nameEq candidate inserted distinct generation
      ((candidate, current) :: rest) | No insertedDifferent | Yes Refl = Refl
    lookupPutCurrentOther nameEq observed inserted distinct generation
      ((candidate, current) :: rest) | No insertedDifferent |
      No observedDifferent =
        lookupPutCurrentOther nameEq observed inserted distinct generation rest

0 lookupCurrentNothingFromAbsent :
  (nameEq : DecEq name) -> (selected : name) ->
  (live : GenerationEnvironment name) ->
  Not (Elem selected (generationEnvironmentNames live)) ->
  lookupCurrentGeneration @{nameEq} selected live = Nothing
lookupCurrentNothingFromAbsent nameEq selected [] absent = Refl
lookupCurrentNothingFromAbsent nameEq selected
  ((candidate, current) :: rest) absent
  with (decEq @{nameEq} selected candidate) proof decision
  lookupCurrentNothingFromAbsent nameEq candidate
    ((candidate, current) :: rest) absent | Yes Refl = void (absent Here)
  lookupCurrentNothingFromAbsent nameEq selected
    ((candidate, current) :: rest) absent | No different =
      lookupCurrentNothingFromAbsent nameEq selected rest
        (\present => absent (There present))

public export
0 lookupDeleteCurrentSelf :
  (nameEq : DecEq name) -> (selected : name) ->
  (live : GenerationEnvironment name) ->
  GenerationEnvironmentNamesUnique live ->
  lookupCurrentGeneration @{nameEq} selected
    (deleteCurrentGeneration @{nameEq} selected live) = Nothing
lookupDeleteCurrentSelf nameEq selected [] UniqueNil = Refl
lookupDeleteCurrentSelf nameEq selected ((candidate, current) :: rest)
  (UniqueCons candidateFresh restUnique)
  with (decEq @{nameEq} selected candidate) proof decision
  lookupDeleteCurrentSelf nameEq candidate ((candidate, current) :: rest)
    (UniqueCons candidateFresh restUnique) | Yes Refl =
      lookupCurrentNothingFromAbsent nameEq candidate rest candidateFresh
  lookupDeleteCurrentSelf nameEq selected ((candidate, current) :: rest)
    (UniqueCons candidateFresh restUnique) | No different =
      rewrite decision in lookupDeleteCurrentSelf nameEq selected rest restUnique

0 lookupDeleteCurrentOther :
  (nameEq : DecEq name) -> (observed, removed : name) ->
  Not (observed = removed) ->
  (live : GenerationEnvironment name) ->
  lookupCurrentGeneration @{nameEq} observed
    (deleteCurrentGeneration @{nameEq} removed live) =
  lookupCurrentGeneration @{nameEq} observed live
lookupDeleteCurrentOther nameEq observed removed distinct [] = Refl
lookupDeleteCurrentOther nameEq observed removed distinct
  ((candidate, current) :: rest) with (decEq @{nameEq} removed candidate)
  lookupDeleteCurrentOther nameEq observed candidate distinct
    ((candidate, current) :: rest) | Yes Refl
    with (decEq @{nameEq} observed candidate)
    lookupDeleteCurrentOther nameEq candidate candidate distinct
      ((candidate, current) :: rest) | Yes Refl | Yes Refl = void (distinct Refl)
    lookupDeleteCurrentOther nameEq observed candidate distinct
      ((candidate, current) :: rest) | Yes Refl | No observedDifferent = Refl
  lookupDeleteCurrentOther nameEq observed removed distinct
    ((candidate, current) :: rest) | No removedDifferent
    with (decEq @{nameEq} observed candidate)
    lookupDeleteCurrentOther nameEq candidate removed distinct
      ((candidate, current) :: rest) | No removedDifferent | Yes Refl = Refl
    lookupDeleteCurrentOther nameEq observed removed distinct
      ((candidate, current) :: rest) | No removedDifferent |
      No observedDifferent =
        lookupDeleteCurrentOther nameEq observed removed distinct rest

public export
0 lookupAdvanceGenerationOther :
  (nameEq : DecEq name) -> (ordinal : Nat) ->
  (action : Action name key value world error) ->
  (observed : name) -> Not (observed = actionOwner action) ->
  (live : GenerationEnvironment name) ->
  lookupCurrentGeneration @{nameEq} observed
    (advanceGenerationEnvironment @{nameEq} ordinal action live) =
  lookupCurrentGeneration @{nameEq} observed live
lookupAdvanceGenerationOther nameEq ordinal
  (OInsert inserted parent component) observed distinct live =
    lookupPutCurrentOther nameEq observed inserted distinct
      (MkRegistrationGeneration inserted ordinal) live
lookupAdvanceGenerationOther nameEq ordinal (ORetire actor) observed distinct
  live = Refl
lookupAdvanceGenerationOther nameEq ordinal (ORemove removed) observed distinct
  live = lookupDeleteCurrentOther nameEq observed removed distinct live
lookupAdvanceGenerationOther nameEq ordinal (LBegin actor) observed distinct
  live = Refl
lookupAdvanceGenerationOther nameEq ordinal (LAdvance actor) observed distinct
  live = Refl
lookupAdvanceGenerationOther nameEq ordinal (LDivert actor) observed distinct
  live = Refl
lookupAdvanceGenerationOther nameEq ordinal (LLeave actor) observed distinct
  live = Refl
lookupAdvanceGenerationOther nameEq ordinal (LUnload actor) observed distinct
  live = Refl

public export
record InactiveFiberAt
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (selected : name)
  (state : SystemState name key value world error) where
  constructor MkInactiveFiberAt
  inactiveComponent : Component key value world error
  inactiveParent : Parent name
  inactiveRetired : Bool
  inactiveTable : OwnedTable key value (componentProvisions inactiveComponent)
  inactiveOutcome : Maybe error
  0 inactiveFound : lookupFiber @{nameEq} selected (registry state) =
    Just (MkFiber inactiveComponent inactiveParent inactiveRetired inactiveTable
      (Inactive inactiveOutcome))

public export
CurrentRegisteredInactiveFibers :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) ->
  List (RegistrationGeneration name) -> GenerationEnvironment name ->
  SystemState name key value world error -> Type
CurrentRegisteredInactiveFibers name key world error value nameEq registered live
  state =
    (selected : name) -> (generation : RegistrationGeneration name) ->
    Elem generation registered ->
    lookupCurrentGeneration @{nameEq} selected live = Just generation ->
    InactiveFiberAt name key world error value nameEq selected state

0 inactiveFiberForeign :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected : name) ->
  (action : Action name key value world error) ->
  Not (selected = actionOwner action) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} action before = Just (tag, afterState) ->
  InactiveFiberAt name key world error value nameEq selected before ->
  InactiveFiberAt name key world error value nameEq selected afterState
inactiveFiberForeign nameEq keyEq selected action distinct before afterState tag
  raw (MkInactiveFiberAt component parent retiredFlag table outcome found) =
    let update = applyActionLocalUpdate nameEq keyEq action before afterState tag raw
        targetFound = trans
          (systemLocalUpdateForeign nameEq selected (actionOwner action) distinct
            before afterState update)
          found
    in MkInactiveFiberAt component parent retiredFlag table outcome targetFound

0 insertedInactiveTarget :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected : name) -> (parent : Parent name) ->
  (component : Component key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (OInsert selected parent component) before =
    Just (tag, afterState) ->
  InactiveFiberAt name key world error value nameEq selected afterState
insertedInactiveTarget nameEq keyEq selected parent component before afterState
  tag raw = MkInactiveFiberAt component parent False emptyOwned Nothing
    (oInsertResultLookup nameEq keyEq selected parent component before afterState
      tag raw)

0 retiredInactiveTarget :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (ORetire selected) before =
    Just (tag, afterState) ->
  InactiveFiberAt name key world error value nameEq selected before ->
  InactiveFiberAt name key world error value nameEq selected afterState
retiredInactiveTarget nameEq keyEq selected
  before@(MkSystemState ambient fibers) afterState tag raw inactive
  with (lookupFiber @{nameEq} selected fibers) proof observed
  retiredInactiveTarget nameEq keyEq selected
    before@(MkSystemState ambient fibers) afterState tag raw
    (MkInactiveFiberAt component parent retiredFlag table outcome found) |
    Nothing = void (nothingIsNotJust (trans (sym observed) found))
  retiredInactiveTarget nameEq keyEq selected
    before@(MkSystemState ambient fibers) afterState tag raw
    (MkInactiveFiberAt component parent retiredFlag table outcome found) |
    Just actual =
      case justInjectiveInactive (trans (sym observed) found) of
        Refl => case justInjectiveInactive raw of
          Refl => MkInactiveFiberAt component parent True table outcome
            (lookupReplacedFiber selected
              (MkFiber component parent retiredFlag table (Inactive outcome))
              (retireFiber
                (MkFiber component parent retiredFlag table (Inactive outcome)))
              fibers found)

0 falseNotTrueInactive : False = True -> Void
falseNotTrueInactive Refl impossible

0 inactiveReloadingFalse :
  (nameEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  (component : Component key value world error) ->
  (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (outcome : Maybe error) ->
  lookupFiber @{nameEq} selected (registry state) =
    Just (MkFiber component parent retiredFlag table (Inactive outcome)) ->
  reloadingAt @{nameEq} selected state = False
inactiveReloadingFalse nameEq selected state component parent retiredFlag table
  outcome found = rewrite found in Refl

0 inactiveActiveFalse :
  (nameEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  (component : Component key value world error) ->
  (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (outcome : Maybe error) ->
  lookupFiber @{nameEq} selected (registry state) =
    Just (MkFiber component parent retiredFlag table (Inactive outcome)) ->
  activeAt @{nameEq} selected state = False
inactiveActiveFalse nameEq selected state component parent retiredFlag table
  outcome found = rewrite found in Refl

0 inactiveUnloadingFalse :
  (nameEq : DecEq name) -> (selected : name) ->
  (state : SystemState name key value world error) ->
  (component : Component key value world error) ->
  (parent : Parent name) -> (retiredFlag : Bool) ->
  (table : OwnedTable key value (componentProvisions component)) ->
  (outcome : Maybe error) ->
  lookupFiber @{nameEq} selected (registry state) =
    Just (MkFiber component parent retiredFlag table (Inactive outcome)) ->
  unloadingAt @{nameEq} selected state = False
inactiveUnloadingFalse nameEq selected state component parent retiredFlag table
  outcome found = rewrite found in Refl

0 advanceSourceReloading :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (LAdvance selected) before =
    Just (tag, afterState) ->
  reloadingAt @{nameEq} selected before = True
advanceSourceReloading nameEq keyEq selected (MkSystemState ambient fibers)
  afterState tag raw with (lookupFiber @{nameEq} selected fibers)
  advanceSourceReloading nameEq keyEq selected (MkSystemState ambient fibers)
    afterState tag raw | Nothing = void (nothingIsNotJust raw)
  advanceSourceReloading nameEq keyEq selected (MkSystemState ambient fibers)
    afterState tag raw | Just fiber with (fiberLifecycle fiber)
    advanceSourceReloading nameEq keyEq selected (MkSystemState ambient fibers)
      afterState tag raw | Just fiber | Inactive outcome =
        void (nothingIsNotJust raw)
    advanceSourceReloading nameEq keyEq selected (MkSystemState ambient fibers)
      afterState tag raw | Just fiber | Reloading remaining accumulator view = Refl
    advanceSourceReloading nameEq keyEq selected (MkSystemState ambient fibers)
      afterState tag raw | Just fiber | Active accumulator view =
        void (nothingIsNotJust raw)
    advanceSourceReloading nameEq keyEq selected (MkSystemState ambient fibers)
      afterState tag raw | Just fiber | Unloading accumulator view outcome =
        void (nothingIsNotJust raw)

0 divertSourceReloading :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (LDivert selected) before =
    Just (tag, afterState) ->
  reloadingAt @{nameEq} selected before = True
divertSourceReloading nameEq keyEq selected (MkSystemState ambient fibers)
  afterState tag raw with (lookupFiber @{nameEq} selected fibers)
  divertSourceReloading nameEq keyEq selected (MkSystemState ambient fibers)
    afterState tag raw | Nothing = void (nothingIsNotJust raw)
  divertSourceReloading nameEq keyEq selected (MkSystemState ambient fibers)
    afterState tag raw | Just fiber with (fiberLifecycle fiber)
    divertSourceReloading nameEq keyEq selected (MkSystemState ambient fibers)
      afterState tag raw | Just fiber | Inactive outcome =
        void (nothingIsNotJust raw)
    divertSourceReloading nameEq keyEq selected (MkSystemState ambient fibers)
      afterState tag raw | Just fiber | Reloading remaining accumulator view
      with (targetMatches @{nameEq}
        (targetFiber @{nameEq} @{keyEq} fiber fibers) view)
      divertSourceReloading nameEq keyEq selected (MkSystemState ambient fibers)
        afterState tag raw | Just fiber | Reloading remaining accumulator view |
        True = void (nothingIsNotJust raw)
      divertSourceReloading nameEq keyEq selected (MkSystemState ambient fibers)
        afterState tag raw | Just fiber | Reloading remaining accumulator view |
        False = Refl
    divertSourceReloading nameEq keyEq selected (MkSystemState ambient fibers)
      afterState tag raw | Just fiber | Active accumulator view =
        void (nothingIsNotJust raw)
    divertSourceReloading nameEq keyEq selected (MkSystemState ambient fibers)
      afterState tag raw | Just fiber | Unloading accumulator view outcome =
        void (nothingIsNotJust raw)

0 leaveSourceActive :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (LLeave selected) before =
    Just (tag, afterState) ->
  activeAt @{nameEq} selected before = True
leaveSourceActive nameEq keyEq selected (MkSystemState ambient fibers)
  afterState tag raw with (lookupFiber @{nameEq} selected fibers)
  leaveSourceActive nameEq keyEq selected (MkSystemState ambient fibers)
    afterState tag raw | Nothing = void (nothingIsNotJust raw)
  leaveSourceActive nameEq keyEq selected (MkSystemState ambient fibers)
    afterState tag raw | Just fiber with (fiberLifecycle fiber)
    leaveSourceActive nameEq keyEq selected (MkSystemState ambient fibers)
      afterState tag raw | Just fiber | Inactive outcome =
        void (nothingIsNotJust raw)
    leaveSourceActive nameEq keyEq selected (MkSystemState ambient fibers)
      afterState tag raw | Just fiber | Reloading remaining accumulator view =
        void (nothingIsNotJust raw)
    leaveSourceActive nameEq keyEq selected (MkSystemState ambient fibers)
      afterState tag raw | Just fiber | Active accumulator view
      with (targetMatches @{nameEq}
        (targetFiber @{nameEq} @{keyEq} fiber fibers) view)
      leaveSourceActive nameEq keyEq selected (MkSystemState ambient fibers)
        afterState tag raw | Just fiber | Active accumulator view | True =
          void (nothingIsNotJust raw)
      leaveSourceActive nameEq keyEq selected (MkSystemState ambient fibers)
        afterState tag raw | Just fiber | Active accumulator view | False = Refl
    leaveSourceActive nameEq keyEq selected (MkSystemState ambient fibers)
      afterState tag raw | Just fiber | Unloading accumulator view outcome =
        void (nothingIsNotJust raw)

0 unloadSourceUnloading :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (LUnload selected) before =
    Just (tag, afterState) ->
  unloadingAt @{nameEq} selected before = True
unloadSourceUnloading nameEq keyEq selected (MkSystemState ambient fibers)
  afterState tag raw with (lookupFiber @{nameEq} selected fibers)
  unloadSourceUnloading nameEq keyEq selected (MkSystemState ambient fibers)
    afterState tag raw | Nothing = void (nothingIsNotJust raw)
  unloadSourceUnloading nameEq keyEq selected (MkSystemState ambient fibers)
    afterState tag raw | Just fiber with (fiberLifecycle fiber)
    unloadSourceUnloading nameEq keyEq selected (MkSystemState ambient fibers)
      afterState tag raw | Just fiber | Inactive outcome =
        void (nothingIsNotJust raw)
    unloadSourceUnloading nameEq keyEq selected (MkSystemState ambient fibers)
      afterState tag raw | Just fiber | Reloading remaining accumulator view =
        void (nothingIsNotJust raw)
    unloadSourceUnloading nameEq keyEq selected (MkSystemState ambient fibers)
      afterState tag raw | Just fiber | Active accumulator view =
        void (nothingIsNotJust raw)
    unloadSourceUnloading nameEq keyEq selected (MkSystemState ambient fibers)
      afterState tag raw | Just fiber | Unloading accumulator view outcome
      with (relied @{nameEq} selected fibers)
      unloadSourceUnloading nameEq keyEq selected (MkSystemState ambient fibers)
        afterState tag raw | Just fiber | Unloading accumulator view outcome |
        True = void (nothingIsNotJust raw)
      unloadSourceUnloading nameEq keyEq selected (MkSystemState ambient fibers)
        afterState tag raw | Just fiber | Unloading accumulator view outcome |
        False = Refl

public export
0 inactiveCannotAdvance :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (LAdvance selected) before =
    Just (tag, afterState) ->
  InactiveFiberAt name key world error value nameEq selected before -> Void
inactiveCannotAdvance nameEq keyEq selected before afterState tag raw
  (MkInactiveFiberAt component parent retiredFlag table outcome found) =
    falseNotTrueInactive (trans
      (sym (inactiveReloadingFalse nameEq selected before component parent
        retiredFlag table outcome found))
      (advanceSourceReloading nameEq keyEq selected before afterState tag raw))

public export
0 inactiveCannotDivert :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (LDivert selected) before =
    Just (tag, afterState) ->
  InactiveFiberAt name key world error value nameEq selected before -> Void
inactiveCannotDivert nameEq keyEq selected before afterState tag raw
  (MkInactiveFiberAt component parent retiredFlag table outcome found) =
    falseNotTrueInactive (trans
      (sym (inactiveReloadingFalse nameEq selected before component parent
        retiredFlag table outcome found))
      (divertSourceReloading nameEq keyEq selected before afterState tag raw))

public export
0 inactiveCannotLeave :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (LLeave selected) before =
    Just (tag, afterState) ->
  InactiveFiberAt name key world error value nameEq selected before -> Void
inactiveCannotLeave nameEq keyEq selected before afterState tag raw
  (MkInactiveFiberAt component parent retiredFlag table outcome found) =
    falseNotTrueInactive (trans
      (sym (inactiveActiveFalse nameEq selected before component parent
        retiredFlag table outcome found))
      (leaveSourceActive nameEq keyEq selected before afterState tag raw))

public export
0 inactiveCannotUnload :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (LUnload selected) before =
    Just (tag, afterState) ->
  InactiveFiberAt name key world error value nameEq selected before -> Void
inactiveCannotUnload nameEq keyEq selected before afterState tag raw
  (MkInactiveFiberAt component parent retiredFlag table outcome found) =
    falseNotTrueInactive (trans
      (sym (inactiveUnloadingFalse nameEq selected before component parent
        retiredFlag table outcome found))
      (unloadSourceUnloading nameEq keyEq selected before afterState tag raw))

public export
0 currentRegisteredInactiveStep :
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
  CurrentRegisteredInactiveFibers name key world error value nameEq registered
    (advanceGenerationEnvironment @{nameEq} ordinal action live) afterState
currentRegisteredInactiveStep nameEq keyEq registered ordinal live unique
  action before afterState tag raw noBegin sourceInvariant selected generation
  member targetCurrent with (decEq @{nameEq} selected (actionOwner action))
  currentRegisteredInactiveStep nameEq keyEq registered ordinal live unique action
    before afterState tag raw noBegin sourceInvariant selected generation member
    targetCurrent | No distinct =
      let sourceCurrent = trans
            (sym (lookupAdvanceGenerationOther nameEq ordinal action selected
              distinct live)) targetCurrent
          sourceInactive = sourceInvariant selected generation member sourceCurrent
      in inactiveFiberForeign nameEq keyEq selected action distinct before afterState
        tag raw sourceInactive
  currentRegisteredInactiveStep nameEq keyEq registered ordinal live
    unique (OInsert selected parent component) before afterState tag raw noBegin
    sourceInvariant selected generation member targetCurrent | Yes Refl =
      let exactCurrent = lookupPutCurrentSelf nameEq selected
            (MkRegistrationGeneration selected ordinal) live
          sameGeneration = justInjectiveInactive
            (trans (sym exactCurrent) targetCurrent)
      in case sameGeneration of
        Refl => insertedInactiveTarget nameEq keyEq selected parent component
          before afterState tag raw
  currentRegisteredInactiveStep nameEq keyEq registered ordinal live
    unique (ORetire selected) before afterState tag raw noBegin sourceInvariant selected
    generation member targetCurrent | Yes Refl =
      retiredInactiveTarget nameEq keyEq selected before afterState tag raw
        (sourceInvariant selected generation member targetCurrent)
  currentRegisteredInactiveStep nameEq keyEq registered ordinal live
    unique (ORemove selected) before afterState tag raw noBegin sourceInvariant selected
    generation member targetCurrent | Yes Refl =
      void (nothingIsNotJust
        (trans (sym (lookupDeleteCurrentSelf nameEq selected live unique))
          targetCurrent))
  currentRegisteredInactiveStep nameEq keyEq registered ordinal live
    unique (LBegin selected) before afterState tag raw noBegin sourceInvariant selected
    generation member targetCurrent | Yes Refl =
      void (noBegin ItIsLBegin (generation ** (targetCurrent, member)))
  currentRegisteredInactiveStep nameEq keyEq registered ordinal live
    unique (LAdvance selected) before afterState tag raw noBegin sourceInvariant selected
    generation member targetCurrent | Yes Refl =
      void (inactiveCannotAdvance nameEq keyEq selected before afterState tag raw
        (sourceInvariant selected generation member targetCurrent))
  currentRegisteredInactiveStep nameEq keyEq registered ordinal live
    unique (LDivert selected) before afterState tag raw noBegin sourceInvariant selected
    generation member targetCurrent | Yes Refl =
      void (inactiveCannotDivert nameEq keyEq selected before afterState tag raw
        (sourceInvariant selected generation member targetCurrent))
  currentRegisteredInactiveStep nameEq keyEq registered ordinal live
    unique (LLeave selected) before afterState tag raw noBegin sourceInvariant selected
    generation member targetCurrent | Yes Refl =
      void (inactiveCannotLeave nameEq keyEq selected before afterState tag raw
        (sourceInvariant selected generation member targetCurrent))
  currentRegisteredInactiveStep nameEq keyEq registered ordinal live
    unique (LUnload selected) before afterState tag raw noBegin sourceInvariant selected
    generation member targetCurrent | Yes Refl =
      void (inactiveCannotUnload nameEq keyEq selected before afterState tag raw
        (sourceInvariant selected generation member targetCurrent))

||| Forward induction over the original trace proves every current exact R
||| generation remains Inactive when that generation has no L-Begin.
public export
0 currentRegisteredInactiveTrace :
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
  CurrentRegisteredInactiveFibers name key world error value nameEq registered
    finalLive finalState
currentRegisteredInactiveTrace nameEq keyEq registered ordinal live unique
  NoTransitions ordinal live GenerationTraceScanEnd AlignedEnd NoRegisteredEpisodeEnd invariant =
    invariant
currentRegisteredInactiveTrace nameEq keyEq registered ordinal live unique
  (MoreTransitions (Fired nameEq keyEq action tag checked) rest)
  finalOrdinal finalLive
  (GenerationTraceScanStep (Fired nameEq keyEq action tag checked) rest scanTail)
  (AlignedStep action tag checked rest alignedTail)
  (NoRegisteredEpisodeStep (Fired nameEq keyEq action tag checked) rest noBegin
    noEpisodeTail)
  invariant =
    let raw = checkedActionProjects nameEq keyEq action _ _ tag checked
        nextInvariant = currentRegisteredInactiveStep nameEq keyEq registered
          ordinal live unique action _ _ tag raw noBegin invariant
        nextUnique = advanceGenerationEnvironmentPreservesUnique nameEq ordinal
          action live unique
    in currentRegisteredInactiveTrace nameEq keyEq registered (S ordinal)
      (advanceGenerationEnvironment @{nameEq} ordinal action live) nextUnique rest
      finalOrdinal finalLive scanTail alignedTail noEpisodeTail nextInvariant

0 emptyCurrentRegisteredInactive :
  CurrentRegisteredInactiveFibers name key world error value nameEq registered []
    state
emptyCurrentRegisteredInactive selected generation member current =
  case current of Refl impossible

||| Public-alias specialization from the empty generation environment.
public export
0 reachedCurrentRegisteredInactive :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (registered : List (RegistrationGeneration name)) ->
  (trace : Transitions initial finalState) ->
  (finalOrdinal : Nat) -> (finalLive : GenerationEnvironment name) ->
  GenerationTraceScan nameEq 0 [] trace finalOrdinal finalLive ->
  AlignedTransitions name key world error value nameEq keyEq trace ->
  NoRegisteredEpisode nameEq registered 0 [] trace ->
  CurrentRegisteredInactiveFibers name key world error value nameEq registered
    finalLive finalState
reachedCurrentRegisteredInactive nameEq keyEq registered trace finalOrdinal
  finalLive scan aligned noEpisodes =
    currentRegisteredInactiveTrace nameEq keyEq registered 0 [] UniqueNil trace
      finalOrdinal finalLive scan aligned noEpisodes
      emptyCurrentRegisteredInactive
