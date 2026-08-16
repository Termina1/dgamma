module DGamma.CP4Support

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total

||| A protocol rank for the immutable component carried by one fiber.
public export
0 FiberProtocolRank : RegistrationProtocol key value world error ->
  Fiber name key value world error -> Type
FiberProtocolRank protocol fiber =
  (rank : Nat ** registrationRank protocol (fiberComponent fiber) = Just rank)

||| Every currently registered generation has a protocol rank.
public export
0 RegistryProtocolRanked : RegistrationProtocol key value world error ->
  (nameEq : DecEq name) -> SystemState name key value world error -> Type
RegistryProtocolRanked protocol nameEq state =
  (selected : name) -> (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} selected (registry state) = Just fiber ->
  FiberProtocolRank protocol fiber

0 lookupNotElemNothing : DecEq key => (wanted : key) ->
  (entries : List (Binding key value)) ->
  Not (Elem wanted (bindingKeys entries)) ->
  lookupEntries wanted entries = Nothing
lookupNotElemNothing wanted [] absent = Refl
lookupNotElemNothing wanted (Bind found value :: rest) absent
  with (decEq wanted found)
  lookupNotElemNothing found (Bind found value :: rest) absent |
    Yes Refl = void (absent Here)
  lookupNotElemNothing wanted (Bind found value :: rest) absent |
    No distinct = lookupNotElemNothing wanted rest (\later => absent (There later))

0 lookupDeleteSelf : DecEq key => (removed : key) ->
  (table : CoeffectContext key value) ->
  lookupBinding removed (deleteBinding removed table) = Nothing
lookupDeleteSelf removed (MkCoeffectContext entries unique) =
  lookupNotElemNothing removed (deleteEntries removed entries)
    (deletedKeyNotElem removed entries unique)

0 RegistryInsertionRank :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (actor : name) ->
  (source, target : Registry name key value world error) -> Type
RegistryInsertionRank protocol nameEq actor source target =
  (fiber : Fiber name key value world error) ->
  (absent : lookupFiber @{nameEq} actor source = Nothing) ->
  target = insertBinding actor fiber source absent ->
  FiberProtocolRank protocol fiber

0 transportFiberRank :
  {protocol : RegistrationProtocol key value world error} ->
  {oldFiber, nextFiber : Fiber name key value world error} ->
  fiberComponent nextFiber = fiberComponent oldFiber ->
  FiberProtocolRank protocol oldFiber ->
  FiberProtocolRank protocol nextFiber
transportFiberRank {protocol} componentSame (rank ** ranked) =
  (rank ** trans (cong (registrationRank protocol) componentSame) ranked)

||| Static-component local updates preserve the rank invariant; insertion asks
||| only for the new component's rank.
public export
0 registryProtocolRankedUpdate :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (actor : name) ->
  (source, target : Registry name key value world error) ->
  (update : RegistryLocalUpdate name key world error value nameEq actor source target) ->
  RegistryInsertionRank protocol nameEq actor source target ->
  ((selected : name) -> (fiber : Fiber name key value world error) ->
    lookupFiber @{nameEq} selected source = Just fiber ->
    FiberProtocolRank protocol fiber) ->
  (selected : name) -> (fiber : Fiber name key value world error) ->
  lookupFiber @{nameEq} selected target = Just fiber ->
  FiberProtocolRank protocol fiber
registryProtocolRankedUpdate protocol nameEq actor source target update inserted
  sourceRanked selected observed targetFound with (decEq @{nameEq} selected actor)
  registryProtocolRankedUpdate protocol nameEq actor source target update inserted
    sourceRanked actor observed targetFound | Yes Refl =
      case update of
        LocalInsert next absent =>
          let nextRanked = inserted next absent Refl
              targetSelf = lookupInserted actor next source absent
              same = justInjective (trans (sym targetSelf) targetFound)
          in replace {p = FiberProtocolRank protocol} same nextRanked
        LocalReplace next {oldFiber} {oldFound} {staticComponent} =>
          let targetSelf = lookupReplacedFiber actor oldFiber next source oldFound
              same = justInjective (trans (sym targetSelf) targetFound)
              nextRanked = transportFiberRank staticComponent
                (sourceRanked actor oldFiber oldFound)
          in replace {p = FiberProtocolRank protocol} same nextRanked
        LocalDelete =>
          void (nothingIsNotJust
            (trans (sym (lookupDeleteSelf actor source)) targetFound))
  registryProtocolRankedUpdate protocol nameEq actor source target update inserted
    sourceRanked selected observed targetFound | No distinct =
      sourceRanked selected observed
        (trans (sym (registryLocalUpdateForeign nameEq selected actor distinct source update))
          targetFound)

0 ExistingAction : Action name key value world error -> Type
ExistingAction (OInsert actor parent component) = Void
ExistingAction (ORetire actor) = ()
ExistingAction (ORemove actor) = ()
ExistingAction (LBegin actor) = ()
ExistingAction (LAdvance actor) = ()
ExistingAction (LDivert actor) = ()
ExistingAction (LLeave actor) = ()
ExistingAction (LUnload actor) = ()

0 successfulExistingActionSource :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  ExistingAction action ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} action before = Just (tag, afterState) ->
  (fiber : Fiber name key value world error **
    lookupFiber @{nameEq} (actionOwner action) (registry before) = Just fiber)
successfulExistingActionSource nameEq keyEq (OInsert actor parent component)
  contra before afterState tag equation = void contra
successfulExistingActionSource nameEq keyEq (ORetire actor) witness
  before afterState tag equation with (lookupFiber @{nameEq} actor (registry before)) proof found
  successfulExistingActionSource nameEq keyEq (ORetire actor) witness
    before afterState tag equation | Nothing = void (nothingIsNotJust equation)
  successfulExistingActionSource nameEq keyEq (ORetire actor) witness
    before afterState tag equation | Just fiber = (fiber ** Refl)
successfulExistingActionSource nameEq keyEq (ORemove actor) witness
  before afterState tag equation with (lookupFiber @{nameEq} actor (registry before)) proof found
  successfulExistingActionSource nameEq keyEq (ORemove actor) witness
    before afterState tag equation | Nothing = void (nothingIsNotJust equation)
  successfulExistingActionSource nameEq keyEq (ORemove actor) witness
    before afterState tag equation | Just fiber = (fiber ** Refl)
successfulExistingActionSource nameEq keyEq (LBegin actor) witness
  before afterState tag equation with (lookupFiber @{nameEq} actor (registry before)) proof found
  successfulExistingActionSource nameEq keyEq (LBegin actor) witness
    before afterState tag equation | Nothing = void (nothingIsNotJust equation)
  successfulExistingActionSource nameEq keyEq (LBegin actor) witness
    before afterState tag equation | Just fiber = (fiber ** Refl)
successfulExistingActionSource nameEq keyEq (LAdvance actor) witness
  before afterState tag equation with (lookupFiber @{nameEq} actor (registry before)) proof found
  successfulExistingActionSource nameEq keyEq (LAdvance actor) witness
    before afterState tag equation | Nothing = void (nothingIsNotJust equation)
  successfulExistingActionSource nameEq keyEq (LAdvance actor) witness
    before afterState tag equation | Just fiber = (fiber ** Refl)
successfulExistingActionSource nameEq keyEq (LDivert actor) witness
  before afterState tag equation with (lookupFiber @{nameEq} actor (registry before)) proof found
  successfulExistingActionSource nameEq keyEq (LDivert actor) witness
    before afterState tag equation | Nothing = void (nothingIsNotJust equation)
  successfulExistingActionSource nameEq keyEq (LDivert actor) witness
    before afterState tag equation | Just fiber = (fiber ** Refl)
successfulExistingActionSource nameEq keyEq (LLeave actor) witness
  before afterState tag equation with (lookupFiber @{nameEq} actor (registry before)) proof found
  successfulExistingActionSource nameEq keyEq (LLeave actor) witness
    before afterState tag equation | Nothing = void (nothingIsNotJust equation)
  successfulExistingActionSource nameEq keyEq (LLeave actor) witness
    before afterState tag equation | Just fiber = (fiber ** Refl)
successfulExistingActionSource nameEq keyEq (LUnload actor) witness
  before afterState tag equation with (lookupFiber @{nameEq} actor (registry before)) proof found
  successfulExistingActionSource nameEq keyEq (LUnload actor) witness
    before afterState tag equation | Nothing = void (nothingIsNotJust equation)
  successfulExistingActionSource nameEq keyEq (LUnload actor) witness
    before afterState tag equation | Just fiber = (fiber ** Refl)

0 presentContradictsAbsent :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {actor : name} ->
  {fibers : Registry name key value world error} ->
  {fiber : Fiber name key value world error} -> {result : Type} ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world}
    {error = error} actor fibers = Just fiber ->
  lookupFiber @{nameEq} {key = key} {value = value} {world = world}
    {error = error} actor fibers = Nothing -> result
presentContradictsAbsent present absent =
  void (nothingIsNotJust (trans (sym absent) present))

0 provenanceInsertionRank :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  (equation : applyAction @{nameEq} @{keyEq} action before = Just (tag, afterState)) ->
  RegistrationStepProvenance protocol nameEq action before ->
  RegistryInsertionRank protocol nameEq (actionOwner action)
    (registry before) (registry afterState)
provenanceInsertionRank protocol nameEq keyEq (OInsert actor Root component)
  before@(MkSystemState sourceWorld sourceRegistry)
  afterState@(MkSystemState targetWorld targetRegistry)
  tag equation (rank ** ranked) fiber absent targetIsInsert =
    let targetExact = oInsertResultLookup nameEq keyEq actor Root component
          (MkSystemState sourceWorld sourceRegistry)
          (MkSystemState targetWorld targetRegistry) tag equation
        updateSelf = lookupInserted actor fiber sourceRegistry absent
        targetAsInsert = cong (lookupFiber @{nameEq} actor) targetIsInsert
        targetFiber = trans targetAsInsert updateSelf
        same = justInjective (trans (sym targetFiber) targetExact)
    in replace {p = FiberProtocolRank protocol} (sym same) (rank ** ranked)
provenanceInsertionRank protocol nameEq keyEq
  (OInsert actor (ChildOf parent) component)
  before@(MkSystemState sourceWorld sourceRegistry)
  afterState@(MkSystemState targetWorld targetRegistry)
  tag equation yielded fiber absent targetIsInsert =
    let targetExact = oInsertResultLookup nameEq keyEq actor (ChildOf parent)
          component (MkSystemState sourceWorld sourceRegistry)
          (MkSystemState targetWorld targetRegistry) tag equation
        updateSelf = lookupInserted actor fiber sourceRegistry absent
        targetAsInsert = cong (lookupFiber @{nameEq} actor) targetIsInsert
        targetFiber = trans targetAsInsert updateSelf
        same = justInjective (trans (sym targetFiber) targetExact)
    in replace {p = FiberProtocolRank protocol} (sym same)
      (childRegistrationRank yielded ** childRanked yielded)
provenanceInsertionRank protocol nameEq keyEq (ORetire actor) before afterState tag
  equation provenance fiber absent targetIsInsert =
    let (old ** present) = successfulExistingActionSource nameEq keyEq
          (ORetire actor) () before afterState tag equation
    in presentContradictsAbsent present absent
provenanceInsertionRank protocol nameEq keyEq (ORemove actor) before afterState tag
  equation provenance fiber absent targetIsInsert =
    let (old ** present) = successfulExistingActionSource nameEq keyEq
          (ORemove actor) () before afterState tag equation
    in presentContradictsAbsent present absent
provenanceInsertionRank protocol nameEq keyEq (LBegin actor) before afterState tag
  equation provenance fiber absent targetIsInsert =
    let (old ** present) = successfulExistingActionSource nameEq keyEq
          (LBegin actor) () before afterState tag equation
    in presentContradictsAbsent present absent
provenanceInsertionRank protocol nameEq keyEq (LAdvance actor) before afterState tag
  equation provenance fiber absent targetIsInsert =
    let (old ** present) = successfulExistingActionSource nameEq keyEq
          (LAdvance actor) () before afterState tag equation
    in presentContradictsAbsent present absent
provenanceInsertionRank protocol nameEq keyEq (LDivert actor) before afterState tag
  equation provenance fiber absent targetIsInsert =
    let (old ** present) = successfulExistingActionSource nameEq keyEq
          (LDivert actor) () before afterState tag equation
    in presentContradictsAbsent present absent
provenanceInsertionRank protocol nameEq keyEq (LLeave actor) before afterState tag
  equation provenance fiber absent targetIsInsert =
    let (old ** present) = successfulExistingActionSource nameEq keyEq
          (LLeave actor) () before afterState tag equation
    in presentContradictsAbsent present absent
provenanceInsertionRank protocol nameEq keyEq (LUnload actor) before afterState tag
  equation provenance fiber absent targetIsInsert =
    let (old ** present) = successfulExistingActionSource nameEq keyEq
          (LUnload actor) () before afterState tag equation
    in presentContradictsAbsent present absent

||| One checked step preserves protocol ranking.
public export
0 registrationRankStep :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  {before, afterState : SystemState name key value world error} ->
  checkedApplyAction @{nameEq} @{keyEq} action before = Just (tag, afterState) ->
  RegistrationStepProvenance protocol nameEq action before ->
  RegistryProtocolRanked protocol nameEq before ->
  RegistryProtocolRanked protocol nameEq afterState
registrationRankStep protocol nameEq keyEq action tag checkedEquation provenance ranked =
    let rawEquation = checkedActionProjects nameEq keyEq action before afterState
          tag checkedEquation
        update = systemRegistryUpdate
          (applyActionLocalUpdate nameEq keyEq action before afterState tag rawEquation)
        inserted = provenanceInsertionRank protocol nameEq keyEq action before
          afterState tag rawEquation provenance
    in registryProtocolRankedUpdate protocol nameEq (actionOwner action)
      (registry before) (registry afterState) update inserted ranked

||| Forward induction over all checked actions establishes the rank invariant.
public export
0 registrationRankInvariant :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (trace : Transitions initial finalState) ->
  AlignedTransitions name key world error value nameEq keyEq trace ->
  RegistrationProvenance protocol nameEq trace ->
  RegistryProtocolRanked protocol nameEq initial ->
  RegistryProtocolRanked protocol nameEq finalState
registrationRankInvariant protocol nameEq keyEq NoTransitions AlignedEnd
  RegistrationProvenanceEnd ranked = ranked
registrationRankInvariant protocol nameEq keyEq
  (MoreTransitions (Fired nameEq keyEq action tag equation) rest)
  (AlignedStep action tag equation rest alignedRest)
  (RegistrationProvenanceStep (Fired nameEq keyEq action tag equation) rest
    stepProvenance restProvenance)
  ranked = registrationRankInvariant protocol nameEq keyEq rest alignedRest
    restProvenance
    (registrationRankStep protocol nameEq keyEq action tag equation stepProvenance
      ranked)

||| Empty registries satisfy the rank invariant vacuously.
public export
0 emptyRegistryProtocolRanked :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) ->
  (state : SystemState name key value world error) ->
  bindings (registry state) = [] ->
  RegistryProtocolRanked protocol nameEq state
emptyRegistryProtocolRanked protocol nameEq
  (MkSystemState ambient (MkCoeffectContext [] unique)) Refl selected fiber found =
    case found of Refl impossible
emptyRegistryProtocolRanked protocol nameEq
  (MkSystemState ambient (MkCoeffectContext (entry :: rest) unique)) empty
  selected fiber found = case empty of Refl impossible

||| Registration provenance from an empty registry ranks every endpoint fiber.
public export
0 reachedRegistryProtocolRanked :
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (reached : ReachedFromEmpty name key world error value nameEq keyEq state) ->
  RegistrationProvenance protocol nameEq (reachTrace reached) ->
  RegistryProtocolRanked protocol nameEq state
reachedRegistryProtocolRanked protocol nameEq keyEq reached provenance =
  registrationRankInvariant protocol nameEq keyEq (reachTrace reached)
    (reachAligned reached) provenance
    (emptyRegistryProtocolRanked protocol nameEq (reachInitial reached)
      (reachInitialEmpty reached))
