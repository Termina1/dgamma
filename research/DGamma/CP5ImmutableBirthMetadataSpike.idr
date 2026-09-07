module DGamma.CP5ImmutableBirthMetadataSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4Support
import DGamma.CP4DeletionSelectedOwn
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5RawClosingRankSpike
import DGamma.CP5CurrentGenerationBirthSpike
import Data.Nat
import Data.List.Elem
import Decidable.Equality

%default total
%unbound_implicits off

||| Parent and component are immutable through actual non-birth updates.
||| Retirement is deliberately excluded: the frozen evaluator may change it.
public export
0 rawImmutableMetadataUpdate :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) ->
  (property : name -> (Parent name, Component key value world error) -> Type) ->
  (actor : name) -> (source, target : Registry name key value world error) ->
  (update : RegistryLocalUpdate name key world error value nameEq actor source target) ->
  ((next : Fiber name key value world error) ->
    (absent : lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
      @{nameEq} actor source = Nothing) ->
    target = insertBinding @{nameEq} actor next source absent -> property actor (fiberParent next, fiberComponent next)) ->
  ((selected : name) -> (fiber : Fiber name key value world error) ->
    lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
      @{nameEq} selected source = Just fiber -> property selected (fiberParent fiber, fiberComponent fiber)) ->
  (selected : name) -> (observed : Fiber name key value world error) ->
  lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected target = Just observed -> property selected (fiberParent observed, fiberComponent observed)
rawImmutableMetadataUpdate name key world error value nameEq property actor source _
  (LocalInsert next absent) inserted previous selected observed found =
    case decEq @{nameEq} selected actor of
      Yes same => case same of
        Refl => replace {p = property actor}
          (cong (\fiber => (fiberParent fiber, fiberComponent fiber)) (justInjective (trans (sym (lookupInserted actor next source absent)) found)))
          (inserted next absent Refl)
      No distinct => previous selected observed
        (trans (sym (registryLocalUpdateForeign nameEq selected actor distinct source
          (LocalInsert next absent))) found)
rawImmutableMetadataUpdate name key world error value nameEq property actor source _
  (LocalReplace {oldFiber} {oldFound} {staticComponent} {staticParent} next) inserted previous selected observed found =
    case decEq @{nameEq} selected actor of
      Yes same => case same of
        Refl => replace {p = property actor}
          (trans (sym (cong2 MkPair staticParent staticComponent)) (cong (\fiber => (fiberParent fiber, fiberComponent fiber))
            (justInjective (trans (sym (lookupReplacedFiber actor oldFiber next source oldFound)) found))))
          (previous actor oldFiber oldFound)
      No distinct => previous selected observed
        (trans (sym (registryLocalUpdateForeign nameEq selected actor distinct source
          (LocalReplace {oldFiber} {oldFound} {staticComponent} {staticParent} next))) found)
rawImmutableMetadataUpdate name key world error value nameEq property actor source _
  LocalDelete inserted previous selected observed found =
    case decEq @{nameEq} selected actor of
      Yes same => case same of
        Refl => void (nothingIsNotJust
          (trans (sym (DGamma.CP4DeletionSelectedOwn.lookupDeleteSelf @{nameEq} actor source)) found))
      No distinct => previous selected observed
        (trans (sym (registryLocalUpdateForeign nameEq selected actor distinct source LocalDelete)) found)

||| Authenticate both immutable endpoint fields at the actual original birth.
public export
0 rawMetadataBirthStep :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (global : Transitions initial finalState) ->
  (action : Action name key value world error) ->
  (before, afterState : SystemState name key value world error) -> (tag : RuleTag) ->
  (raw : applyAction @{nameEq} @{keyEq} action before = Just (tag, afterState)) ->
  (occurrence : LocatedActionOccurrence action global) ->
  ((selected : name) -> (fiber : Fiber name key value world error) ->
    lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
      @{nameEq} selected (registry before) = Just fiber ->
    LocatedActionOccurrence (OInsert selected (fiberParent fiber) (fiberComponent fiber)) global) ->
  (selected : name) -> (observed : Fiber name key value world error) ->
  lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected (registry afterState) = Just observed ->
  LocatedActionOccurrence (OInsert selected (fiberParent observed) (fiberComponent observed)) global
rawMetadataBirthStep name key world error value nameEq keyEq global action
  before afterState tag raw occurrence sourceBirth =
    rawImmutableMetadataUpdate name key world error value nameEq
      (\selected, metadata => LocatedActionOccurrence
        (OInsert selected (fst metadata) (snd metadata)) global)
      (actionOwner action) (registry before) (registry afterState)
      (systemRegistryUpdate (applyActionLocalUpdate nameEq keyEq action before afterState tag raw))
      (\next, absent, targetIsInsert =>
        case rawAbsentOwnerInsertion name key world error value nameEq keyEq action
          before afterState tag raw absent of
          (parent ** (component ** inserted)) =>
            replace {p = \metadata => LocatedActionOccurrence
              (OInsert (actionOwner action) (fst metadata) (snd metadata)) global}
              (cong (\fiber => (fiberParent fiber, fiberComponent fiber)) (justInjective
                (trans (sym (oInsertResultLookup nameEq keyEq (actionOwner action) parent component
                  before afterState tag (replace
                    {p = \chosen => applyAction @{nameEq} @{keyEq} chosen before = Just (tag, afterState)}
                    inserted raw)))
                  (trans (cong (lookupFiber @{nameEq} (actionOwner action)) targetIsInsert)
                    (lookupInserted (actionOwner action) next (registry before) absent)))))
              (replace {p = \chosen => LocatedActionOccurrence chosen global} inserted occurrence))
      sourceBirth

||| Forward induction retains actual birth locations and exact immutable metadata.
public export
0 rawMetadataBirthInvariant :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState, first, last : SystemState name key value world error} ->
  (global : Transitions initial finalState) -> (segment : Transitions first last) ->
  AlignedTransitions name key world error value nameEq keyEq segment ->
  ((action : Action name key value world error) ->
    LocatedActionOccurrence action segment -> LocatedActionOccurrence action global) ->
  ((selected : name) -> (fiber : Fiber name key value world error) ->
    lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
      @{nameEq} selected (registry first) = Just fiber ->
    LocatedActionOccurrence
      (OInsert selected (fiberParent fiber) (fiberComponent fiber)) global) ->
  (selected : name) -> (observed : Fiber name key value world error) ->
  lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected (registry last) = Just observed ->
  LocatedActionOccurrence
    (OInsert selected (fiberParent observed) (fiberComponent observed)) global
rawMetadataBirthInvariant name key world error value nameEq keyEq global
  NoTransitions AlignedEnd embedding previous = previous
rawMetadataBirthInvariant name key world error value nameEq keyEq global
  (MoreTransitions head rest) aligned embedding previous =
    case aligned of
      AlignedStep action tag checked _ alignedRest =>
        rawMetadataBirthInvariant name key world error value nameEq keyEq global rest alignedRest
          (\wanted, occurrence => embedding wanted (case occurrence of
            MkLocatedActionOccurrence before afterState prior step later actionExact decomposition =>
              MkLocatedActionOccurrence before afterState (MoreTransitions (Fired nameEq keyEq action tag checked) prior) step later
                actionExact (cong (MoreTransitions (Fired nameEq keyEq action tag checked)) decomposition)))
          (rawMetadataBirthStep name key world error value nameEq keyEq global action _ _ tag
            (checkedActionProjects nameEq keyEq action _ _ tag checked)
            (embedding action (MkLocatedActionOccurrence _ _ NoTransitions (Fired nameEq keyEq action tag checked) rest Refl Refl)) previous)

||| Any actual prefix lookup identifies a birth of this exact parent and component.
public export
0 rawMetadataBirthAtPrefix :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, middle, finalState : SystemState name key value world error} ->
  (global : Transitions initial finalState) ->
  (prior : Transitions initial middle) -> (later : Transitions middle finalState) ->
  appendTransitions prior later = global ->
  AlignedTransitions name key world error value nameEq keyEq prior ->
  bindings (registry initial) = [] ->
  (selected : name) -> (observed : Fiber name key value world error) ->
  lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected (registry middle) = Just observed ->
  LocatedActionOccurrence
    (OInsert selected (fiberParent observed) (fiberComponent observed)) global
rawMetadataBirthAtPrefix name key world error value nameEq keyEq {initial}
  global prior later decomposition aligned empty =
    rawMetadataBirthInvariant name key world error value nameEq keyEq global prior aligned
      (\action, occurrence => replace {p = \whole => LocatedActionOccurrence action whole} decomposition
        (case occurrence of
          MkLocatedActionOccurrence before afterState pre step post actionExact split =>
            MkLocatedActionOccurrence before afterState pre step (appendTransitions post later) actionExact
              (trans (sym (appendTransitionsAssociative pre (MoreTransitions step post) later))
                (cong (\whole => appendTransitions whole later) split))))
      (\selected, fiber, found =>
        case emptyRegistryProtocolRanked (emptyRegistrationProtocol {key = key} {value = value}
          {world = world} {error = error}) nameEq initial empty selected fiber found of
          (rank ** ranked) => void (nothingIsNotJust ranked))

||| Uniqueness compares two authenticated births, yielding both immutable fields.
public export
0 uniqueRawBirthMetadata :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq trace ->
  (selected : name) -> (leftParent, rightParent : Parent name) ->
  (leftComponent, rightComponent : Component key value world error) ->
  (left : LocatedActionOccurrence (OInsert selected leftParent leftComponent) trace) ->
  (right : LocatedActionOccurrence (OInsert selected rightParent rightComponent) trace) ->
  (leftParent, leftComponent) = (rightParent, rightComponent)
uniqueRawBirthMetadata name key world error value nameEq keyEq trace unique
  selected leftParent rightParent leftComponent rightComponent left right =
    case justInjective
      (trans (sym (rawClosingActionAtLocated name key world error value trace
        (OInsert selected leftParent leftComponent) left))
        (trans (cong (\ordinal => rawClosingActionAt name key world error value ordinal trace)
          (uniqueInsertionPosition unique selected leftParent rightParent leftComponent rightComponent left right))
          (rawClosingActionAtLocated name key world error value trace
            (OInsert selected rightParent rightComponent) right))) of
      Refl => Refl

||| The accepted scanner birth and an actual lookup agree in BOTH static fields.
public export
0 currentBirthMetadataAtPrefix :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, middle, finalState : SystemState name key value world error} ->
  (global : Transitions initial finalState) ->
  (prior : Transitions initial middle) -> (later : Transitions middle finalState) ->
  (appendTransitions prior later = global) ->
  AlignedTransitions name key world error value nameEq keyEq prior ->
  (bindings (registry initial) = []) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq global ->
  (selected : name) -> (generation : RegistrationGeneration name) ->
  (authentication : CurrentGenerationBirth name key world error value global selected generation) ->
  (observed : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected (registry middle) = Just observed) ->
  (currentBirthParent authentication, currentBirthComponent authentication) =
    (fiberParent observed, fiberComponent observed)
currentBirthMetadataAtPrefix name key world error value nameEq keyEq global prior later decomposition aligned empty unique
  selected generation authentication observed found =
    uniqueRawBirthMetadata name key world error value nameEq keyEq global unique selected
      (currentBirthParent authentication) (fiberParent observed)
      (currentBirthComponent authentication) (fiberComponent observed)
      (currentLocatedBirth authentication)
      (rawMetadataBirthAtPrefix name key world error value nameEq keyEq global prior later
        decomposition aligned empty selected observed found)

||| Actual parent/component birth with the exact scanner stamp, not a chosen birth.
public export
0 currentBirthAtPrefixMetadata :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, middle, finalState : SystemState name key value world error} ->
  (global : Transitions initial finalState) ->
  (prior : Transitions initial middle) -> (later : Transitions middle finalState) ->
  (appendTransitions prior later = global) ->
  AlignedTransitions name key world error value nameEq keyEq prior ->
  (bindings (registry initial) = []) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq global ->
  (selected : name) -> (generation : RegistrationGeneration name) ->
  (authentication : CurrentGenerationBirth name key world error value global selected generation) ->
  (observed : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected (registry middle) = Just observed) ->
  (birth : LocatedActionOccurrence (OInsert selected (fiberParent observed) (fiberComponent observed)) global **
    generation = MkRegistrationGeneration selected (locatedActionOrdinal birth))
currentBirthAtPrefixMetadata name key world error value nameEq keyEq global prior later decomposition aligned empty unique
  selected generation authentication observed found =
    (rawMetadataBirthAtPrefix name key world error value nameEq keyEq global prior later
      decomposition aligned empty selected observed found **
      trans (currentBirthStampExact authentication)
        (cong (MkRegistrationGeneration selected)
          (uniqueInsertionPosition unique selected (currentBirthParent authentication) (fiberParent observed)
            (currentBirthComponent authentication) (fiberComponent observed)
            (currentLocatedBirth authentication)
            (rawMetadataBirthAtPrefix name key world error value nameEq keyEq global prior later
              decomposition aligned empty selected observed found))))

||| A genuine generated event birth in the scanned trace, including its stamp.
||| The offset supports structural induction without inventing a global origin.
public export
record ScannedRegistrationBirth
  (name, key, world, error : Type) (value : key -> Type)
  (startOrdinal : Nat)
  {first, finalState : SystemState name key value world error}
  (trace : Transitions first finalState)
  (event : RegistrationEvent name key world error value) where
  constructor MkScannedRegistrationBirth
  scannedLocatedBirth : LocatedActionOccurrence
    (OInsert (eventChild event) (ChildOf (eventParent event)) (eventComponent event)) trace
  0 scannedBirthStampExact : eventChildGeneration event =
    MkRegistrationGeneration (eventChild event) (startOrdinal + locatedActionOrdinal scannedLocatedBirth)

||| Prepend an actual checked transition while preserving the global event stamp.
public export
0 scannedRegistrationBirthPrepend :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (ordinal : Nat) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (step : Transition first middle) -> (rest : Transitions middle finalState) ->
  (event : RegistrationEvent name key world error value) ->
  ScannedRegistrationBirth name key world error value (S ordinal) rest event ->
  ScannedRegistrationBirth name key world error value ordinal (MoreTransitions step rest) event
scannedRegistrationBirthPrepend name key world error value ordinal step rest event
  (MkScannedRegistrationBirth
    (MkLocatedActionOccurrence before afterState prior located later actionExact decomposition) stamp) =
      MkScannedRegistrationBirth
        (MkLocatedActionOccurrence before afterState (MoreTransitions step prior) located later actionExact
          (cong (MoreTransitions step) decomposition))
        (trans stamp (cong (MkRegistrationGeneration (eventChild event))
          (plusSuccRightSucc ordinal (transitionCount prior))))

||| Producer-owned observation of registrationEventAt: never eliminate its opaque result.
public export
0 scannedRegistrationBirthHead :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (ordinal : Nat) -> (index : RegistrationIndexState name) ->
  (child, parent : name) -> (component : Component key value world error) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (step : Transition first middle) -> (rest : Transitions middle finalState) ->
  transitionAction step = OInsert child (ChildOf parent) component ->
  ScannedRegistrationBirth name key world error value ordinal (MoreTransitions step rest)
    (registrationEventAt @{nameEq} ordinal index child parent component)
scannedRegistrationBirthHead name key world error value nameEq ordinal
  (MkRegistrationIndexState live activations counts deleted) child parent component step rest actionExact =
    MkScannedRegistrationBirth
      (MkLocatedActionOccurrence _ _ NoTransitions step rest actionExact Refl)
      (cong (MkRegistrationGeneration child) (sym (plusZeroRightNeutral ordinal)))

||| Public boundary for the sealed scanner's own finite matching. Both event
||| domains are authenticated in their ORIGINAL traces, not caller-origin maps.
public export
record AuthenticatedRegistrationMatching
  (name, key, world, error : Type) (value : key -> Type)
  (renaming : RegistrationGenerationBijection name)
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error}
  (left : Transitions leftFirst leftFinal) (right : Transitions rightFirst rightFinal) where
  constructor MkAuthenticatedRegistrationMatching
  leftScannedEvents : List (RegistrationEvent name key world error value)
  rightScannedEvents : List (RegistrationEvent name key world error value)
  0 leftScannedBirths : (event : RegistrationEvent name key world error value) ->
    Elem event leftScannedEvents -> ScannedRegistrationBirth name key world error value Z left event
  0 rightScannedBirths : (event : RegistrationEvent name key world error value) ->
    Elem event rightScannedEvents -> ScannedRegistrationBirth name key world error value Z right event
  0 matchedEventForward : (event : RegistrationEvent name key world error value) -> Elem event leftScannedEvents ->
    (paired : RegistrationEvent name key world error value **
      (Elem paired rightScannedEvents, RegistrationEventMatch renaming event paired))
  0 matchedEventBackward : (event : RegistrationEvent name key world error value) -> Elem event rightScannedEvents ->
    (paired : RegistrationEvent name key world error value **
      (Elem paired leftScannedEvents, RegistrationEventMatch renaming paired event))

||| A real retained event reads back BOTH static fields of its actual endpoint.
public export
0 scannedBirthEndpointMetadata :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  AlignedTransitions name key world error value nameEq keyEq trace ->
  bindings (registry initial) = [] ->
  UniqueRawNameInsertions name key world error value nameEq keyEq trace ->
  (event : RegistrationEvent name key world error value) ->
  ScannedRegistrationBirth name key world error value Z trace event ->
  (observed : Fiber name key value world error) ->
  lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} (eventChild event) (registry finalState) = Just observed ->
  (ChildOf (eventParent event), eventComponent event) = (fiberParent observed, fiberComponent observed)
scannedBirthEndpointMetadata name key world error value nameEq keyEq trace aligned empty unique event birth observed found =
  uniqueRawBirthMetadata name key world error value nameEq keyEq trace unique (eventChild event)
    (ChildOf (eventParent event)) (fiberParent observed) (eventComponent event) (fiberComponent observed)
    (scannedLocatedBirth birth)
    (rawMetadataBirthAtPrefix name key world error value nameEq keyEq trace trace NoTransitions
      (currentBirthTraceAppendEmpty name key world error value trace) aligned empty (eventChild event) observed found)

||| The exact accepted current stamp equals the authenticated event stamp.
||| Both births are located before raw-name uniqueness is used.
public export
0 currentBirthMatchesScannedEvent :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq trace ->
  (event : RegistrationEvent name key world error value) ->
  ScannedRegistrationBirth name key world error value Z trace event ->
  (generation : RegistrationGeneration name) ->
  CurrentGenerationBirth name key world error value trace (eventChild event) generation ->
  generation = eventChildGeneration event
currentBirthMatchesScannedEvent name key world error value nameEq keyEq trace unique event scanned generation current =
  trans (currentBirthStampExact current)
    (trans (cong (MkRegistrationGeneration (eventChild event))
      (uniqueInsertionPosition unique (eventChild event) (currentBirthParent current) (ChildOf (eventParent event))
        (currentBirthComponent current) (eventComponent event)
        (currentLocatedBirth current) (scannedLocatedBirth scanned)))
      (sym (scannedBirthStampExact scanned)))

||| All immutable endpoint data needed by dependency/provision support analysis.
||| Parent identities are related through the authenticated birth/activation
||| match; NO retired-flag equality or support truth is included.
public export
record MatchedEndpointStaticMetadata
  (name, key, world, error : Type) (value : key -> Type)
  (renaming : RegistrationGenerationBijection name)
  (leftEvent, rightEvent : RegistrationEvent name key world error value)
  (leftFiber, rightFiber : Fiber name key value world error) where
  constructor MkMatchedEndpointStaticMetadata
  0 endpointEventMatch : RegistrationEventMatch renaming leftEvent rightEvent
  0 endpointComponentsMatch : fiberComponent leftFiber = fiberComponent rightFiber
  0 endpointDependenciesMatch : componentDependencies (fiberComponent leftFiber) =
    componentDependencies (fiberComponent rightFiber)
  0 endpointProvisionsMatch : componentProvisions (fiberComponent leftFiber) =
    componentProvisions (fiberComponent rightFiber)
  0 leftEndpointBirthParent : fiberParent leftFiber = ChildOf (eventParent leftEvent)
  0 rightEndpointBirthParent : fiberParent rightFiber = ChildOf (eventParent rightEvent)

||| Exact endpoint metadata from two authenticated ORIGINAL matched births.
public export
0 matchedBirthEndpointMetadata :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {leftFirst, leftFinal, rightFirst, rightFinal : SystemState name key value world error} ->
  (left : Transitions leftFirst leftFinal) -> (right : Transitions rightFirst rightFinal) ->
  AlignedTransitions name key world error value nameEq keyEq left ->
  AlignedTransitions name key world error value nameEq keyEq right ->
  bindings (registry leftFirst) = [] -> bindings (registry rightFirst) = [] ->
  UniqueRawNameInsertions name key world error value nameEq keyEq left ->
  UniqueRawNameInsertions name key world error value nameEq keyEq right ->
  (renaming : RegistrationGenerationBijection name) ->
  (leftEvent, rightEvent : RegistrationEvent name key world error value) ->
  ScannedRegistrationBirth name key world error value Z left leftEvent ->
  ScannedRegistrationBirth name key world error value Z right rightEvent ->
  RegistrationEventMatch renaming leftEvent rightEvent ->
  (leftFiber, rightFiber : Fiber name key value world error) ->
  lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} (eventChild leftEvent) (registry leftFinal) = Just leftFiber ->
  lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} (eventChild rightEvent) (registry rightFinal) = Just rightFiber ->
  MatchedEndpointStaticMetadata name key world error value renaming leftEvent rightEvent leftFiber rightFiber
matchedBirthEndpointMetadata name key world error value nameEq keyEq left right leftAligned rightAligned leftEmpty rightEmpty
  leftUnique rightUnique renaming leftEvent rightEvent leftBirth rightBirth matched leftFiber rightFiber leftFound rightFound =
    MkMatchedEndpointStaticMetadata matched
      (trans (sym (cong snd (scannedBirthEndpointMetadata name key world error value nameEq keyEq left leftAligned leftEmpty leftUnique leftEvent leftBirth leftFiber leftFound)))
      (trans (matchedComponent matched) (cong snd (scannedBirthEndpointMetadata name key world error value nameEq keyEq right rightAligned rightEmpty rightUnique rightEvent rightBirth rightFiber rightFound))))
      (cong componentDependencies (trans (sym (cong snd (scannedBirthEndpointMetadata name key world error value nameEq keyEq left leftAligned leftEmpty leftUnique leftEvent leftBirth leftFiber leftFound)))
      (trans (matchedComponent matched) (cong snd (scannedBirthEndpointMetadata name key world error value nameEq keyEq right rightAligned rightEmpty rightUnique rightEvent rightBirth rightFiber rightFound)))))
      (cong componentProvisions (trans (sym (cong snd (scannedBirthEndpointMetadata name key world error value nameEq keyEq left leftAligned leftEmpty leftUnique leftEvent leftBirth leftFiber leftFound)))
      (trans (matchedComponent matched) (cong snd (scannedBirthEndpointMetadata name key world error value nameEq keyEq right rightAligned rightEmpty rightUnique rightEvent rightBirth rightFiber rightFound)))))
      (sym (cong fst (scannedBirthEndpointMetadata name key world error value nameEq keyEq left leftAligned leftEmpty leftUnique leftEvent leftBirth leftFiber leftFound)))
      (sym (cong fst (scannedBirthEndpointMetadata name key world error value nameEq keyEq right rightAligned rightEmpty rightUnique rightEvent rightBirth rightFiber rightFound)))
