module DGamma.CP5SupportedBirthCoverageSpike

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP5ImmutableBirthMetadataSpike
import DGamma.CP5CurrentGenerationBirthSpike
import DGamma.CP5RawClosingRankSpike
import DGamma.CP5RetirementHistorySpike
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5ConfluenceDeletionChainSpike
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Structural coverage of one genuine generated birth. The closing alternative
||| carries its OWN located birth and exact suffix, never an unrelated unload.
||| Endpoint support will exclude that alternative in a later semantic lemma.
public export
record ClassifiedGeneratedBirth
  (name, key, world, error : Type) (value : key -> Type)
  (ordinal : Nat)
  {0 first, finalState : SystemState name key value world error}
  (0 trace : Transitions first finalState)
  (events : List (RegistrationEvent name key world error value))
  (selected : name) where
  constructor MkClassifiedGeneratedBirth
  0 coveredEvent : RegistrationEvent name key world error value
  0 coveredChild : (eventChild coveredEvent = selected)
  0 coveredBirth : ScannedRegistrationBirth name key world error value ordinal trace coveredEvent
  0 coveredClassification : Either (Elem coveredEvent events)
    (DeletedClosingRegistration coveredEvent (afterActionOccurrence (scannedLocatedBirth coveredBirth)))

||| A prefix step changes the birth location, not its exact post-birth suffix.
export
0 classifiedBirthPrepend :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (ordinal : Nat) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (step : Transition first middle) -> (rest : Transitions middle finalState) ->
  (events, larger : List (RegistrationEvent name key world error value)) ->
  ((event : RegistrationEvent name key world error value) -> Elem event events -> Elem event larger) ->
  (selected : name) -> ClassifiedGeneratedBirth name key world error value (S ordinal) rest events selected ->
  ClassifiedGeneratedBirth name key world error value ordinal (MoreTransitions step rest) larger selected
classifiedBirthPrepend name key world error value ordinal step rest events larger embed selected
  (MkClassifiedGeneratedBirth event child
    (MkScannedRegistrationBirth
      (MkLocatedActionOccurrence before afterState prior located later actionExact decomposition) stamp) classification) =
    MkClassifiedGeneratedBirth event child
      (MkScannedRegistrationBirth
        (MkLocatedActionOccurrence before afterState (MoreTransitions step prior) located later actionExact
          (cong (MoreTransitions step) decomposition))
        (trans stamp (cong (MkRegistrationGeneration (eventChild event))
          (plusSuccRightSucc ordinal (transitionCount prior)))))
      (either (\member => Left (embed event member)) Right classification)

||| Head classification retains the scanner's exact event and decision.
export
0 classifiedBirthHead :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (ordinal : Nat) -> (index : RegistrationIndexState name) ->
  (child, parent : name) -> (component : Component key value world error) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (step : Transition first middle) -> (rest : Transitions middle finalState) ->
  (transitionAction step = OInsert child (ChildOf parent) component) ->
  (events : List (RegistrationEvent name key world error value)) ->
  Either (Elem (registrationEventAt @{nameEq} ordinal index child parent component) events)
    (DeletedClosingRegistration (registrationEventAt @{nameEq} ordinal index child parent component) rest) ->
  ClassifiedGeneratedBirth name key world error value ordinal (MoreTransitions step rest) events child
classifiedBirthHead name key world error value nameEq ordinal
  (MkRegistrationIndexState live activations counts deleted) child parent component step rest actionExact events classification =
    MkClassifiedGeneratedBirth
      (registrationEventAt @{nameEq} ordinal (MkRegistrationIndexState live activations counts deleted) child parent component) Refl
      (MkScannedRegistrationBirth (MkLocatedActionOccurrence _ _ NoTransitions step rest actionExact Refl)
        (cong (MkRegistrationGeneration child) (sym (plusZeroRightNeutral ordinal)))) classification

||| Observe an opaque checked head without destructing its proof-token shape.
export
0 coveredHeadActionObserved :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (step : Transition first middle) -> (rest : Transitions middle finalState) ->
  (wanted : Action name key value world error) ->
  (rawClosingActionAt name key world error value Z (MoreTransitions step rest) = Just wanted) ->
  transitionAction step = wanted
coveredHeadActionObserved name key world error value step rest wanted observed =
  justInjective (trans (sym (rawClosingActionAtSplit name key world error value NoTransitions step rest)) observed)

||| Closing the parent after THIS generated birth forces an actual child
||| retirement by the existing checked registration discipline. No deletion
||| theorem, withdrawal branch, or raw/scoped conversion is used.
export
0 locatedClosingBirthHasRetirement :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) -> AlignedTransitions name key world error value nameEq keyEq trace ->
  RegistrationDiscipline protocol nameEq trace -> (child, parent : name) -> (component : Component key value world error) ->
  (birth : LocatedActionOccurrence (OInsert child (ChildOf parent) component) trace) ->
  ActionOccurs (LUnload parent) (afterActionOccurrence birth) -> LocatedActionOccurrence (ORetire child) trace
locatedClosingBirthHasRetirement name key world error value nameEq keyEq protocol trace aligned discipline child parent component
  (MkLocatedActionOccurrence before afterState prior step later exact decomposition) closes =
    replace {p = LocatedActionOccurrence (ORetire child)} decomposition
      (afterCutOccurrence name key world error value prior (MoreTransitions step later) (ORetire child)
        (currentBirthPrependLocation name key world error value step later (ORetire child)
          (retirementOccurrenceLocated name key world error value later (ORetire child)
            (childRetirementAtGeneratedOccurrence protocol nameEq keyEq trace child parent component
              (MkLocatedGeneratedRegistration before afterState prior step later exact decomposition) aligned discipline closes))))

||| Endpoint support excludes the authentic closing alternative, so coverage
||| becomes membership in the scanner's actual RETAINED event domain.
export
0 supportedClassifiedBirthRetained :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) -> AlignedTransitions name key world error value nameEq keyEq trace ->
  RegistrationDiscipline protocol nameEq trace -> (bindings (registry first) = []) ->
  UniqueRawNameInsertions name key world error value nameEq keyEq trace ->
  (events : List (RegistrationEvent name key world error value)) -> (selected : name) ->
  (finalFiber : Fiber name key value world error) ->
  (lookupFiber {name = name} {key = key} {value = value} {world = world} {error = error}
    @{nameEq} selected (registry finalState) = Just finalFiber) ->
  (isSupported {name = name} {key = key} {value = value} {world = world} {error = error} @{nameEq} @{keyEq} selected finalState = True) ->
  ClassifiedGeneratedBirth name key world error value Z trace events selected ->
  (event : RegistrationEvent name key world error value ** (Elem event events, eventChild event = selected))
supportedClassifiedBirthRetained name key world error value nameEq keyEq protocol {finalState} trace aligned discipline empty unique
  events selected finalFiber found supported (MkClassifiedGeneratedBirth event childExact birth classification) =
    case classification of
      Left retained => (event ** (retained, childExact))
      Right deleted => void (nonretiredEndpointRejectsRetirement name key world error value nameEq keyEq trace aligned empty unique
        selected finalFiber found (computedSupportNotRetired name key world error value nameEq keyEq finalState selected finalFiber found supported)
        (replace {p = \action => LocatedActionOccurrence action trace} (cong ORetire childExact)
          (locatedClosingBirthHasRetirement name key world error value nameEq keyEq protocol trace aligned discipline
            (eventChild event) (eventParent event) (eventComponent event) (scannedLocatedBirth birth) (deletedParentEpisodeCloses deleted))))
