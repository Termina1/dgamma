module DGamma.CP5O20ChronologicalOccurrenceHistorySpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.CP5ImmutableBirthMetadataSpike
import DGamma.CP5O20GlobalActivationHistorySpike
import DGamma.CP5O20InsertOccurrenceHistorySpike
import DGamma.CP5O20OccurrenceStampedHistorySpike
import DGamma.CP5O20NativeInsertEnvironmentSpike
import DGamma.CP5O20StampedOrdinalNecessitySpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Prepend the actual native edge to an authentic retained event birth.
||| Its own suffix remains literally unchanged, so the real no-Unload witness
||| survives. Arithmetic transports only the physical insertion count.
export
0 o20ChronologicalBirthPrepend :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (ordinal : Nat) -> (edge : Transition first middle) -> (rest : Transitions middle finalState) ->
  (event : RegistrationEvent name key world error value) ->
  (birth : ScannedRegistrationBirth name key world error value (S ordinal) rest event **
    SurvivingRegistration event (afterActionOccurrence (scannedLocatedBirth birth))) ->
  (birth : ScannedRegistrationBirth name key world error value ordinal (MoreTransitions edge rest) event **
    SurvivingRegistration event (afterActionOccurrence (scannedLocatedBirth birth)))
o20ChronologicalBirthPrepend name key world error value ordinal edge rest event
  (MkScannedRegistrationBirth (MkLocatedActionOccurrence before afterState earlier located later shape decomposition) stamp ** retained) =
    (MkScannedRegistrationBirth
      (MkLocatedActionOccurrence before afterState (MoreTransitions edge earlier) located later shape
        (cong (MoreTransitions edge) decomposition))
      (trans stamp (cong (MkRegistrationGeneration (eventChild event))
        (plusSuccRightSucc ordinal (transitionCount earlier)))) ** retained)

||| Every retained event in either R203 native ORIGINAL chronology yields
||| its real occurrence, exact original stamp and its OWN open parent suffix.
||| The proof follows actual ordinary/deleted/retained edges; it never zips
||| arbitrary event lists or substitutes iterator position for physical count.
export
0 o20NativeChronologicalBirth :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (ordinal : Nat) -> (index : RegistrationIndexState name) ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) -> (finalIndex : RegistrationIndexState name) ->
  (events : List (RegistrationEvent name key world error value)) ->
  O20NativeActivationScan nameEq ordinal index trace finalIndex events ->
  (event : RegistrationEvent name key world error value) -> Elem event events ->
  (birth : ScannedRegistrationBirth name key world error value ordinal trace event **
    SurvivingRegistration event (afterActionOccurrence (scannedLocatedBirth birth)))
o20NativeChronologicalBirth name key world error value nameEq ordinal
  (MkRegistrationIndexState live activations counts discarded) trace finalIndex events scan event member =
    case scan of
      O20ActivationScanEnd => absurd member
      O20ActivationScanOrdinary action edge rest shape ordinary later =>
        o20ChronologicalBirthPrepend name key world error value ordinal edge rest event
          (o20NativeChronologicalBirth name key world error value nameEq (S ordinal)
            (advanceRegistrationIndex @{nameEq} ordinal action (MkRegistrationIndexState live activations counts discarded))
            rest finalIndex events later event member)
      O20ActivationScanDeleted {child} {parent} {component} edge rest shape closed later =>
        o20ChronologicalBirthPrepend name key world error value ordinal edge rest event
          (o20NativeChronologicalBirth name key world error value nameEq (S ordinal)
            (advanceDeletedRegistrationIndex @{nameEq} ordinal child parent component (MkRegistrationIndexState live activations counts discarded))
            rest finalIndex events later event member)
      O20ActivationScanRetained {child} {parent} {component} {events = laterEvents} edge rest shape retained later =>
        case member of
          Here => (scannedRegistrationBirthHead name key world error value nameEq ordinal
            (MkRegistrationIndexState live activations counts discarded) child parent component edge rest shape ** retained)
          There remaining =>
            o20ChronologicalBirthPrepend name key world error value ordinal edge rest event
              (o20NativeChronologicalBirth name key world error value nameEq (S ordinal)
                (advanceSurvivingRegistrationIndex @{nameEq} ordinal child parent component (MkRegistrationIndexState live activations counts discarded))
                rest finalIndex laterEvents later event remaining)
