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
