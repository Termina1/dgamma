module DGamma.CP5SupportedBirthCoverageSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP5ImmutableBirthMetadataSpike
import DGamma.CP5CurrentGenerationBirthSpike
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
