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
