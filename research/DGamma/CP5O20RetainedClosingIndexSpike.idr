module DGamma.CP5O20RetainedClosingIndexSpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5RawClosingRankSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5O20DeletionRetainedUnloadSpike
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Decidable

%default total
%unbound_implicits off

||| Locate a REAL closing witness by its physical suffix index. This is not
||| an arbitrary index premise and does not yet transport a deletion.
export
0 o20UnloadOccurrenceIndex :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) -> (actor : name) ->
  ActionOccurs (LUnload actor) trace ->
  (ordinal : Nat ** (rawClosingActionAt name key world error value ordinal trace = Just (LUnload actor)))
o20UnloadOccurrenceIndex name key world error value _ actor
  (ActionOccursHere (Fired nameEq keyEq action tag checked) rest exact) =
    (Z ** cong Just exact)
o20UnloadOccurrenceIndex name key world error value _ actor
  (ActionOccursLater step rest later) =
    case o20UnloadOccurrenceIndex name key world error value rest actor later of
      (ordinal ** exact) => (S ordinal ** exact)

||| A nonselected classification cannot have its exact generated birth in
||| the selected parent's center. Membership is PRODUCED by the candidate's
||| registered-during completeness, not assumed. Locating that center birth
||| from a removed-center closing witness remains a separate obligation.
export
0 o20SelectedCenterBirthContradictsNonselection :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, finalState : SystemState name key value world error} ->
  (trace : Transitions initial finalState) ->
  (candidate : DeletableClosingEpisode name key world error value nameEq keyEq trace) ->
  (generation : RegistrationGeneration name) ->
  (classified : DeletedGenerationClassification name key world error value nameEq trace generation) ->
  Not (Elem generation (selectedRegistrations candidate)) ->
  (centerBirth : LocatedActionOccurrence
    (OInsert (generationName generation) (ChildOf (selectedActor candidate)) (deletedComponent classified))
    (MoreTransitions (beginTransition (closedOpening (locatedEpisode (selectedEpisode candidate))))
      (closedTransitions (locatedEpisode (selectedEpisode candidate))))) ->
  (registrationGeneration (deletedOccurrence classified) =
    MkRegistrationGeneration (generationName generation)
      (selectedStartOrdinal candidate + locatedActionOrdinal centerBirth)) -> Void
o20SelectedCenterBirthContradictsNonselection trace candidate generation classified outside centerBirth exact =
  outside (replace {p = \stamp => Elem stamp (selectedRegistrations candidate)}
    (trans (sym exact) (deletedOccurrenceGeneration classified))
    (snd (selectedRegisteredDuring candidate) (generationName generation)
      (deletedComponent classified) centerBirth))
