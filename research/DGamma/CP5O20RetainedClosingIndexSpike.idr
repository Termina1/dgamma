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

||| Rebase a physical suffix observation by the ACTUAL preceding trace count.
||| This equality is needed when a birth-relative index enters the whole scan.
export
0 o20ClosingActionAtAppend :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (earlier : Transitions first middle) -> (later : Transitions middle finalState) ->
  (ordinal : Nat) ->
  (rawClosingActionAt name key world error value (transitionCount earlier + ordinal)
    (appendTransitions earlier later) = rawClosingActionAt name key world error value ordinal later)
o20ClosingActionAtAppend name key world error value NoTransitions later ordinal = Refl
o20ClosingActionAtAppend name key world error value (MoreTransitions step rest) later ordinal =
  o20ClosingActionAtAppend name key world error value rest later ordinal

||| The closing witness stored in a deleted classification lies STRICTLY
||| after its actual birth in the ORIGINAL scan. The returned equation uses
||| physical transitionCount, not a canonical or externally chosen ordinal.
export
0 o20DeletedBirthClosingIndex :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) ->
  (generation : RegistrationGeneration name) ->
  (classified : DeletedGenerationClassification name key world error value nameEq trace generation) ->
  (ordinal : Nat ** (LT (registrationOrdinal (deletedOccurrence classified)) ordinal,
    rawClosingActionAt name key world error value ordinal trace = Just (LUnload (deletedParent classified))))
o20DeletedBirthClosingIndex name key world error value nameEq trace generation classified =
  case o20UnloadOccurrenceIndex name key world error value
    (afterRegistration (deletedOccurrence classified)) (deletedParent classified)
    (deletedParentEpisodeCloses classified) of
      (ordinal ** exact) =>
        (transitionCount (beforeRegistration (deletedOccurrence classified)) + S ordinal **
          (replace {p = LT (registrationOrdinal (deletedOccurrence classified))}
            (plusSuccRightSucc (registrationOrdinal (deletedOccurrence classified)) ordinal)
            (LTESucc (lteAddRight {m = ordinal} (registrationOrdinal (deletedOccurrence classified)))),
           trans (cong (rawClosingActionAt name key world error value
               (transitionCount (beforeRegistration (deletedOccurrence classified)) + S ordinal))
             (sym (registrationDecomposition (deletedOccurrence classified))))
             (trans (o20ClosingActionAtAppend name key world error value
               (beforeRegistration (deletedOccurrence classified))
               (MoreTransitions (registrationTransition (deletedOccurrence classified))
                 (afterRegistration (deletedOccurrence classified))) (S ordinal)) exact)))

||| An observed physical Unload index contains a real occurrence, including
||| under an arbitrary finite preceding trace. No trace is reconstructed.
export
0 o20IndexedUnloadOccurs :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {first, finalState : SystemState name key value world error} ->
  (trace : Transitions first finalState) -> (ordinal : Nat) -> (actor : name) ->
  (rawClosingActionAt name key world error value ordinal trace = Just (LUnload actor)) ->
  ActionOccurs (LUnload actor) trace
o20IndexedUnloadOccurs name key world error value NoTransitions ordinal actor exact = absurd exact
o20IndexedUnloadOccurs name key world error value
  (MoreTransitions (Fired nameEq keyEq action tag checked) rest) Z actor exact =
    ActionOccursHere (Fired nameEq keyEq action tag checked) rest (justInjective exact)
o20IndexedUnloadOccurs name key world error value (MoreTransitions step rest) (S ordinal) actor exact =
  ActionOccursLater step rest (o20IndexedUnloadOccurs name key world error value rest ordinal actor exact)

||| Drop the actual birth's preceding trace and its own edge. The strict
||| scan inequality prevents a close at or before that birth from being used.
export
0 o20UnloadBeyondBirthCut :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  {first, before, afterState, finalState : SystemState name key value world error} ->
  (earlier : Transitions first before) -> (birth : Transition before afterState) ->
  (later : Transitions afterState finalState) -> (ordinal : Nat) -> (actor : name) ->
  LT (transitionCount earlier) ordinal ->
  (rawClosingActionAt name key world error value ordinal
    (appendTransitions earlier (MoreTransitions birth later)) = Just (LUnload actor)) ->
  ActionOccurs (LUnload actor) later
o20UnloadBeyondBirthCut name key world error value NoTransitions birth later Z actor afterBirth exact =
  void (succNotLTEzero afterBirth)
o20UnloadBeyondBirthCut name key world error value NoTransitions birth later (S ordinal) actor afterBirth exact =
  o20IndexedUnloadOccurs name key world error value later ordinal actor exact
o20UnloadBeyondBirthCut name key world error value (MoreTransitions step rest) birth later Z actor afterBirth exact =
  void (succNotLTEzero afterBirth)
o20UnloadBeyondBirthCut name key world error value (MoreTransitions step rest) birth later (S ordinal) actor afterBirth exact =
  o20UnloadBeyondBirthCut name key world error value rest birth later ordinal actor (fromLteSucc afterBirth) exact

||| Retain an Unload at its exact source index through the registered filter.
||| BOTH the target action and the native subsequence origin equation are
||| produced; callers cannot independently select their target occurrence.
export
0 o20RegisteredSubsequenceUnloadIndex :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  {first, finalState, otherFirst, otherFinal : SystemState name key value world error} ->
  {trace : Transitions first finalState} -> {survivor : Transitions otherFirst otherFinal} ->
  (kept : GenerationActionSubsequence nameEq (GenerationOwnedActor nameEq registered) ordinal live trace survivor) ->
  O20RegisteredUnloadFree name key world error value nameEq registered ordinal live trace ->
  (actor : name) -> (sourceIndex : Nat) ->
  (rawClosingActionAt name key world error value sourceIndex trace = Just (LUnload actor)) ->
  (targetIndex : Nat ** (rawClosingActionAt name key world error value targetIndex survivor = Just (LUnload actor),
    generationSubsequenceSourceOrdinal kept targetIndex = Just sourceIndex))
o20RegisteredSubsequenceUnloadIndex name key world error value nameEq registered ordinal live
  GenerationActionSubsequenceEnd free actor sourceIndex exact = absurd exact
o20RegisteredSubsequenceUnloadIndex name key world error value nameEq registered ordinal live
  (KeepGenerationAction (Fired sourceEq sourceKey action tag checked) rest
    (Fired targetEq targetKey targetAction targetTag targetChecked) later outside same tail) free actor Z exact =
      (Z ** (trans (cong Just (sym same)) exact, Refl))
o20RegisteredSubsequenceUnloadIndex name key world error value nameEq registered ordinal live
  (KeepGenerationAction step rest target later outside same tail) free actor (S sourceIndex) exact =
    case o20RegisteredSubsequenceUnloadIndex name key world error value nameEq registered (S ordinal)
      (advanceGenerationEnvironment @{nameEq} ordinal (transitionAction step) live)
      tail (o20RegisteredUnloadFreeTail free) actor sourceIndex exact of
        (targetIndex ** (targetExact, originExact)) =>
          (S targetIndex ** (targetExact, cong (map S) originExact))
o20RegisteredSubsequenceUnloadIndex name key world error value nameEq registered ordinal live
  (DeleteGenerationAction (Fired sourceEq sourceKey action tag checked) rest deleted tail) free actor Z exact =
    void (o20RegisteredUnloadHeadExcludes free actor (justInjective exact) deleted)
o20RegisteredSubsequenceUnloadIndex name key world error value nameEq registered ordinal live
  (DeleteGenerationAction step rest deleted tail) free actor (S sourceIndex) exact =
    case o20RegisteredSubsequenceUnloadIndex name key world error value nameEq registered (S ordinal)
      (advanceGenerationEnvironment @{nameEq} ordinal (transitionAction step) live)
      tail (o20RegisteredUnloadFreeTail free) actor sourceIndex exact of
        (targetIndex ** (targetExact, originExact)) =>
          (targetIndex ** (targetExact, cong (map S) originExact))

||| FOREIGN-center analogue retaining the exact close origin. The selected
||| parent is explicitly excluded; its removed center close is NOT retained.
export
0 o20ForeignSubsequenceUnloadIndex :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (selected : name) -> (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  {first, finalState, otherFirst, otherFinal : SystemState name key value world error} ->
  {trace : Transitions first finalState} -> {survivor : Transitions otherFirst otherFinal} ->
  (kept : GenerationActionSubsequence nameEq (EpisodeGenerationDeletedActor nameEq selected registered) ordinal live trace survivor) ->
  O20RegisteredUnloadFree name key world error value nameEq registered ordinal live trace ->
  (actor : name) -> Not (actor = selected) -> (sourceIndex : Nat) ->
  (rawClosingActionAt name key world error value sourceIndex trace = Just (LUnload actor)) ->
  (targetIndex : Nat ** (rawClosingActionAt name key world error value targetIndex survivor = Just (LUnload actor),
    generationSubsequenceSourceOrdinal kept targetIndex = Just sourceIndex))
o20ForeignSubsequenceUnloadIndex name key world error value nameEq selected registered ordinal live
  GenerationActionSubsequenceEnd free actor distinct sourceIndex exact = absurd exact
o20ForeignSubsequenceUnloadIndex name key world error value nameEq selected registered ordinal live
  (KeepGenerationAction (Fired sourceEq sourceKey action tag checked) rest
    (Fired targetEq targetKey targetAction targetTag targetChecked) later outside same tail) free actor distinct Z exact =
      (Z ** (trans (cong Just (sym same)) exact, Refl))
o20ForeignSubsequenceUnloadIndex name key world error value nameEq selected registered ordinal live
  (KeepGenerationAction step rest target later outside same tail) free actor distinct (S sourceIndex) exact =
    case o20ForeignSubsequenceUnloadIndex name key world error value nameEq selected registered (S ordinal)
      (advanceGenerationEnvironment @{nameEq} ordinal (transitionAction step) live)
      tail (o20RegisteredUnloadFreeTail free) actor distinct sourceIndex exact of
        (targetIndex ** (targetExact, originExact)) =>
          (S targetIndex ** (targetExact, cong (map S) originExact))
o20ForeignSubsequenceUnloadIndex name key world error value nameEq selected registered ordinal live
  (DeleteGenerationAction (Fired sourceEq sourceKey action tag checked) rest deleted tail) free actor distinct Z exact =
    void (o20EpisodeDeletedNotForeignUnload nameEq selected registered ordinal live action actor distinct
      (o20RegisteredUnloadHeadExcludes free actor) deleted (justInjective exact))
o20ForeignSubsequenceUnloadIndex name key world error value nameEq selected registered ordinal live
  (DeleteGenerationAction step rest deleted tail) free actor distinct (S sourceIndex) exact =
    case o20ForeignSubsequenceUnloadIndex name key world error value nameEq selected registered (S ordinal)
      (advanceGenerationEnvironment @{nameEq} ordinal (transitionAction step) live)
      tail (o20RegisteredUnloadFreeTail free) actor distinct sourceIndex exact of
        (targetIndex ** (targetExact, originExact)) =>
          (targetIndex ** (targetExact, cong (map S) originExact))
