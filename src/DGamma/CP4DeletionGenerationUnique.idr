module DGamma.CP4DeletionGenerationUnique

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.CP4DeletionPlanBuilder
import Data.List.Elem
import Decidable.Equality

%default total

public export
generationEnvironmentNames : GenerationEnvironment name -> List name
generationEnvironmentNames [] = []
generationEnvironmentNames ((selected, generation) :: rest) =
  selected :: generationEnvironmentNames rest

public export
GenerationEnvironmentNamesUnique : GenerationEnvironment name -> Type
GenerationEnvironmentNamesUnique live =
  UniqueKeys (generationEnvironmentNames live)

0 environmentElemName :
  Elem (selected, generation) live ->
  Elem selected (generationEnvironmentNames live)
environmentElemName {live = (selected, generation) :: rest} Here = Here
environmentElemName {live = (candidate, current) :: rest} (There later) =
  There (environmentElemName later)

0 nameAbsentAfterPutOther :
  (nameEq : DecEq name) ->
  (protected, inserted : name) -> Not (protected = inserted) ->
  (generation : RegistrationGeneration name) ->
  (live : GenerationEnvironment name) ->
  Not (Elem protected (generationEnvironmentNames live)) ->
  Not (Elem protected
    (generationEnvironmentNames
      (putCurrentGeneration @{nameEq} inserted generation live)))
nameAbsentAfterPutOther nameEq protected inserted distinct generation [] absent =
  \present => case present of
    Here => distinct Refl
    There later => absurd later
nameAbsentAfterPutOther nameEq protected inserted distinct generation
  ((candidate, current) :: rest) absent with (decEq @{nameEq} inserted candidate)
  nameAbsentAfterPutOther nameEq protected candidate distinct generation
    ((candidate, current) :: rest) absent | Yes Refl = absent
  nameAbsentAfterPutOther nameEq protected inserted distinct generation
    ((candidate, current) :: rest) absent | No insertedNotCandidate =
      \present => case present of
        Here => absent Here
        There later => nameAbsentAfterPutOther nameEq protected inserted distinct
          generation rest (\old => absent (There old)) later

0 putCurrentGenerationPreservesUnique :
  (nameEq : DecEq name) -> (selected : name) ->
  (generation : RegistrationGeneration name) ->
  (live : GenerationEnvironment name) ->
  GenerationEnvironmentNamesUnique live ->
  GenerationEnvironmentNamesUnique
    (putCurrentGeneration @{nameEq} selected generation live)
putCurrentGenerationPreservesUnique nameEq selected generation [] UniqueNil =
  UniqueCons (\present => case present of Here impossible) UniqueNil
putCurrentGenerationPreservesUnique nameEq selected generation
  ((candidate, current) :: rest) (UniqueCons candidateFresh restUnique)
  with (decEq @{nameEq} selected candidate)
  putCurrentGenerationPreservesUnique nameEq candidate generation
    ((candidate, current) :: rest) (UniqueCons candidateFresh restUnique) |
    Yes Refl = UniqueCons candidateFresh restUnique
  putCurrentGenerationPreservesUnique nameEq selected generation
    ((candidate, current) :: rest) (UniqueCons candidateFresh restUnique) |
    No selectedNotCandidate =
      let candidateNotSelected : Not (candidate = selected)
          candidateNotSelected same = selectedNotCandidate (sym same)
      in UniqueCons
        (nameAbsentAfterPutOther nameEq candidate selected candidateNotSelected
          generation rest candidateFresh)
        (putCurrentGenerationPreservesUnique nameEq selected generation rest
          restUnique)

0 nameAbsentAfterDelete :
  (nameEq : DecEq name) -> (protected, removed : name) ->
  (live : GenerationEnvironment name) ->
  Not (Elem protected (generationEnvironmentNames live)) ->
  Not (Elem protected
    (generationEnvironmentNames
      (deleteCurrentGeneration @{nameEq} removed live)))
nameAbsentAfterDelete nameEq protected removed [] absent =
  \present => absurd present
nameAbsentAfterDelete nameEq protected removed
  ((candidate, current) :: rest) absent with (decEq @{nameEq} removed candidate)
  nameAbsentAfterDelete nameEq protected candidate
    ((candidate, current) :: rest) absent | Yes Refl =
      \present => absent (There present)
  nameAbsentAfterDelete nameEq protected removed
    ((candidate, current) :: rest) absent | No different =
      \present => case present of
        Here => absent Here
        There later => nameAbsentAfterDelete nameEq protected removed rest
          (\old => absent (There old)) later

0 deleteCurrentGenerationPreservesUnique :
  (nameEq : DecEq name) -> (selected : name) ->
  (live : GenerationEnvironment name) ->
  GenerationEnvironmentNamesUnique live ->
  GenerationEnvironmentNamesUnique
    (deleteCurrentGeneration @{nameEq} selected live)
deleteCurrentGenerationPreservesUnique nameEq selected [] UniqueNil = UniqueNil
deleteCurrentGenerationPreservesUnique nameEq selected
  ((candidate, current) :: rest) (UniqueCons candidateFresh restUnique)
  with (decEq @{nameEq} selected candidate)
  deleteCurrentGenerationPreservesUnique nameEq candidate
    ((candidate, current) :: rest) (UniqueCons candidateFresh restUnique) |
    Yes Refl = restUnique
  deleteCurrentGenerationPreservesUnique nameEq selected
    ((candidate, current) :: rest) (UniqueCons candidateFresh restUnique) |
    No different = UniqueCons
      (nameAbsentAfterDelete nameEq candidate selected rest candidateFresh)
      (deleteCurrentGenerationPreservesUnique nameEq selected rest restUnique)

||| Every scanner action preserves raw-name uniqueness in the live generation
||| environment.
public export
0 advanceGenerationEnvironmentPreservesUnique :
  (nameEq : DecEq name) -> (ordinal : Nat) ->
  (action : Action name key value world error) ->
  (live : GenerationEnvironment name) ->
  GenerationEnvironmentNamesUnique live ->
  GenerationEnvironmentNamesUnique
    (advanceGenerationEnvironment @{nameEq} ordinal action live)
advanceGenerationEnvironmentPreservesUnique nameEq ordinal
  (OInsert selected parent component) live unique =
    putCurrentGenerationPreservesUnique nameEq selected
      (MkRegistrationGeneration selected ordinal) live unique
advanceGenerationEnvironmentPreservesUnique nameEq ordinal (ORetire selected)
  live unique = unique
advanceGenerationEnvironmentPreservesUnique nameEq ordinal (ORemove selected)
  live unique = deleteCurrentGenerationPreservesUnique nameEq selected live unique
advanceGenerationEnvironmentPreservesUnique nameEq ordinal (LBegin selected)
  live unique = unique
advanceGenerationEnvironmentPreservesUnique nameEq ordinal (LAdvance selected)
  live unique = unique
advanceGenerationEnvironmentPreservesUnique nameEq ordinal (LDivert selected)
  live unique = unique
advanceGenerationEnvironmentPreservesUnique nameEq ordinal (LLeave selected)
  live unique = unique
advanceGenerationEnvironmentPreservesUnique nameEq ordinal (LUnload selected)
  live unique = unique

||| A completed generation scan transports uniqueness from its initial to final
||| environment.
public export
0 generationTraceScanPreservesUnique :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  {trace : Transitions first finalState} ->
  {ordinal, finalOrdinal : Nat} ->
  {live, finalLive : GenerationEnvironment name} ->
  (nameEq : DecEq name) ->
  (scan : GenerationTraceScan
    {name = name} {key = key} {value = value} {world = world} {error = error}
    nameEq ordinal live trace finalOrdinal finalLive) ->
  GenerationEnvironmentNamesUnique live ->
  GenerationEnvironmentNamesUnique finalLive
generationTraceScanPreservesUnique nameEq GenerationTraceScanEnd unique = unique
generationTraceScanPreservesUnique nameEq
  (GenerationTraceScanStep transition rest tail) unique =
    generationTraceScanPreservesUnique nameEq tail
      (advanceGenerationEnvironmentPreservesUnique nameEq _
        (transitionAction transition) _ unique)

||| Under scanner uniqueness, list membership identifies the exact result of
||| current-generation lookup.
public export
0 lookupCurrentGenerationFromElem :
  (nameEq : DecEq name) ->
  (live : GenerationEnvironment name) ->
  GenerationEnvironmentNamesUnique live ->
  Elem (selected, generation) live ->
  lookupCurrentGeneration @{nameEq} selected live = Just generation
lookupCurrentGenerationFromElem nameEq
  ((selected, generation) :: rest) (UniqueCons fresh uniqueRest) Here
  with (decEq @{nameEq} selected selected)
  lookupCurrentGenerationFromElem nameEq
    ((selected, generation) :: rest) (UniqueCons fresh uniqueRest) Here |
    Yes Refl = Refl
  lookupCurrentGenerationFromElem nameEq
    ((selected, generation) :: rest) (UniqueCons fresh uniqueRest) Here |
    No contra = void (contra Refl)
lookupCurrentGenerationFromElem {selected} nameEq
  ((candidate, current) :: rest) (UniqueCons fresh uniqueRest) (There later)
  with (decEq @{nameEq} selected candidate)
  lookupCurrentGenerationFromElem {selected} nameEq
    ((candidate, current) :: rest) (UniqueCons fresh uniqueRest) (There later) |
    Yes same = case same of
      Refl => void (fresh (environmentElemName later))
  lookupCurrentGenerationFromElem {selected} nameEq
    ((candidate, current) :: rest) (UniqueCons fresh uniqueRest) (There later) |
    No different = lookupCurrentGenerationFromElem nameEq rest uniqueRest later

||| Bridge the public endpoint notion to the stronger plan-builder notion.
public export
0 currentGenerationOutsideImpliesActorOutsidePlan :
  (nameEq : DecEq name) ->
  (registered : List (RegistrationGeneration name)) ->
  (live : GenerationEnvironment name) ->
  GenerationEnvironmentNamesUnique live ->
  (actor : name) ->
  CurrentGenerationOutside {nameEq = nameEq} registered live actor ->
  ActorOutsideCurrentRegistered actor registered live
currentGenerationOutsideImpliesActorOutsidePlan nameEq registered live unique
  actor outside selected generation present member same =
    case same of
      Refl => outside generation
        (lookupCurrentGenerationFromElem nameEq live unique present) member
