module DGamma.CP4DeletionGenerationBounds

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total

0 justInjectiveBounds : Just left = Just right -> left = right
justInjectiveBounds Refl = Refl

||| Every live generation was born strictly before the scanner's next ordinal.
||| This invariant is independent of registry state and follows solely from the
||| executable generation scanner.
public export
GenerationEnvironmentBounded : Nat -> GenerationEnvironment name -> Type
GenerationEnvironmentBounded ordinal [] = Unit
GenerationEnvironmentBounded ordinal
  ((selected, generation) :: rest) =
    (LT (generationBirthOrdinal generation) ordinal,
     GenerationEnvironmentBounded ordinal rest)

0 weakenEnvironmentBound :
  GenerationEnvironmentBounded ordinal live ->
  GenerationEnvironmentBounded (S ordinal) live
weakenEnvironmentBound {live = []} bounded = ()
weakenEnvironmentBound {live = (selected, generation) :: rest}
  (headBound, tailBound) =
    (lteSuccRight headBound, weakenEnvironmentBound tailBound)

0 putCurrentGenerationBounded :
  (nameEq : DecEq name) -> (selected : name) ->
  (live : GenerationEnvironment name) ->
  GenerationEnvironmentBounded ordinal live ->
  GenerationEnvironmentBounded (S ordinal)
    (putCurrentGeneration @{nameEq} selected
      (MkRegistrationGeneration selected ordinal) live)
putCurrentGenerationBounded nameEq selected [] bounded =
  (reflexive, ())
putCurrentGenerationBounded nameEq selected
  ((candidate, current) :: rest) (headBound, tailBound)
  with (decEq @{nameEq} selected candidate)
  putCurrentGenerationBounded nameEq candidate
    ((candidate, current) :: rest) (headBound, tailBound) | Yes Refl =
      (reflexive, weakenEnvironmentBound tailBound)
  putCurrentGenerationBounded nameEq selected
    ((candidate, current) :: rest) (headBound, tailBound) | No distinct =
      (lteSuccRight headBound,
       putCurrentGenerationBounded nameEq selected rest tailBound)

0 deleteCurrentGenerationBounded :
  (nameEq : DecEq name) -> (selected : name) ->
  (live : GenerationEnvironment name) ->
  GenerationEnvironmentBounded ordinal live ->
  GenerationEnvironmentBounded (S ordinal)
    (deleteCurrentGeneration @{nameEq} selected live)
deleteCurrentGenerationBounded nameEq selected [] bounded = ()
deleteCurrentGenerationBounded nameEq selected
  ((candidate, current) :: rest) (headBound, tailBound)
  with (decEq @{nameEq} selected candidate)
  deleteCurrentGenerationBounded nameEq candidate
    ((candidate, current) :: rest) (headBound, tailBound) | Yes Refl =
      weakenEnvironmentBound tailBound
  deleteCurrentGenerationBounded nameEq selected
    ((candidate, current) :: rest) (headBound, tailBound) | No distinct =
      (lteSuccRight headBound,
       deleteCurrentGenerationBounded nameEq selected rest tailBound)

||| One scanner step preserves the birth-before-next-ordinal invariant.
public export
0 advanceGenerationEnvironmentBounded :
  (nameEq : DecEq name) -> (ordinal : Nat) ->
  (action : Action name key value world error) ->
  (live : GenerationEnvironment name) ->
  GenerationEnvironmentBounded ordinal live ->
  GenerationEnvironmentBounded (S ordinal)
    (advanceGenerationEnvironment @{nameEq} ordinal action live)
advanceGenerationEnvironmentBounded nameEq ordinal
  (OInsert inserted parent component) live bounded =
    putCurrentGenerationBounded nameEq inserted live bounded
advanceGenerationEnvironmentBounded nameEq ordinal (ORetire selected) live
  bounded = weakenEnvironmentBound bounded
advanceGenerationEnvironmentBounded nameEq ordinal (ORemove selected) live
  bounded = deleteCurrentGenerationBounded nameEq selected live bounded
advanceGenerationEnvironmentBounded nameEq ordinal (LBegin selected) live
  bounded = weakenEnvironmentBound bounded
advanceGenerationEnvironmentBounded nameEq ordinal (LAdvance selected) live
  bounded = weakenEnvironmentBound bounded
advanceGenerationEnvironmentBounded nameEq ordinal (LDivert selected) live
  bounded = weakenEnvironmentBound bounded
advanceGenerationEnvironmentBounded nameEq ordinal (LLeave selected) live
  bounded = weakenEnvironmentBound bounded
advanceGenerationEnvironmentBounded nameEq ordinal (LUnload selected) live
  bounded = weakenEnvironmentBound bounded

0 lookupCurrentGenerationBounded :
  (nameEq : DecEq name) -> (selected : name) ->
  (live : GenerationEnvironment name) ->
  GenerationEnvironmentBounded ordinal live ->
  lookupCurrentGeneration @{nameEq} selected live = Just generation ->
  LT (generationBirthOrdinal generation) ordinal
lookupCurrentGenerationBounded nameEq selected [] bounded found =
  case found of Refl impossible
lookupCurrentGenerationBounded nameEq selected
  ((candidate, current) :: rest) (headBound, tailBound) found
  with (decEq @{nameEq} selected candidate)
  lookupCurrentGenerationBounded nameEq candidate
    ((candidate, current) :: rest) (headBound, tailBound) found | Yes Refl =
      case justInjectiveBounds found of Refl => headBound
  lookupCurrentGenerationBounded nameEq selected
    ((candidate, current) :: rest) (headBound, tailBound) found | No distinct =
      lookupCurrentGenerationBounded nameEq selected rest tailBound found

||| Every action-associated generation at a source boundary was born before the
||| boundary immediately after that action. O-Insert is the sharp equality case;
||| all other actions use the current-generation environment invariant.
public export
0 actionGenerationBeforeNext :
  (nameEq : DecEq name) -> (ordinal : Nat) ->
  (live : GenerationEnvironment name) ->
  GenerationEnvironmentBounded ordinal live ->
  (action : Action name key value world error) ->
  actionGenerationAt @{nameEq} ordinal live action = Just generation ->
  LT (generationBirthOrdinal generation) (S ordinal)
actionGenerationBeforeNext nameEq ordinal live bounded
  (OInsert inserted parent component) found =
    case justInjectiveBounds found of Refl => reflexive
actionGenerationBeforeNext nameEq ordinal live bounded
  action@(ORetire selected) found =
    lteSuccRight
      (lookupCurrentGenerationBounded nameEq selected live bounded found)
actionGenerationBeforeNext nameEq ordinal live bounded
  action@(ORemove selected) found =
    lteSuccRight
      (lookupCurrentGenerationBounded nameEq selected live bounded found)
actionGenerationBeforeNext nameEq ordinal live bounded
  action@(LBegin selected) found =
    lteSuccRight
      (lookupCurrentGenerationBounded nameEq selected live bounded found)
actionGenerationBeforeNext nameEq ordinal live bounded
  action@(LAdvance selected) found =
    lteSuccRight
      (lookupCurrentGenerationBounded nameEq selected live bounded found)
actionGenerationBeforeNext nameEq ordinal live bounded
  action@(LDivert selected) found =
    lteSuccRight
      (lookupCurrentGenerationBounded nameEq selected live bounded found)
actionGenerationBeforeNext nameEq ordinal live bounded
  action@(LLeave selected) found =
    lteSuccRight
      (lookupCurrentGenerationBounded nameEq selected live bounded found)
actionGenerationBeforeNext nameEq ordinal live bounded
  action@(LUnload selected) found =
    lteSuccRight
      (lookupCurrentGenerationBounded nameEq selected live bounded found)

||| The start ordinal of any finite generation scan is no later than its final
||| ordinal. The tail form is the strict fact needed at a nonempty prefix.
public export
0 generationScanStartLTE :
  GenerationTraceScan nameEq ordinal live trace finalOrdinal finalLive ->
  LTE ordinal finalOrdinal
generationScanStartLTE GenerationTraceScanEnd = reflexive
generationScanStartLTE
  (GenerationTraceScanStep transition rest tail) =
    lteSuccLeft (generationScanStartLTE tail)

0 registeredBirthAfterScan :
  ((generation : RegistrationGeneration name) -> Elem generation registered ->
    LTE finalOrdinal (generationBirthOrdinal generation)) ->
  (generation : RegistrationGeneration name) -> Elem generation registered ->
  LTE finalOrdinal (generationBirthOrdinal generation)
registeredBirthAfterScan lower generation member = lower generation member

0 generationOwnedImpossibleBeforeFinal :
  (nameEq : DecEq name) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal, finalOrdinal : Nat) ->
  (live : GenerationEnvironment name) ->
  GenerationEnvironmentBounded ordinal live ->
  LTE (S ordinal) finalOrdinal ->
  ((generation : RegistrationGeneration name) -> Elem generation registered ->
    LTE finalOrdinal (generationBirthOrdinal generation)) ->
  (action : Action name key value world error) ->
  GenerationOwnedActor nameEq registered ordinal live action -> Void
generationOwnedImpossibleBeforeFinal nameEq registered ordinal finalOrdinal live
  bounded stepToFinal registeredLower action
  (generation ** (owned, member)) =
    let bornBeforeNext = actionGenerationBeforeNext nameEq ordinal live bounded action owned in
    let finalBeforeBirth = registeredLower generation member in
    let absurdBound = transitive bornBeforeNext
          (transitive stepToFinal finalBeforeBirth) in
    succNotLTEpred absurdBound

||| A trace prefix ending before every registered birth is retained verbatim.
||| This supplies `DeletionResult.beforeDeletion` constructively: generation
||| filtering cannot erase an action before the selected episode starts.
public export
0 generationPrefixIdentitySubsequence :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  (nameEq : DecEq name) ->
  (registered : List (RegistrationGeneration name)) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  (trace : Transitions first finalState) ->
  (finalOrdinal : Nat) -> (finalLive : GenerationEnvironment name) ->
  GenerationEnvironmentBounded ordinal live ->
  (scan : GenerationTraceScan nameEq ordinal live trace finalOrdinal finalLive) ->
  ((generation : RegistrationGeneration name) -> Elem generation registered ->
    LTE finalOrdinal (generationBirthOrdinal generation)) ->
  GenerationActionSubsequence nameEq
    (GenerationOwnedActor nameEq registered) ordinal live trace trace
generationPrefixIdentitySubsequence nameEq registered ordinal live NoTransitions
  ordinal live bounded GenerationTraceScanEnd registeredLower =
    GenerationActionSubsequenceEnd
generationPrefixIdentitySubsequence nameEq registered ordinal live
  (MoreTransitions transition rest) finalOrdinal finalLive bounded
  (GenerationTraceScanStep transition rest tailScan) registeredLower =
    let stepToFinal : LTE (S ordinal) finalOrdinal
        stepToFinal = generationScanStartLTE tailScan
        notOwned : Not (GenerationOwnedActor nameEq registered ordinal live
          (transitionAction transition))
        notOwned = generationOwnedImpossibleBeforeFinal nameEq registered ordinal
          finalOrdinal live bounded stepToFinal registeredLower
          (transitionAction transition)
        0 nextBounded : GenerationEnvironmentBounded (S ordinal)
          (advanceGenerationEnvironment @{nameEq} ordinal
            (transitionAction transition) live)
        nextBounded = advanceGenerationEnvironmentBounded nameEq ordinal
          (transitionAction transition) live bounded
        0 tail : GenerationActionSubsequence nameEq
          (GenerationOwnedActor nameEq registered) (S ordinal)
          (advanceGenerationEnvironment @{nameEq} ordinal
            (transitionAction transition) live) rest rest
        tail = generationPrefixIdentitySubsequence nameEq registered (S ordinal)
          (advanceGenerationEnvironment @{nameEq} ordinal
            (transitionAction transition) live)
          rest finalOrdinal finalLive nextBounded tailScan registeredLower
    in KeepGenerationAction transition rest transition rest notOwned Refl tail

||| `RegisteredGenerationsDuring` pins every selected-episode birth at or after
||| the supplied episode start ordinal.
public export
0 registeredDuringBirthLowerBound :
  (registeredDuring : RegisteredGenerationsDuring selected startOrdinal
    registered episodeTrace) ->
  (generation : RegistrationGeneration name) -> Elem generation registered ->
  LTE startOrdinal (generationBirthOrdinal generation)
registeredDuringBirthLowerBound registeredDuring generation member =
  case fst registeredDuring generation member of
    MkGeneratedDuring child component birth stamp retiresLater =>
      rewrite stamp in lteAddRight startOrdinal

||| The exact public-alias prefix constructor, specialized to the empty initial
||| scanner environment used by Lemma 72.
public export
0 deletionBeforeIdentity :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  (nameEq : DecEq name) ->
  (registered : List (RegistrationGeneration name)) ->
  (trace : Transitions first finalState) ->
  (episodeStartOrdinal : Nat) ->
  (episodeStartLive : GenerationEnvironment name) ->
  GenerationTraceScan nameEq 0 [] trace episodeStartOrdinal episodeStartLive ->
  ((generation : RegistrationGeneration name) -> Elem generation registered ->
    LTE episodeStartOrdinal (generationBirthOrdinal generation)) ->
  GenerationActionSubsequence nameEq
    (GenerationOwnedActor nameEq registered) 0 [] trace trace
deletionBeforeIdentity nameEq registered trace episodeStartOrdinal
  episodeStartLive scan registeredLower =
    generationPrefixIdentitySubsequence nameEq registered 0 [] trace
      episodeStartOrdinal episodeStartLive () scan registeredLower

||| Direct assembly from the two corresponding public `deletionTheorem`
||| premises. The selected episode trace determines the lower birth bound; the
||| supplied prefix scan determines the exact boundary ordinal/environment.
public export
0 deletionBeforeFromRegisteredDuring :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {initial, episodePre, episodeEnd : SystemState name key value world error} ->
  (nameEq : DecEq name) ->
  (selected : name) ->
  (registered : List (RegistrationGeneration name)) ->
  (before : Transitions initial episodePre) ->
  (episodeTrace : Transitions episodePre episodeEnd) ->
  (episodeStartOrdinal : Nat) ->
  (episodeStartLive : GenerationEnvironment name) ->
  GenerationTraceScan nameEq 0 [] before episodeStartOrdinal episodeStartLive ->
  RegisteredGenerationsDuring selected episodeStartOrdinal registered episodeTrace ->
  GenerationActionSubsequence nameEq
    (GenerationOwnedActor nameEq registered) 0 [] before before
deletionBeforeFromRegisteredDuring nameEq selected registered before episodeTrace
  episodeStartOrdinal episodeStartLive beforeScan registeredDuring =
    deletionBeforeIdentity nameEq registered before episodeStartOrdinal
      episodeStartLive beforeScan
      (registeredDuringBirthLowerBound registeredDuring)
