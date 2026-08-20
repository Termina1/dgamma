module DGamma.CP4DeletionWithdrawalCurrent

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionGenerationUnique
import DGamma.CP4DeletionInactiveInvariant
import Data.Nat
import Decidable.Equality

%default total

0 nothingIsNotJustCurrent : Nothing = Just item -> Void
nothingIsNotJustCurrent Refl impossible

0 natLTNotReflexive : LT n n -> Void
natLTNotReflexive {n = Z} less impossible
natLTNotReflexive {n = S k} (LTESucc less) = natLTNotReflexive less

||| A generation older than the current scanner ordinal cannot be manufactured
||| again by a later raw-name insertion.  Consequently, if it is still current
||| at the end of a scanned suffix, it was already current at the suffix source.
||| This is the key backward fact used to attach an occurrence-local O-Retire to
||| the exact current generation rather than to a later raw-name reissue.
public export
0 currentGenerationAtScanStart :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {first, finalState : SystemState name key value world error} ->
  (nameEq : DecEq name) ->
  (actor : name) -> (generation : RegistrationGeneration name) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  GenerationEnvironmentNamesUnique live ->
  LT (generationBirthOrdinal generation) ordinal ->
  (trace : Transitions first finalState) ->
  (finalOrdinal : Nat) -> (finalLive : GenerationEnvironment name) ->
  GenerationTraceScan nameEq ordinal live trace finalOrdinal finalLive ->
  lookupCurrentGeneration @{nameEq} actor finalLive = Just generation ->
  lookupCurrentGeneration @{nameEq} actor live = Just generation
currentGenerationAtScanStart nameEq actor generation ordinal live unique less
  NoTransitions ordinal live GenerationTraceScanEnd finalCurrent = finalCurrent
currentGenerationAtScanStart nameEq actor generation ordinal live unique less
  (MoreTransitions transition@(Fired stepNameEq stepKeyEq action tag checked)
    rest)
  finalOrdinal finalLive
  (GenerationTraceScanStep
    (Fired _ _ action tag checked) rest tailScan)
  finalCurrent =
    let 0 nextUnique : GenerationEnvironmentNamesUnique
          (advanceGenerationEnvironment @{nameEq} ordinal action live)
        nextUnique = advanceGenerationEnvironmentPreservesUnique nameEq ordinal
          action live unique
        0 nextCurrent : lookupCurrentGeneration @{nameEq} actor
          (advanceGenerationEnvironment @{nameEq} ordinal action live) =
          Just generation
        nextCurrent = currentGenerationAtScanStart nameEq actor generation
          (S ordinal)
          (advanceGenerationEnvironment @{nameEq} ordinal action live) nextUnique (lteSuccRight less) rest finalOrdinal
          finalLive tailScan finalCurrent
    in actionBackward action nextCurrent
  where
  0 actionBackward :
    (observed : Action name key value world error) ->
    lookupCurrentGeneration @{nameEq} actor
      (advanceGenerationEnvironment @{nameEq} ordinal observed live) =
      Just generation ->
    lookupCurrentGeneration @{nameEq} actor live = Just generation
  actionBackward (OInsert inserted parent component) next
    with (decEq @{nameEq} actor inserted)
    actionBackward (OInsert inserted parent component) next | Yes same =
      case same of
        Refl =>
          let fresh : RegistrationGeneration name
              fresh = MkRegistrationGeneration actor ordinal
              0 freshLookup : lookupCurrentGeneration @{nameEq} actor
                (putCurrentGeneration @{nameEq} actor fresh live) = Just fresh
              freshLookup = lookupPutCurrentSelf nameEq actor fresh live
              0 sameGeneration : fresh = generation
              sameGeneration = justInjective (trans (sym freshLookup) next)
              0 sameBirth : ordinal = generationBirthOrdinal generation
              sameBirth = cong generationBirthOrdinal sameGeneration
              impossibleLT : LT ordinal ordinal
              impossibleLT = replace
                {p = \observed => LT observed ordinal}
                (sym sameBirth) less
          in void (natLTNotReflexive impossibleLT)
    actionBackward (OInsert inserted parent component) next | No distinct =
      trans (sym (lookupPutCurrentOther nameEq actor inserted distinct
        (MkRegistrationGeneration inserted ordinal) live)) next
  actionBackward (ORetire retiredActor) next = next
  actionBackward (ORemove removed) next
    with (decEq @{nameEq} actor removed)
    actionBackward (ORemove removed) next | Yes same = case same of
      Refl =>
        let removedLookup = lookupDeleteCurrentSelf nameEq actor live unique
        in void (nothingIsNotJustCurrent (trans (sym removedLookup) next))
    actionBackward (ORemove removed) next | No distinct =
      trans (sym (lookupAdvanceGenerationOther nameEq ordinal
        (the (Action name key value world error) (ORemove removed)) actor
        distinct live)) next
  actionBackward (LBegin lifecycleActor) next = next
  actionBackward (LAdvance lifecycleActor) next = next
  actionBackward (LDivert lifecycleActor) next = next
  actionBackward (LLeave lifecycleActor) next = next
  actionBackward (LUnload lifecycleActor) next = next

