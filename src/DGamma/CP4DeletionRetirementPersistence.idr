module DGamma.CP4DeletionRetirementPersistence

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4DeletionBoundaryDeleted
import DGamma.CP4DeletionGenerationUnique
import DGamma.CP4DeletionInactiveInvariant
import DGamma.CP4DeletionSelectedRetire
import DGamma.CP4DeletionWithdrawalCurrent
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total

0 nothingNotJustRetirement : Nothing = Just value -> Void
nothingNotJustRetirement Refl impossible

0 natLTNotReflexiveRetirement : LT n n -> Void
natLTNotReflexiveRetirement {n = Z} less impossible
natLTNotReflexiveRetirement {n = S k} (LTESucc less) =
  natLTNotReflexiveRetirement less

public export
record RetiredFiberAt
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (actor : name)
  (state : SystemState name key value world error) where
  constructor MkRetiredFiberAt
  retiredFiberAt : Fiber name key value world error
  0 retiredFiberFound : lookupFiber @{nameEq} actor (registry state) =
    Just retiredFiberAt
  0 retiredFiberTrue : retired retiredFiberAt = True

0 currentAfterOneStep :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {afterState, finalState : SystemState name key value world error} ->
  (nameEq : DecEq name) ->
  (actor : name) -> (generation : RegistrationGeneration name) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  GenerationEnvironmentNamesUnique live ->
  LT (generationBirthOrdinal generation) ordinal ->
  (action : Action name key value world error) ->
  (rest : Transitions afterState finalState) ->
  (finalOrdinal : Nat) -> (finalLive : GenerationEnvironment name) ->
  GenerationTraceScan nameEq (S ordinal)
    (advanceGenerationEnvironment @{nameEq} ordinal action live)
    rest finalOrdinal finalLive ->
  lookupCurrentGeneration @{nameEq} actor finalLive = Just generation ->
  lookupCurrentGeneration @{nameEq} actor
    (advanceGenerationEnvironment @{nameEq} ordinal action live) = Just generation
currentAfterOneStep nameEq actor generation ordinal live unique less action rest
  finalOrdinal finalLive scan finalCurrent =
    currentGenerationAtScanStart nameEq actor generation (S ordinal)
      (advanceGenerationEnvironment @{nameEq} ordinal action live)
      (advanceGenerationEnvironmentPreservesUnique nameEq ordinal action live
        unique)
      (lteSuccRight less) rest finalOrdinal finalLive scan finalCurrent

0 retireGivesRetiredInactive :
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (actor : name) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} (ORetire actor) before =
    Just (tag, afterState) ->
  InactiveFiberAt name key world error value nameEq actor before ->
  (RetiredFiberAt name key world error value nameEq actor afterState,
   InactiveFiberAt name key world error value nameEq actor afterState)
retireGivesRetiredInactive nameEq keyEq actor
  (MkSystemState ambient source) afterState
  tag raw inactive = case retireSuccessView nameEq keyEq actor ambient source tag
    afterState raw of
      MkRetireSuccessView fiber found => case inactive of
        MkInactiveFiberAt component parent retiredFlag table outcome
          inactiveFound =>
            let 0 sameFiber = justInjective (trans (sym found) inactiveFound)
            in case sameFiber of
              Refl =>
                let 0 targetFound = lookupReplacedFiber actor fiber
                      (retireFiber fiber) source found
                in (MkRetiredFiberAt (retireFiber fiber) targetFound Refl,
                    MkInactiveFiberAt component parent True table outcome
                      targetFound)

0 retiredAndInactiveForeign :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor : name) -> (action : Action name key value world error) ->
  Not (actor = actionOwner action) ->
  (before, afterState : SystemState name key value world error) ->
  (tag : RuleTag) ->
  applyAction @{nameEq} @{keyEq} action before = Just (tag, afterState) ->
  RetiredFiberAt name key world error value nameEq actor before ->
  InactiveFiberAt name key world error value nameEq actor before ->
  (RetiredFiberAt name key world error value nameEq actor afterState,
   InactiveFiberAt name key world error value nameEq actor afterState)
retiredAndInactiveForeign nameEq keyEq actor action distinct before afterState tag
  raw (MkRetiredFiberAt fiber found retiredTrue) inactive =
    let 0 lookupSame = systemLocalUpdateForeign nameEq actor (actionOwner action)
          distinct before afterState
          (applyActionLocalUpdate nameEq keyEq action before afterState tag raw)
        0 targetFound = trans lookupSame found
        0 targetInactive = case inactive of
          MkInactiveFiberAt component parent retiredFlag table outcome
            inactiveFound =>
              MkInactiveFiberAt component parent retiredFlag table outcome
                (trans lookupSame inactiveFound)
    in (MkRetiredFiberAt fiber targetFound retiredTrue, targetInactive)

||| Once an exact registered generation has retired while Inactive, retirement
||| persists to every later endpoint where that same generation is still
||| current. `NoRegisteredEpisode` eliminates a later L-Begin; the remaining
||| lifecycle rules are impossible from Inactive, O-Remove clears currentness,
||| and every foreign head preserves the exact cell.
public export
0 retiredInactiveCurrentPersists :
  {first, finalState : SystemState name key value world error} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (actor : name) -> (generation : RegistrationGeneration name) ->
  (ordinal : Nat) -> (live : GenerationEnvironment name) ->
  GenerationEnvironmentNamesUnique live ->
  LT (generationBirthOrdinal generation) ordinal ->
  (trace : Transitions first finalState) ->
  (finalOrdinal : Nat) -> (finalLive : GenerationEnvironment name) ->
  GenerationTraceScan nameEq ordinal live trace finalOrdinal finalLive ->
  AlignedTransitions name key world error value nameEq keyEq trace ->
  NoRegisteredEpisode nameEq [generation] ordinal live trace ->
  lookupCurrentGeneration @{nameEq} actor live = Just generation ->
  lookupCurrentGeneration @{nameEq} actor finalLive = Just generation ->
  RetiredFiberAt name key world error value nameEq actor first ->
  InactiveFiberAt name key world error value nameEq actor first ->
  RetiredFiberAt name key world error value nameEq actor finalState
retiredInactiveCurrentPersists nameEq keyEq actor generation ordinal live unique
  less NoTransitions ordinal live GenerationTraceScanEnd AlignedEnd
  NoRegisteredEpisodeEnd currentBefore finalCurrent retiredAt inactive = retiredAt
retiredInactiveCurrentPersists nameEq keyEq actor generation ordinal live unique
  less
  (MoreTransitions
    (Fired {before = first} {afterState = middle}
      nameEq keyEq action tag checked) rest)
  finalOrdinal finalLive
  (GenerationTraceScanStep
    (Fired {before = first} {afterState = middle} nameEq keyEq action tag checked)
    rest tailScan)
  (AlignedStep action tag checked rest alignedTail)
  (NoRegisteredEpisodeStep
    (Fired {before = first} {afterState = middle} nameEq keyEq action tag checked)
    rest noBegin noEpisodeTail)
  currentBefore finalCurrent retiredAt inactive =
    let 0 raw = checkedActionProjects nameEq keyEq action first middle tag checked
        0 nextCurrent = currentAfterOneStep nameEq actor generation ordinal live
          unique less action rest finalOrdinal finalLive tailScan finalCurrent
        0 nextUnique = advanceGenerationEnvironmentPreservesUnique nameEq ordinal
          action live unique
        0 nextLess = lteSuccRight less
    in case decEq @{nameEq} actor (actionOwner action) of
      No distinct =>
        let (nextRetired, nextInactive) = retiredAndInactiveForeign nameEq keyEq
              actor action distinct first middle tag raw retiredAt inactive
        in retiredInactiveCurrentPersists nameEq keyEq actor generation
          (S ordinal) (advanceGenerationEnvironment @{nameEq} ordinal action live)
          nextUnique nextLess rest finalOrdinal finalLive tailScan alignedTail
          noEpisodeTail nextCurrent finalCurrent nextRetired nextInactive
      Yes same => case same of
        Refl => case action of
          OInsert actor parent component =>
            let 0 insertedCurrent = lookupPutCurrentSelf nameEq actor
                  (MkRegistrationGeneration actor ordinal) live
                0 sameGeneration = justInjective
                  (trans (sym insertedCurrent) nextCurrent)
            in case sameGeneration of
              Refl => void (natLTNotReflexiveRetirement less)
          ORetire actor =>
            case retireGivesRetiredInactive nameEq keyEq actor first middle tag
              raw inactive of
              (nextRetired, nextInactive) =>
                retiredInactiveCurrentPersists nameEq keyEq actor generation
                  (S ordinal)
                  (advanceGenerationEnvironment @{nameEq} ordinal
                    (the (Action name key value world error) (ORetire actor)) live)
                  nextUnique nextLess rest finalOrdinal finalLive tailScan
                  alignedTail noEpisodeTail nextCurrent finalCurrent nextRetired
                  nextInactive
          ORemove actor =>
            let 0 removed = lookupDeleteCurrentSelf nameEq actor live unique
            in void (nothingNotJustRetirement (trans (sym removed) nextCurrent))
          LBegin actor =>
            void (noBegin ItIsLBegin (generation ** (currentBefore, Here)))
          LAdvance actor =>
            void (inactiveCannotAdvance nameEq keyEq actor first middle tag raw
              inactive)
          LDivert actor =>
            void (inactiveCannotDivert nameEq keyEq actor first middle tag raw
              inactive)
          LLeave actor =>
            void (inactiveCannotLeave nameEq keyEq actor first middle tag raw
              inactive)
          LUnload actor =>
            void (inactiveCannotUnload nameEq keyEq actor first middle tag raw
              inactive)
