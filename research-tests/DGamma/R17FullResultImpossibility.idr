module DGamma.R17FullResultImpossibility

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import Decidable.Equality
import Data.Nat

%default total

data ProbeTraceEmpty : Transitions first finalState -> Type where
  ProbeNoTransitions : ProbeTraceEmpty NoTransitions

0 twoNodeTraceHasNoOrdinalTwo :
  (occurrence : LocatedActionOccurrence action
    (MoreTransitions firstStep (MoreTransitions secondStep NoTransitions))) ->
  locatedActionOrdinal occurrence = 2 -> Void
twoNodeTraceHasNoOrdinalTwo
  (MkLocatedActionOccurrence before after NoTransitions located suffix same
    decomposition) Refl impossible
twoNodeTraceHasNoOrdinalTwo
  (MkLocatedActionOccurrence before after
    (MoreTransitions prefixStep NoTransitions) located suffix same decomposition)
  Refl impossible
twoNodeTraceHasNoOrdinalTwo
  (MkLocatedActionOccurrence before after
    (MoreTransitions prefixStep (MoreTransitions secondPrefix NoTransitions))
    located suffix same Refl) ordinal impossible
twoNodeTraceHasNoOrdinalTwo
  (MkLocatedActionOccurrence before after
    (MoreTransitions prefixStep
      (MoreTransitions secondPrefix (MoreTransitions thirdPrefix prefixRest)))
    located suffix same Refl) ordinal impossible

0 zeroTwoRelationHasSourceTwo :
  AdjacentSwapOrdinalRelation Z (S (S Z)) sourceOrdinal ->
  sourceOrdinal = S (S Z)
zeroTwoRelationHasSourceTwo (AdjacentPrefixOrdinal LTEZero) impossible
zeroTwoRelationHasSourceTwo AdjacentMovedRightOrdinal impossible
zeroTwoRelationHasSourceTwo AdjacentMovedLeftOrdinal impossible
zeroTwoRelationHasSourceTwo (AdjacentSuffixOrdinal after) = Refl

0 pairFoldForcesEmptyReplayedSuffix :
  (left : Transition first middle) ->
  (right : Transition middle originalFinal) ->
  (movedRight : Transition first swappedMiddle) ->
  (movedLeft : Transition swappedMiddle swappedFinal) ->
  (replayedSuffix : Transitions swappedFinal replayedFinal) ->
  (swappedTrace : Transitions first replayedFinal) ->
  (fold : AdjacentSwapOperationalOccurrenceFold name key world error value
    (MoreTransitions left (MoreTransitions right NoTransitions)) NoTransitions
    left right NoTransitions movedRight movedLeft replayedSuffix swappedTrace) ->
  ProbeTraceEmpty replayedSuffix
pairFoldForcesEmptyReplayedSuffix left right movedRight movedLeft NoTransitions
  swappedTrace fold = ProbeNoTransitions
pairFoldForcesEmptyReplayedSuffix left right movedRight movedLeft
  (MoreTransitions extra rest) swappedTrace fold =
    let explicit : Transitions first replayedFinal
        explicit = MoreTransitions movedRight
          (MoreTransitions movedLeft (MoreTransitions extra rest))
        atThirdExplicit : LocatedActionOccurrence (transitionAction extra) explicit
        atThirdExplicit = MkLocatedActionOccurrence _ _
          (MoreTransitions movedRight (MoreTransitions movedLeft NoTransitions))
          extra rest Refl Refl
    in case operationalSwappedDecomposition fold of
      Refl =>
        let relation = operationalOrdinalRelation fold atThirdExplicit
            0 sourceAtTwo : Equal
              (locatedActionOrdinal
                (replayActionOrigin (operationalOccurrenceCorrespondence fold)
                  atThirdExplicit)) (S (S Z))
            sourceAtTwo = zeroTwoRelationHasSourceTwo relation
        in void (twoNodeTraceHasNoOrdinalTwo
          (replayActionOrigin (operationalOccurrenceCorrespondence fold)
            atThirdExplicit) sourceAtTwo)

0 adjacentResultSuffixEmpty :
  (result : AdjacentSwapResult name key world error value protocol nameEq keyEq
    (MoreTransitions left (MoreTransitions right NoTransitions)) NoTransitions
    left right NoTransitions diamond) ->
  ProbeTraceEmpty (replayedSuffix result)
adjacentResultSuffixEmpty {left} {right} {diamond} result =
  pairFoldForcesEmptyReplayedSuffix left right (movedRight diamond)
    (movedLeft diamond) (replayedSuffix result) (swappedTrace result)
    (swappedOccurrenceFold result)

0 sameExternalAfterEmptySuffix :
  (left : Transition first middle) ->
  (right : Transition middle originalFinal) ->
  (movedRight : Transition first swappedMiddle) ->
  (movedLeft : Transition swappedMiddle swappedFinal) ->
  (suffix : Transitions swappedFinal replayedFinal) ->
  ProbeTraceEmpty suffix ->
  (swapped : Transitions first replayedFinal) ->
  swapped = MoreTransitions movedRight (MoreTransitions movedLeft suffix) ->
  SameExternalOrchestration nameEq
    (MoreTransitions left (MoreTransitions right NoTransitions)) swapped ->
  SameExternalOrchestration nameEq
    (MoreTransitions left (MoreTransitions right NoTransitions))
    (MoreTransitions movedRight (MoreTransitions movedLeft NoTransitions))
sameExternalAfterEmptySuffix left right movedRight movedLeft NoTransitions
  ProbeNoTransitions
  (MoreTransitions movedRight (MoreTransitions movedLeft NoTransitions))
  Refl external = external

0 transposedRootInputsImpossible :
  {leftFirst, leftMiddle, leftFinal, rightFirst, rightMiddle, rightFinal :
    SystemState name key value world error} ->
  (left : Transition leftFirst leftMiddle) ->
  (right : Transition leftMiddle leftFinal) ->
  (movedRight : Transition rightFirst rightMiddle) ->
  (movedLeft : Transition rightMiddle rightFinal) ->
  RootOrchestrationStep nameEq left ->
  RootOrchestrationStep nameEq movedRight ->
  Not (transitionAction left = transitionAction movedRight) ->
  SameExternalOrchestration nameEq
    (MoreTransitions left (MoreTransitions right NoTransitions))
    (MoreTransitions movedRight (MoreTransitions movedLeft NoTransitions)) -> Void
transposedRootInputsImpossible left right movedRight movedLeft leftRoot
  movedRightRoot distinct
  (SkipLeftInternal left (MoreTransitions right NoTransitions) leftInternal rest) =
    void (leftInternal leftRoot)
transposedRootInputsImpossible left right movedRight movedLeft leftRoot
  movedRightRoot distinct
  (SkipRightInternal movedRight (MoreTransitions movedLeft NoTransitions)
    movedRightInternal rest) = void (movedRightInternal movedRightRoot)
transposedRootInputsImpossible left right movedRight movedLeft leftRoot
  movedRightRoot distinct
  (MatchExternalInput action left (MoreTransitions right NoTransitions)
    observedLeftRoot movedRight (MoreTransitions movedLeft NoTransitions)
    observedMovedRoot leftAction movedRightAction rest) =
      distinct (trans leftAction (sym movedRightAction))

||| This is a separate obstruction to the user's requested *full* suffix-free
||| witness. For two distinct root insertions, the repaired endpoint exists, but
||| AdjacentSwapResult cannot reorder the externally observable root inputs.
0 suffixFreeDistinctRootInsertResultImpossible :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {first, middle, originalFinal : SystemState name key value world error} ->
  (leftActor, rightActor : name) -> Not (leftActor = rightActor) ->
  (leftComponent, rightComponent : Component key value world error) ->
  (leftTag, rightTag : RuleTag) ->
  (leftChecked : checkedApplyAction @{nameEq} @{keyEq}
    (OInsert leftActor Root leftComponent) first = Just (leftTag, middle)) ->
  (rightChecked : checkedApplyAction @{nameEq} @{keyEq}
    (OInsert rightActor Root rightComponent) middle =
      Just (rightTag, originalFinal)) ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq
    (Fired {before = first} {afterState = middle} nameEq keyEq
      (OInsert leftActor Root leftComponent) leftTag leftChecked)
    (Fired {before = middle} {afterState = originalFinal} nameEq keyEq
      (OInsert rightActor Root rightComponent) rightTag rightChecked)) ->
  AdjacentSwapResult name key world error value protocol nameEq keyEq
    (MoreTransitions
      (Fired {before = first} {afterState = middle} nameEq keyEq
        (OInsert leftActor Root leftComponent) leftTag leftChecked)
      (MoreTransitions
        (Fired {before = middle} {afterState = originalFinal} nameEq keyEq
          (OInsert rightActor Root rightComponent) rightTag rightChecked)
        NoTransitions))
    NoTransitions
    (Fired {before = first} {afterState = middle} nameEq keyEq
      (OInsert leftActor Root leftComponent) leftTag leftChecked)
    (Fired {before = middle} {afterState = originalFinal} nameEq keyEq
      (OInsert rightActor Root rightComponent) rightTag rightChecked)
    NoTransitions diamond -> Void
suffixFreeDistinctRootInsertResultImpossible nameEq keyEq protocol leftActor
  rightActor distinctActors leftComponent rightComponent leftTag rightTag
  leftChecked rightChecked diamond result =
    let left : Transition first middle
        left = Fired nameEq keyEq (OInsert leftActor Root leftComponent) leftTag
          leftChecked
        right : Transition middle originalFinal
        right = Fired nameEq keyEq (OInsert rightActor Root rightComponent)
          rightTag rightChecked
        0 empty : ProbeTraceEmpty (replayedSuffix result)
        empty = adjacentResultSuffixEmpty result
    in let 0 externalExact : SameExternalOrchestration nameEq
             (MoreTransitions left (MoreTransitions right NoTransitions))
             (MoreTransitions (movedRight diamond)
               (MoreTransitions (movedLeft diamond) NoTransitions))
           externalExact = sameExternalAfterEmptySuffix left right
             (movedRight diamond) (movedLeft diamond)
             (replayedSuffix result) empty (swappedTrace result)
             (swappedDecomposition result) (swappedSameExternalInputs result)
           0 leftRoot : RootOrchestrationStep nameEq left
           leftRoot = RootInsertStep Refl
           0 movedRightRoot : RootOrchestrationStep nameEq (movedRight diamond)
           movedRightRoot = RootInsertStep
             (trans (movedRightAction diamond) Refl)
           0 distinctActions : Not
             (transitionAction left = transitionAction (movedRight diamond))
           distinctActions same = distinctActors
             (cong actionOwner (trans same (movedRightAction diamond)))
       in transposedRootInputsImpossible left right
         (movedRight diamond) (movedLeft diamond) leftRoot movedRightRoot
         distinctActions externalExact
