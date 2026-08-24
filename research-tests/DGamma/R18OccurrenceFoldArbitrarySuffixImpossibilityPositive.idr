module DGamma.R18OccurrenceFoldArbitrarySuffixImpossibilityPositive

import DGamma.Calculus
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import Data.Nat
import Decidable.Equality

%default total

||| A two-node source has no occurrence at ordinal two. This is structural and
||| does not depend on transition actions or tags.
0 twoNodeSourceHasNoOrdinalTwo :
  (occurrence : LocatedActionOccurrence action
    (MoreTransitions firstStep (MoreTransitions secondStep NoTransitions))) ->
  locatedActionOrdinal occurrence = 2 -> Void
twoNodeSourceHasNoOrdinalTwo
  (MkLocatedActionOccurrence before after NoTransitions located suffix same
    decomposition) Refl impossible
twoNodeSourceHasNoOrdinalTwo
  (MkLocatedActionOccurrence before after
    (MoreTransitions prefixStep NoTransitions) located suffix same decomposition)
  Refl impossible
twoNodeSourceHasNoOrdinalTwo
  (MkLocatedActionOccurrence before after
    (MoreTransitions prefixStep (MoreTransitions secondPrefix NoTransitions))
    located suffix same Refl) ordinal impossible
twoNodeSourceHasNoOrdinalTwo
  (MkLocatedActionOccurrence before after
    (MoreTransitions prefixStep
      (MoreTransitions secondPrefix (MoreTransitions thirdPrefix prefixRest)))
    located suffix same Refl) ordinal impossible

0 zeroTwoSuffixRelationHasSourceTwo :
  AdjacentSwapOrdinalRelation Z (S (S Z)) sourceOrdinal ->
  sourceOrdinal = S (S Z)
zeroTwoSuffixRelationHasSourceTwo (AdjacentPrefixOrdinal LTEZero) impossible
zeroTwoSuffixRelationHasSourceTwo AdjacentMovedRightOrdinal impossible
zeroTwoSuffixRelationHasSourceTwo AdjacentMovedLeftOrdinal impossible
zeroTwoSuffixRelationHasSourceTwo (AdjacentSuffixOrdinal after) = Refl

||| Self-contained historical copy of the unrestricted revision-18 output
||| record.  It deliberately does not mention the live research fold.  When the
||| false fold declaration is retired, this record continues to pin the exact
||| contract that accepted an arbitrary replayed suffix yet promised complete
||| source occurrence authenticity.
public export
record RetiredUnrestrictedAdjacentSwapOperationalOccurrenceFold
  (name, key, world, error : Type) (value : key -> Type)
  {initial, pairFirst, pairMiddle, pairFinal, originalFinal, swappedMiddle,
    swappedFinal, replayedFinal : SystemState name key value world error}
  (original : Transitions initial originalFinal)
  (prefixTrace : Transitions initial pairFirst)
  (left : Transition pairFirst pairMiddle)
  (right : Transition pairMiddle pairFinal)
  (suffix : Transitions pairFinal originalFinal)
  (movedRight : Transition pairFirst swappedMiddle)
  (movedLeft : Transition swappedMiddle swappedFinal)
  (replayedSuffix : Transitions swappedFinal replayedFinal)
  (swappedTrace : Transitions initial replayedFinal) where
  constructor MkRetiredUnrestrictedAdjacentSwapOperationalOccurrenceFold
  retiredOriginalDecomposition : appendTransitions prefixTrace
    (MoreTransitions left (MoreTransitions right suffix)) = original
  retiredSwappedDecomposition : appendTransitions prefixTrace
    (MoreTransitions movedRight (MoreTransitions movedLeft replayedSuffix)) =
      swappedTrace
  retiredOccurrenceCorrespondence : ActionRegistrationReplayCorrespondence
    name key world error value original swappedTrace
  0 retiredOrdinalRelation :
    {action : Action name key value world error} ->
    (occurrence : LocatedActionOccurrence action swappedTrace) ->
    AdjacentSwapOrdinalRelation (transitionCount prefixTrace)
      (locatedActionOrdinal occurrence)
      (locatedActionOrdinal
        (replayActionOrigin retiredOccurrenceCorrespondence occurrence))

||| The retired unrestricted producer accepts an arbitrary replayed suffix with
||| no correspondence to the source suffix. Instantiating an empty source suffix
||| and a one-step replayed suffix makes its own ordinal contract map target
||| ordinal two to source ordinal two, which cannot exist.
|||
||| This theorem quantifies the retired producer explicitly instead of invoking
||| the live hole.  It therefore remains a meaningful historical impossibility
||| pin after the production-facing fold is narrowed or removed.
0 arbitraryNonemptyReplayedSuffixMakesFoldVoid :
  (original : Transitions first pairFinal) ->
  (left : Transition first middle) ->
  (right : Transition middle pairFinal) ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq
    left right) ->
  (extra : Transition (swappedFinal diamond) replayedFinal) ->
  original = MoreTransitions left (MoreTransitions right NoTransitions) ->
  (0 retiredFold :
    (0 anyReplayedFinal : SystemState name key value world error) ->
    (replayedSuffix : Transitions (swappedFinal diamond) anyReplayedFinal) ->
    (swappedTrace : Transitions first anyReplayedFinal) ->
    appendTransitions NoTransitions
      (MoreTransitions left (MoreTransitions right NoTransitions)) = original ->
    appendTransitions NoTransitions
      (MoreTransitions (movedRight diamond)
        (MoreTransitions (movedLeft diamond) replayedSuffix)) = swappedTrace ->
    RetiredUnrestrictedAdjacentSwapOperationalOccurrenceFold name key world error
      value original NoTransitions left right NoTransitions
      (movedRight diamond) (movedLeft diamond) replayedSuffix swappedTrace) ->
  Void
arbitraryNonemptyReplayedSuffixMakesFoldVoid original left right diamond extra
  decomposition retiredFold = case decomposition of
  Refl =>
    let replayedSuffix : Transitions (swappedFinal diamond) replayedFinal
        replayedSuffix = MoreTransitions extra NoTransitions
        swappedTrace : Transitions first replayedFinal
        swappedTrace = MoreTransitions (movedRight diamond)
          (MoreTransitions (movedLeft diamond) replayedSuffix)
        0 fold : RetiredUnrestrictedAdjacentSwapOperationalOccurrenceFold
          name key world error value
          (MoreTransitions left (MoreTransitions right NoTransitions))
          NoTransitions left right NoTransitions (movedRight diamond)
          (movedLeft diamond) replayedSuffix swappedTrace
        fold = retiredFold replayedFinal replayedSuffix swappedTrace Refl Refl
        0 extraOccurrence : LocatedActionOccurrence (transitionAction extra)
          swappedTrace
        extraOccurrence = MkLocatedActionOccurrence _ _
          (MoreTransitions (movedRight diamond)
            (MoreTransitions (movedLeft diamond) NoTransitions))
          extra NoTransitions Refl Refl
        0 relation : AdjacentSwapOrdinalRelation Z (S (S Z))
          (locatedActionOrdinal
            (replayActionOrigin (retiredOccurrenceCorrespondence fold)
              extraOccurrence))
        relation = retiredOrdinalRelation fold extraOccurrence
        0 sourceAtTwo : locatedActionOrdinal
          (replayActionOrigin (retiredOccurrenceCorrespondence fold)
            extraOccurrence) = S (S Z)
        sourceAtTwo = zeroTwoSuffixRelationHasSourceTwo relation
    in twoNodeSourceHasNoOrdinalTwo
      (replayActionOrigin (retiredOccurrenceCorrespondence fold)
        extraOccurrence) sourceAtTwo
