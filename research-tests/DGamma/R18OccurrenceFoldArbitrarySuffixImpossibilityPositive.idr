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

||| The current occurrence-fold signature accepts an arbitrary replayed suffix
||| with no correspondence to the source suffix. Instantiating an empty source
||| suffix and a one-step replayed suffix makes its own ordinal contract map the
||| target ordinal two to a source ordinal two, which cannot exist.
|||
||| Therefore a total body for the current declaration would prove every
||| transition out of `swappedFinal diamond` impossible. A genuine suffix replay
||| needs source-authenticated occurrence correspondence as an input or must be
||| sealed inside a producer that constructs the replayed suffix simultaneously.
0 arbitraryNonemptyReplayedSuffixMakesFoldVoid :
  (original : Transitions first originalFinal) ->
  (left : Transition first middle) ->
  (right : Transition middle pairFinal) ->
  (diamond : LocalRelationalDiamond name key world error value nameEq keyEq
    left right) ->
  (extra : Transition (swappedFinal diamond) replayedFinal) ->
  original = MoreTransitions left (MoreTransitions right NoTransitions) ->
  Void
arbitraryNonemptyReplayedSuffixMakesFoldVoid original left right diamond extra
  decomposition = case decomposition of
  Refl =>
    let replayedSuffix : Transitions (swappedFinal diamond) replayedFinal
        replayedSuffix = MoreTransitions extra NoTransitions
        swappedTrace : Transitions first replayedFinal
        swappedTrace = MoreTransitions (movedRight diamond)
          (MoreTransitions (movedLeft diamond) replayedSuffix)
        0 fold : AdjacentSwapOperationalOccurrenceFold name key world error value
          (MoreTransitions left (MoreTransitions right NoTransitions))
          NoTransitions left right NoTransitions (movedRight diamond)
          (movedLeft diamond) replayedSuffix swappedTrace
        fold = adjacentSwapOperationalOccurrenceFoldSpike
          (MoreTransitions left (MoreTransitions right NoTransitions))
          NoTransitions left right NoTransitions diamond replayedSuffix
          swappedTrace Refl Refl
        0 extraOccurrence : LocatedActionOccurrence (transitionAction extra)
          swappedTrace
        extraOccurrence = MkLocatedActionOccurrence _ _
          (MoreTransitions (movedRight diamond)
            (MoreTransitions (movedLeft diamond) NoTransitions))
          extra NoTransitions Refl Refl
        0 relation : AdjacentSwapOrdinalRelation Z (S (S Z))
          (locatedActionOrdinal
            (replayActionOrigin (operationalOccurrenceCorrespondence fold)
              extraOccurrence))
        relation = operationalOrdinalRelation fold extraOccurrence
        0 sourceAtTwo : locatedActionOrdinal
          (replayActionOrigin (operationalOccurrenceCorrespondence fold)
            extraOccurrence) = S (S Z)
        sourceAtTwo = zeroTwoSuffixRelationHasSourceTwo relation
    in twoNodeSourceHasNoOrdinalTwo
      (replayActionOrigin (operationalOccurrenceCorrespondence fold)
        extraOccurrence) sourceAtTwo
