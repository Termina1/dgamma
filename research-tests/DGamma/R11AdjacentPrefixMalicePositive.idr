module DGamma.R11AdjacentPrefixMalicePositive

import DGamma.Calculus
import DGamma.CP3
import DGamma.CP5ConfluenceLocalDiamondSpike
import Data.Nat

%default total

public export
0 adjacentPrefixRelationForcesIdentity :
  LT targetOrdinal prefixCount ->
  AdjacentSwapOrdinalRelation prefixCount targetOrdinal sourceOrdinal ->
  sourceOrdinal = targetOrdinal
adjacentPrefixRelationForcesIdentity before (AdjacentPrefixOrdinal kept) = Refl
adjacentPrefixRelationForcesIdentity before AdjacentMovedRightOrdinal =
  void (adjacentPrefixNotMovedRight before)
adjacentPrefixRelationForcesIdentity before AdjacentMovedLeftOrdinal =
  void (adjacentPrefixNotMovedLeft before)
adjacentPrefixRelationForcesIdentity before (AdjacentSuffixOrdinal after) =
  void (adjacentPrefixNotSuffix before after)

||| Two same-action/same-tag prefix occurrences cannot be collapsed by the
||| operational fold. The tag equality is explicit so repeated Iter nodes are
||| covered rather than silently relying on distinct actions.
public export
0 repeatedPrefixCollapseRejected :
  (fold : AdjacentSwapOperationalOccurrenceFold name key world error value
    original tracePrefix left right suffix movedRight movedLeft replayedSuffix
    swappedTrace) ->
  {action : Action name key value world error} ->
  (first, second : LocatedActionOccurrence action swappedTrace) ->
  transitionTag (locatedTransition first) = transitionTag (locatedTransition second) ->
  LT (locatedActionOrdinal second) (transitionCount tracePrefix) ->
  locatedActionOrdinal
    (replayActionOrigin (operationalOccurrenceCorrespondence fold) second) =
    locatedActionOrdinal first ->
  Not (locatedActionOrdinal first = locatedActionOrdinal second) -> Void
repeatedPrefixCollapseRejected fold first second sameTag before collapsed distinct =
  let authentic = adjacentPrefixRelationForcesIdentity before
        (operationalOrdinalRelation fold second)
   in distinct (trans (sym collapsed) authentic)

||| Swapping two repeated prefix origins is equally impossible; the first half
||| already contradicts exhaustive prefix identity.
public export
0 repeatedPrefixPermutationRejected :
  (fold : AdjacentSwapOperationalOccurrenceFold name key world error value
    original tracePrefix left right suffix movedRight movedLeft replayedSuffix
    swappedTrace) ->
  {action : Action name key value world error} ->
  (first, second : LocatedActionOccurrence action swappedTrace) ->
  transitionTag (locatedTransition first) = transitionTag (locatedTransition second) ->
  LT (locatedActionOrdinal first) (transitionCount tracePrefix) ->
  LT (locatedActionOrdinal second) (transitionCount tracePrefix) ->
  locatedActionOrdinal
    (replayActionOrigin (operationalOccurrenceCorrespondence fold) first) =
    locatedActionOrdinal second ->
  locatedActionOrdinal
    (replayActionOrigin (operationalOccurrenceCorrespondence fold) second) =
    locatedActionOrdinal first ->
  Not (locatedActionOrdinal first = locatedActionOrdinal second) -> Void
repeatedPrefixPermutationRejected fold first second sameTag firstBefore secondBefore
  firstToSecond secondToFirst distinct =
  let authentic = adjacentPrefixRelationForcesIdentity firstBefore
        (operationalOrdinalRelation fold first)
   in distinct (trans (sym authentic) firstToSecond)
