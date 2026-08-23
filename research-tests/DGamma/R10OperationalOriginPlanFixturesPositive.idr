module DGamma.R10OperationalOriginPlanFixturesPositive

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.Metatheory
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import Data.Nat
import Decidable.Equality

%default total

||| Raw semantic fields for one operational swap, deliberately excluding an
||| occurrence correspondence.  The constructor below materializes the actual
||| `AdjacentSwapResult`; its map is therefore the globally sealed O6 fold.
public export
0 materializeAdjacentSwapResult :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, pairFirst, pairMiddle, pairFinal, originalFinal :
    SystemState name key value world error} ->
  {original : Transitions initial originalFinal} ->
  {tracePrefix : Transitions initial pairFirst} ->
  {left : Transition pairFirst pairMiddle} ->
  {right : Transition pairMiddle pairFinal} ->
  {suffix : Transitions pairFinal originalFinal} ->
  {diamond : LocalRelationalDiamond name key world error value nameEq keyEq
    left right} ->
  (replayedFinal : SystemState name key value world error) ->
  (replayedSuffix : Transitions (swappedFinal diamond) replayedFinal) ->
  (swappedTrace : Transitions initial replayedFinal) ->
  appendTransitions tracePrefix
    (MoreTransitions left (MoreTransitions right suffix)) = original ->
  swappedTrace = appendTransitions tracePrefix
    (MoreTransitions (movedRight diamond)
      (MoreTransitions (movedLeft diamond) replayedSuffix)) ->
  SameExternalOrchestration nameEq original swappedTrace ->
  RelationalReplayCorrespondence name key world error value original swappedTrace ->
  RelationalReplayEndpoint name key world error value nameEq keyEq originalFinal
    replayedFinal ->
  ReplayInvariantBundle name key world error value protocol nameEq keyEq
    swappedTrace ->
  AdjacentSwapResult name key world error value protocol nameEq keyEq original
    tracePrefix left right suffix diamond
materializeAdjacentSwapResult {original = original} {tracePrefix = tracePrefix} {left = left} {right = right} {suffix = suffix} {diamond = diamond} replayedFinal replayedSuffix swappedTrace originalExact
  swappedExact external replay endpoint premises =
    MkAdjacentSwapResult replayedFinal replayedSuffix swappedTrace originalExact
      swappedExact external replay endpoint premises

||| Raw recursive origin evidence.  Unlike `BlockCrossingOriginPlan`, each step
||| contains the semantic ingredients of an adjacent swap, not an already-built
||| result, derivation node, label, or plan node.
public export
data RawOperationalOriginPlan :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (protocol : RegistrationProtocol key value world error) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  {sourceInitial, sourceFinal : SystemState name key value world error} ->
  (sourceTrace : Transitions sourceInitial sourceFinal) ->
  {leftActor, rightActor : name} ->
  (leftBlock : LocatedOpenEpisodeBlock name key world error value nameEq keyEq
    leftActor sourceTrace) ->
  (rightBlock : LocatedOpenEpisodeBlock name key world error value nameEq keyEq
    rightActor sourceTrace) ->
  {currentInitial, currentFinal, targetFinal :
    SystemState name key value world error} ->
  (current : Transitions currentInitial currentFinal) ->
  (prefixOccurrences : ActionRegistrationReplayCorrespondence name key world
    error value sourceTrace current) ->
  (target : Transitions currentInitial targetFinal) ->
  List (Nat, Nat) -> Type where
  RawOriginDone :
    RawOperationalOriginPlan name key world error value protocol nameEq keyEq
      sourceTrace leftBlock rightBlock current prefixOccurrences current []
  RawOriginStep :
    {initial, pairFirst, pairMiddle, pairFinal, originalFinal, replayedFinal,
      targetFinal : SystemState name key value world error} ->
    {leftPosition, rightPosition : Nat} ->
    {sourceInitial, sourceFinal : SystemState name key value world error} ->
    (sourceTrace : Transitions sourceInitial sourceFinal) ->
    {leftActor, rightActor : name} ->
    (leftBlock : LocatedOpenEpisodeBlock name key world error value nameEq keyEq
      leftActor sourceTrace) ->
    (rightBlock : LocatedOpenEpisodeBlock name key world error value nameEq keyEq
      rightActor sourceTrace) ->
    (original : Transitions initial originalFinal) ->
    (tracePrefix : Transitions initial pairFirst) ->
    (left : Transition pairFirst pairMiddle) ->
    (right : Transition pairMiddle pairFinal) ->
    (suffix : Transitions pairFinal originalFinal) ->
    (orientation : AdjacentSwapOrientationEvidence left right) ->
    (diamond : LocalRelationalDiamond name key world error value nameEq keyEq
      left right) ->
    (replayedSuffix : Transitions (swappedFinal diamond) replayedFinal) ->
    (swappedTrace : Transitions initial replayedFinal) ->
    (originalExact : appendTransitions tracePrefix
      (MoreTransitions left (MoreTransitions right suffix)) = original) ->
    (swappedExact : swappedTrace = appendTransitions tracePrefix
      (MoreTransitions (movedRight diamond)
        (MoreTransitions (movedLeft diamond) replayedSuffix))) ->
    (external : SameExternalOrchestration nameEq original swappedTrace) ->
    (replay : RelationalReplayCorrespondence name key world error value original
      swappedTrace) ->
    (endpoint : RelationalReplayEndpoint name key world error value nameEq keyEq
      originalFinal replayedFinal) ->
    (premises : ReplayInvariantBundle name key world error value protocol nameEq
      keyEq swappedTrace) ->
    (prefixOccurrences : ActionRegistrationReplayCorrespondence name key world
      error value sourceTrace original) ->
    (leftOrigin : locatedActionOrdinal (replayActionOrigin prefixOccurrences
      (adjacentLeftNodeOccurrence {original = original} {prefixTrace = tracePrefix} {left = left} {right = right} {suffix = suffix} {diamond = diamond} (materializeAdjacentSwapResult {original = original} {tracePrefix = tracePrefix} {left = left} {right = right} {suffix = suffix} {diamond = diamond} replayedFinal
        replayedSuffix swappedTrace originalExact swappedExact external replay
        endpoint premises))) =
      transitionCount (traceBeforeBlock {global = sourceTrace} leftBlock) + leftPosition) ->
    (rightOrigin : locatedActionOrdinal (replayActionOrigin prefixOccurrences
      (adjacentRightNodeOccurrence {original = original} {prefixTrace = tracePrefix} {left = left} {right = right} {suffix = suffix} {diamond = diamond} (materializeAdjacentSwapResult {original = original} {tracePrefix = tracePrefix} {left = left} {right = right} {suffix = suffix} {diamond = diamond} replayedFinal
        replayedSuffix swappedTrace originalExact swappedExact external replay
        endpoint premises))) =
      transitionCount (traceBeforeBlock {global = sourceTrace} rightBlock) + rightPosition) ->
    (target : Transitions initial targetFinal) ->
    (restPositions : List (Nat, Nat)) ->
    (rest : RawOperationalOriginPlan name key world error value protocol nameEq
      keyEq sourceTrace leftBlock rightBlock swappedTrace
      (composeActionRegistrationReplayCorrespondence prefixOccurrences
        (swappedOccurrenceCorrespondence
          (materializeAdjacentSwapResult {original = original} {tracePrefix = tracePrefix} {left = left} {right = right} {suffix = suffix} {diamond = diamond} replayedFinal replayedSuffix swappedTrace
            originalExact swappedExact external replay endpoint premises)))
      target restPositions) ->
    RawOperationalOriginPlan name key world error value protocol nameEq keyEq
      sourceTrace leftBlock rightBlock original prefixOccurrences target
      ((leftPosition, rightPosition) :: restPositions)

public export
record MaterializedOperationalOriginPlan
  (name, key, world, error : Type) (value : key -> Type)
  (protocol : RegistrationProtocol key value world error)
  (nameEq : DecEq name) (keyEq : DecEq key)
  {sourceInitial, sourceFinal : SystemState name key value world error}
  (sourceTrace : Transitions sourceInitial sourceFinal)
  {leftActor, rightActor : name}
  (leftBlock : LocatedOpenEpisodeBlock name key world error value nameEq keyEq
    leftActor sourceTrace)
  (rightBlock : LocatedOpenEpisodeBlock name key world error value nameEq keyEq
    rightActor sourceTrace)
  {currentInitial, currentFinal, targetFinal :
    SystemState name key value world error}
  (current : Transitions currentInitial currentFinal)
  (prefixOccurrences : ActionRegistrationReplayCorrespondence name key world
    error value sourceTrace current)
  (target : Transitions currentInitial targetFinal)
  (positions : List (Nat, Nat)) where
  constructor MkMaterializedOperationalOriginPlan
  materializedDerivation : FiniteAdjacentSwapDerivation name key world error value
    protocol nameEq keyEq current target
  materializedPlan : BlockCrossingOriginPlan name key world error value protocol
    nameEq keyEq sourceTrace leftBlock rightBlock prefixOccurrences
    materializedDerivation positions

public export
0 materializeOperationalOriginPlan :
  (raw : RawOperationalOriginPlan name key world error value protocol nameEq keyEq
    sourceTrace leftBlock rightBlock current prefixOccurrences target positions) ->
  MaterializedOperationalOriginPlan name key world error value protocol nameEq
    keyEq sourceTrace leftBlock rightBlock current prefixOccurrences target positions
materializeOperationalOriginPlan RawOriginDone =
  MkMaterializedOperationalOriginPlan FiniteAdjacentSwapDone
    CrossingOriginPlanDone
materializeOperationalOriginPlan
  (RawOriginStep {replayedFinal} sourceTrace leftBlock rightBlock original tracePrefix left right
    suffix orientation diamond replayedSuffix swappedTrace originalExact
    swappedExact external replay endpoint premises prefixOccurrences leftOrigin
    rightOrigin target restPositions rest) =
  case materializeOperationalOriginPlan rest of
    MkMaterializedOperationalOriginPlan restDerivation restPlan =>
      MkMaterializedOperationalOriginPlan
        (FiniteAdjacentSwapStep original tracePrefix left right suffix orientation
          diamond
          (MkAdjacentSwapResult replayedFinal replayedSuffix swappedTrace
            originalExact swappedExact external replay endpoint premises)
          target restDerivation)
        (CrossingOriginPlanStep original tracePrefix left right suffix orientation
          diamond
          (MkAdjacentSwapResult replayedFinal replayedSuffix swappedTrace
            originalExact swappedExact external replay endpoint premises)
          target restDerivation prefixOccurrences leftBlock rightBlock leftOrigin
          rightOrigin restPositions restPlan)

||| A one-node raw fixture materializes both an actual sealed result and a real
||| `CrossingOriginPlanStep`; no prebuilt result/plan/label is an input.
public export
0 oneByOneMaterializesPlan :
  (raw : RawOperationalOriginPlan name key world error value protocol nameEq keyEq
    sourceTrace leftBlock rightBlock sourceTrace
    (identityActionRegistrationReplayCorrespondence sourceTrace) target
    [(the Nat 0, the Nat 0)]) ->
  MaterializedOperationalOriginPlan name key world error value protocol nameEq
    keyEq sourceTrace leftBlock rightBlock sourceTrace
    (identityActionRegistrationReplayCorrespondence sourceTrace) target
    [(the Nat 0, the Nat 0)]
oneByOneMaterializesPlan = materializeOperationalOriginPlan

public export
0 twoByOneMaterializesPlan :
  (raw : RawOperationalOriginPlan name key world error value protocol nameEq keyEq
    sourceTrace leftBlock rightBlock sourceTrace
    (identityActionRegistrationReplayCorrespondence sourceTrace) target
    [(the Nat 0, the Nat 0), (the Nat 1, the Nat 0)]) ->
  MaterializedOperationalOriginPlan name key world error value protocol nameEq
    keyEq sourceTrace leftBlock rightBlock sourceTrace
    (identityActionRegistrationReplayCorrespondence sourceTrace) target
    [(the Nat 0, the Nat 0), (the Nat 1, the Nat 0)]
twoByOneMaterializesPlan = materializeOperationalOriginPlan

||| Executable predicate that checks every raw crossing node is an Iter/Iter
||| pair.  This is source-sensitive: it refers to the actual transitions stored
||| by each raw step, not merely to a list of action tags.
public export
0 RawPlanIsRepeatedIter :
  RawOperationalOriginPlan name key world error value protocol nameEq keyEq
    sourceTrace leftBlock rightBlock current prefixOccurrences target positions ->
  Type
RawPlanIsRepeatedIter RawOriginDone = Unit
RawPlanIsRepeatedIter
  (RawOriginStep sourceTrace leftBlock rightBlock original tracePrefix left right
    suffix orientation diamond replayedSuffix swappedTrace originalExact
    swappedExact external replay endpoint premises prefixOccurrences leftOrigin
    rightOrigin target restPositions rest) =
      (leftActor : name **
       (transitionAction left = LAdvance leftActor,
        transitionTag left = LIterTag,
        (rightActor : name **
         (transitionAction right = LAdvance rightActor,
          transitionTag right = LIterTag,
          RawPlanIsRepeatedIter rest))))

||| Four raw nodes at the exact 2x2 coordinates materialize four actual sealed
||| results and four `CrossingOriginPlanStep`s.  The additional predicate proves
||| all eight moved/source actions are repeated Iter steps.
public export
0 repeatedIterTwoByTwoMaterializesPlan :
  (raw : RawOperationalOriginPlan name key world error value protocol nameEq keyEq
    sourceTrace leftBlock rightBlock sourceTrace
    (identityActionRegistrationReplayCorrespondence sourceTrace) target
    [(the Nat 0, the Nat 0), (the Nat 0, the Nat 1),
     (the Nat 1, the Nat 0), (the Nat 1, the Nat 1)]) ->
  RawPlanIsRepeatedIter raw ->
  MaterializedOperationalOriginPlan name key world error value protocol nameEq
    keyEq sourceTrace leftBlock rightBlock sourceTrace
    (identityActionRegistrationReplayCorrespondence sourceTrace) target
    [(the Nat 0, the Nat 0), (the Nat 0, the Nat 1),
     (the Nat 1, the Nat 0), (the Nat 1, the Nat 1)]
repeatedIterTwoByTwoMaterializesPlan raw iter =
  materializeOperationalOriginPlan raw
