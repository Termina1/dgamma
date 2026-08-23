module DGamma.R11GenericRawPlanRepackagerPositive

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.CP3
import DGamma.Metatheory
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.R9WholeBlockSingletonPositive
import DGamma.R9WholeBlockTwoByOnePositive
import DGamma.R9WholeBlockTwoByTwoPositive
import Data.Nat
import Decidable.Equality

%default total

||| Semantic fields for one operational swap. The recursive family below still
||| accepts a threaded prefix occurrence correspondence and both origin
||| equations; this module is therefore a generic repackager, not a fixture.  The constructor below materializes the actual
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

||| Supplied recursive origin-plan ingredients. Each step explicitly accepts the
||| threaded `prefixOccurrences` map, both source-origin equations, and its
||| recursive tail. The checked functions only repackage those premises into the
||| public result/derivation/plan records.
public export
data SuppliedOriginPlanIngredients :
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
  SuppliedOriginDone :
    SuppliedOriginPlanIngredients name key world error value protocol nameEq keyEq
      sourceTrace leftBlock rightBlock current prefixOccurrences current []
  SuppliedOriginStep :
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
    (rest : SuppliedOriginPlanIngredients name key world error value protocol nameEq
      keyEq sourceTrace leftBlock rightBlock swappedTrace
      (composeActionRegistrationReplayCorrespondence prefixOccurrences
        (swappedOccurrenceCorrespondence
          (materializeAdjacentSwapResult {original = original} {tracePrefix = tracePrefix} {left = left} {right = right} {suffix = suffix} {diamond = diamond} replayedFinal replayedSuffix swappedTrace
            originalExact swappedExact external replay endpoint premises)))
      target restPositions) ->
    SuppliedOriginPlanIngredients name key world error value protocol nameEq keyEq
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
  (raw : SuppliedOriginPlanIngredients name key world error value protocol nameEq keyEq
    sourceTrace leftBlock rightBlock current prefixOccurrences target positions) ->
  MaterializedOperationalOriginPlan name key world error value protocol nameEq
    keyEq sourceTrace leftBlock rightBlock current prefixOccurrences target positions
materializeOperationalOriginPlan SuppliedOriginDone =
  MkMaterializedOperationalOriginPlan FiniteAdjacentSwapDone
    CrossingOriginPlanDone
materializeOperationalOriginPlan
  (SuppliedOriginStep {replayedFinal} sourceTrace leftBlock rightBlock original tracePrefix left right
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

||| Nonempty materialization packages the concrete first result, the tail fold,
||| and the recursive origin plan under one definitional derivation index.
public export
record MaterializedNonEmptyOperationalOriginPlan
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
  {targetFinal : SystemState name key value world error}
  (target : Transitions sourceInitial targetFinal)
  (positions : List (Nat, Nat)) where
  constructor MkMaterializedNonEmptyOperationalOriginPlan
  materializedNonEmptyDerivation : NonEmptyFiniteAdjacentSwapDerivation name key
    world error value protocol nameEq keyEq sourceTrace target
  materializedNonEmptyPlan : BlockCrossingOriginPlan name key world error value
    protocol nameEq keyEq sourceTrace leftBlock rightBlock
    (identityActionRegistrationReplayCorrespondence sourceTrace)
    (nonEmptyToFiniteAdjacentSwapDerivation materializedNonEmptyDerivation)
    positions

public export
0 materializeNonEmptyOperationalOriginPlan :
  (raw : SuppliedOriginPlanIngredients name key world error value protocol nameEq keyEq
    sourceTrace leftBlock rightBlock sourceTrace
    (identityActionRegistrationReplayCorrespondence sourceTrace) target
    (firstPosition :: restPositions)) ->
  MaterializedNonEmptyOperationalOriginPlan name key world error value protocol
    nameEq keyEq sourceTrace leftBlock rightBlock target
    (firstPosition :: restPositions)
materializeNonEmptyOperationalOriginPlan
  (SuppliedOriginStep {replayedFinal} sourceTrace leftBlock rightBlock sourceTrace
    tracePrefix left right suffix orientation diamond replayedSuffix swappedTrace
    originalExact swappedExact external replay endpoint premises _
    leftOrigin rightOrigin target restPositions rest) =
  case materializeOperationalOriginPlan rest of
    MkMaterializedOperationalOriginPlan restDerivation restPlan =>
      MkMaterializedNonEmptyOperationalOriginPlan
        (NonEmptyAdjacentSwap sourceTrace tracePrefix left right suffix orientation
          diamond
          (MkAdjacentSwapResult replayedFinal replayedSuffix swappedTrace
            originalExact swappedExact external replay endpoint premises)
          target restDerivation)
        (CrossingOriginPlanStep sourceTrace tracePrefix left right suffix orientation
          diamond
          (MkAdjacentSwapResult replayedFinal replayedSuffix swappedTrace
            originalExact swappedExact external replay endpoint premises)
          target restDerivation
          (identityActionRegistrationReplayCorrespondence sourceTrace)
          leftBlock rightBlock leftOrigin rightOrigin restPositions restPlan)

||| The 1x1 boundary repackages a supplied recursive plan. It constructs target
||| records but does not prove or construct the supplied origin equations.
public export
0 repackageOneByOneSuppliedPlan :
  (raw : SuppliedOriginPlanIngredients name key world error value protocol nameEq keyEq
    sourceTrace leftBlock rightBlock sourceTrace
    (identityActionRegistrationReplayCorrespondence sourceTrace) target
    [(the Nat 0, the Nat 0)]) ->
  MaterializedOperationalOriginPlan name key world error value protocol nameEq
    keyEq sourceTrace leftBlock rightBlock sourceTrace
    (identityActionRegistrationReplayCorrespondence sourceTrace) target
    [(the Nat 0, the Nat 0)]
repackageOneByOneSuppliedPlan = materializeOperationalOriginPlan

public export
0 repackageTwoByOneSuppliedPlan :
  (raw : SuppliedOriginPlanIngredients name key world error value protocol nameEq keyEq
    sourceTrace leftBlock rightBlock sourceTrace
    (identityActionRegistrationReplayCorrespondence sourceTrace) target
    [(the Nat 0, the Nat 0), (the Nat 1, the Nat 0)]) ->
  MaterializedOperationalOriginPlan name key world error value protocol nameEq
    keyEq sourceTrace leftBlock rightBlock sourceTrace
    (identityActionRegistrationReplayCorrespondence sourceTrace) target
    [(the Nat 0, the Nat 0), (the Nat 1, the Nat 0)]
repackageTwoByOneSuppliedPlan = materializeOperationalOriginPlan

||| Executable predicate that checks every raw crossing node is an Iter/Iter
||| pair.  This is source-sensitive: it refers to the actual transitions stored
||| by each raw step, not merely to a list of action tags.
public export
0 SuppliedPlanIsRepeatedIter :
  SuppliedOriginPlanIngredients name key world error value protocol nameEq keyEq
    sourceTrace leftBlock rightBlock current prefixOccurrences target positions ->
  Type
SuppliedPlanIsRepeatedIter SuppliedOriginDone = Unit
SuppliedPlanIsRepeatedIter
  (SuppliedOriginStep sourceTrace leftBlock rightBlock original tracePrefix left right
    suffix orientation diamond replayedSuffix swappedTrace originalExact
    swappedExact external replay endpoint premises prefixOccurrences leftOrigin
    rightOrigin target restPositions rest) =
      (leftActor : name **
       (transitionAction left = LAdvance leftActor,
        transitionTag left = LIterTag,
        (rightActor : name **
         (transitionAction right = LAdvance rightActor,
          transitionTag right = LIterTag,
          SuppliedPlanIsRepeatedIter rest))))

||| A supplied four-node 2x2 plan is repackaged into target records.  The additional predicate proves
||| all eight moved/source actions are repeated Iter steps.
public export
0 repackageRepeatedIterTwoByTwoSuppliedPlan :
  (raw : SuppliedOriginPlanIngredients name key world error value protocol nameEq keyEq
    sourceTrace leftBlock rightBlock sourceTrace
    (identityActionRegistrationReplayCorrespondence sourceTrace) target
    [(the Nat 0, the Nat 0), (the Nat 0, the Nat 1),
     (the Nat 1, the Nat 0), (the Nat 1, the Nat 1)]) ->
  SuppliedPlanIsRepeatedIter raw ->
  MaterializedOperationalOriginPlan name key world error value protocol nameEq
    keyEq sourceTrace leftBlock rightBlock sourceTrace
    (identityActionRegistrationReplayCorrespondence sourceTrace) target
    [(the Nat 0, the Nat 0), (the Nat 0, the Nat 1),
     (the Nat 1, the Nat 0), (the Nat 1, the Nat 1)]
repackageRepeatedIterTwoByTwoSuppliedPlan raw iter =
  materializeOperationalOriginPlan raw

||| Whole-record constructors from supplied recursive origin-plan ingredients.  These call
||| `MkWholeBlockSwapDerivation` through the checked Cartesian wrappers, but the
||| derivation and origin plan are produced by the materializer above.
public export
0 repackageOneByOneWhole :
  {sourceOrder, targetOrder : List name} ->
  {orderSwap : AdjacentActorOrderSwap name sourceOrder targetOrder} ->
  {sourceBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
    sourceOrder sourceTrace} ->
  {sourcePremises : ReplayInvariantBundle name key world error value protocol
    nameEq keyEq sourceTrace} ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq
    keyEq orderSwap sourceTrace sourceBlocks sourcePremises) ->
  (raw : SuppliedOriginPlanIngredients name key world error value protocol nameEq keyEq
    sourceTrace
    (decomposedBlock sourceBlocks (actorLeft orderSwap)
      (safetyLeftInOrder safety))
    (decomposedBlock sourceBlocks (actorRight orderSwap)
      (safetyRightInOrder safety))
    sourceTrace (identityActionRegistrationReplayCorrespondence sourceTrace)
    targetTrace [(the Nat 0, the Nat 0)]) ->
  actorBlockTransitionCount (decomposedBlock sourceBlocks (actorLeft orderSwap)
    (safetyLeftInOrder safety)) = 1 ->
  actorBlockTransitionCount (decomposedBlock sourceBlocks (actorRight orderSwap)
    (safetyRightInOrder safety)) = 1 ->
  nonEmptyAdjacentSwapNodeCount
    (materializedNonEmptyDerivation
      (materializeNonEmptyOperationalOriginPlan raw)) = 1 ->
  WholeBlockSwapDerivation name key world error value protocol nameEq keyEq
    orderSwap sourceTrace sourceBlocks sourcePremises safety targetTrace
repackageOneByOneWhole safety raw leftOne rightOne oneNode =
  singletonWholeBlockWitness safety
    (materializedNonEmptyDerivation
      (materializeNonEmptyOperationalOriginPlan raw))
    (materializedNonEmptyPlan
      (materializeNonEmptyOperationalOriginPlan raw)) leftOne rightOne oneNode

public export
0 repackageTwoByOneWhole :
  {sourceOrder, targetOrder : List name} ->
  {orderSwap : AdjacentActorOrderSwap name sourceOrder targetOrder} ->
  {sourceBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
    sourceOrder sourceTrace} ->
  {sourcePremises : ReplayInvariantBundle name key world error value protocol
    nameEq keyEq sourceTrace} ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq
    keyEq orderSwap sourceTrace sourceBlocks sourcePremises) ->
  (raw : SuppliedOriginPlanIngredients name key world error value protocol nameEq keyEq
    sourceTrace
    (decomposedBlock sourceBlocks (actorLeft orderSwap)
      (safetyLeftInOrder safety))
    (decomposedBlock sourceBlocks (actorRight orderSwap)
      (safetyRightInOrder safety))
    sourceTrace (identityActionRegistrationReplayCorrespondence sourceTrace)
    targetTrace [(the Nat 0, the Nat 0), (the Nat 1, the Nat 0)]) ->
  actorBlockTransitionCount (decomposedBlock sourceBlocks (actorLeft orderSwap)
    (safetyLeftInOrder safety)) = 2 ->
  actorBlockTransitionCount (decomposedBlock sourceBlocks (actorRight orderSwap)
    (safetyRightInOrder safety)) = 1 ->
  nonEmptyAdjacentSwapNodeCount
    (materializedNonEmptyDerivation
      (materializeNonEmptyOperationalOriginPlan raw)) = 2 ->
  WholeBlockSwapDerivation name key world error value protocol nameEq keyEq
    orderSwap sourceTrace sourceBlocks sourcePremises safety targetTrace
repackageTwoByOneWhole safety raw leftTwo rightOne twoNodes =
  twoByOneWholeBlockWitness safety
    (materializedNonEmptyDerivation
      (materializeNonEmptyOperationalOriginPlan raw))
    (materializedNonEmptyPlan
      (materializeNonEmptyOperationalOriginPlan raw)) leftTwo rightOne twoNodes

public export
0 repackageRepeatedIterTwoByTwoWhole :
  {sourceOrder, targetOrder : List name} ->
  {orderSwap : AdjacentActorOrderSwap name sourceOrder targetOrder} ->
  {sourceBlocks : ActorBlockDecomposition name key world error value nameEq keyEq
    sourceOrder sourceTrace} ->
  {sourcePremises : ReplayInvariantBundle name key world error value protocol
    nameEq keyEq sourceTrace} ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq
    keyEq orderSwap sourceTrace sourceBlocks sourcePremises) ->
  (raw : SuppliedOriginPlanIngredients name key world error value protocol nameEq keyEq
    sourceTrace
    (decomposedBlock sourceBlocks (actorLeft orderSwap)
      (safetyLeftInOrder safety))
    (decomposedBlock sourceBlocks (actorRight orderSwap)
      (safetyRightInOrder safety))
    sourceTrace (identityActionRegistrationReplayCorrespondence sourceTrace)
    targetTrace [(the Nat 0, the Nat 0), (the Nat 0, the Nat 1),
      (the Nat 1, the Nat 0), (the Nat 1, the Nat 1)]) ->
  SuppliedPlanIsRepeatedIter raw ->
  actorBlockTransitionCount (decomposedBlock sourceBlocks (actorLeft orderSwap)
    (safetyLeftInOrder safety)) = 2 ->
  actorBlockTransitionCount (decomposedBlock sourceBlocks (actorRight orderSwap)
    (safetyRightInOrder safety)) = 2 ->
  nonEmptyAdjacentSwapNodeCount
    (materializedNonEmptyDerivation
      (materializeNonEmptyOperationalOriginPlan raw)) = S (S (S (S Z))) ->
  WholeBlockSwapDerivation name key world error value protocol nameEq keyEq
    orderSwap sourceTrace sourceBlocks sourcePremises safety targetTrace
repackageRepeatedIterTwoByTwoWhole safety raw iter leftTwo rightTwo fourNodes =
  twoByTwoWholeBlockWitness safety
    (materializedNonEmptyDerivation
      (materializeNonEmptyOperationalOriginPlan raw))
    (materializedNonEmptyPlan
      (materializeNonEmptyOperationalOriginPlan raw)) leftTwo rightTwo fourNodes
