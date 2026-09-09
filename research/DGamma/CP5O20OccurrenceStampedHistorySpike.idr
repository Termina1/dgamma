module DGamma.CP5O20OccurrenceStampedHistorySpike

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5O20PairedAdvanceSpike
import DGamma.CP5O20StampedHistoryFoldSpike
import DGamma.CP5O20HistoryNameTransportSpike
import DGamma.CP5O20AllNameSynchronizationSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import Decidable.Equality

%default total
%unbound_implicits off

||| The actual LEFT native edge owned by each of the six stamped stages.
||| No check or target is re-executed/reconstructed; use the stage's equation.
public export
0 o20StampedLeftTransition :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {mapping : RegistrationGenerationBijection name} -> {renaming : NameBijection name} ->
  {leftOrdinal, rightOrdinal : Nat} ->
  {leftLive, rightLive, leftNext, rightNext : GenerationEnvironment name} ->
  {leftBefore, rightBefore, leftAfter, rightAfter : SystemState name key value world error} ->
  O20StampedStage name key world error value nameEq keyEq mapping renaming
    leftOrdinal rightOrdinal leftLive rightLive leftNext rightNext
    leftBefore rightBefore leftAfter rightAfter ->
  Transition leftBefore leftAfter
o20StampedLeftTransition
  (StampedBeginStage nameEq keyEq renaming actor leftBefore leftAfter rightBefore rightAfter leftOpening rightOpening pairwise) =
    beginTransition leftOpening
o20StampedLeftTransition
  (StampedAdvanceStage nameEq keyEq renaming actor component step rest leftParent rightParent leftRetired rightRetired leftTable rightTable leftOlder rightOlder leftView rightView leftWorld rightWorld leftRegistry rightRegistry leftAfter rightAfter leftUndo rightUndo leftCapability rightCapability leftTag rightTag leftFound rightFound leftResolved rightResolved leftRun rightRun leftChecked rightChecked) =
    Fired nameEq keyEq (LAdvance actor) leftTag leftChecked
o20StampedLeftTransition
  (StampedEmptyFinishStage nameEq keyEq renaming actor component leftParent rightParent leftRetired rightRetired leftTable rightTable leftOlder rightOlder leftView rightView leftWorld rightWorld leftRegistry rightRegistry leftFound rightFound leftChecked rightChecked) =
    Fired nameEq keyEq (LAdvance actor) LFinishTag leftChecked
o20StampedLeftTransition
  (StampedRetireStage nameEq keyEq renaming actor leftWorld rightWorld leftRegistry rightRegistry leftOld rightOld leftFound rightFound leftChecked rightChecked) =
    Fired nameEq keyEq (ORetire actor) ORetireTag leftChecked
o20StampedLeftTransition
  (StampedInsertStage nameEq keyEq renaming actor component leftParent rightParent parents leftWorld rightWorld leftRegistry rightRegistry leftAbsent rightAbsent leftChecked rightChecked matched) =
    Fired nameEq keyEq (OInsert actor leftParent component) OInsertTag leftChecked
o20StampedLeftTransition
  (StampedRemoveStage nameEq keyEq renaming actor leftUnique rightUnique
    leftWorld rightWorld leftRegistry rightRegistry leftChecked rightChecked) =
    Fired nameEq keyEq (ORemove actor) ORemoveTag leftChecked

||| The actual RIGHT native edge owned by each of the six stamped stages.
||| No check or target is re-executed/reconstructed; use the stage's equation.
public export
0 o20StampedRightTransition :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {mapping : RegistrationGenerationBijection name} -> {renaming : NameBijection name} ->
  {leftOrdinal, rightOrdinal : Nat} ->
  {leftLive, rightLive, leftNext, rightNext : GenerationEnvironment name} ->
  {leftBefore, rightBefore, leftAfter, rightAfter : SystemState name key value world error} ->
  O20StampedStage name key world error value nameEq keyEq mapping renaming
    leftOrdinal rightOrdinal leftLive rightLive leftNext rightNext
    leftBefore rightBefore leftAfter rightAfter ->
  Transition rightBefore rightAfter
o20StampedRightTransition
  (StampedBeginStage nameEq keyEq renaming actor leftBefore leftAfter rightBefore rightAfter leftOpening rightOpening pairwise) =
    beginTransition rightOpening
o20StampedRightTransition
  (StampedAdvanceStage nameEq keyEq renaming actor component step rest leftParent rightParent leftRetired rightRetired leftTable rightTable leftOlder rightOlder leftView rightView leftWorld rightWorld leftRegistry rightRegistry leftAfter rightAfter leftUndo rightUndo leftCapability rightCapability leftTag rightTag leftFound rightFound leftResolved rightResolved leftRun rightRun leftChecked rightChecked) =
    Fired nameEq keyEq (LAdvance (renameForward renaming actor)) rightTag rightChecked
o20StampedRightTransition
  (StampedEmptyFinishStage nameEq keyEq renaming actor component leftParent rightParent leftRetired rightRetired leftTable rightTable leftOlder rightOlder leftView rightView leftWorld rightWorld leftRegistry rightRegistry leftFound rightFound leftChecked rightChecked) =
    Fired nameEq keyEq (LAdvance (renameForward renaming actor)) LFinishTag rightChecked
o20StampedRightTransition
  (StampedRetireStage nameEq keyEq renaming actor leftWorld rightWorld leftRegistry rightRegistry leftOld rightOld leftFound rightFound leftChecked rightChecked) =
    Fired nameEq keyEq (ORetire (renameForward renaming actor)) ORetireTag rightChecked
o20StampedRightTransition
  (StampedInsertStage nameEq keyEq renaming actor component leftParent rightParent parents leftWorld rightWorld leftRegistry rightRegistry leftAbsent rightAbsent leftChecked rightChecked matched) =
    Fired nameEq keyEq (OInsert (renameForward renaming actor) rightParent component) OInsertTag rightChecked
o20StampedRightTransition
  (StampedRemoveStage nameEq keyEq renaming actor leftUnique rightUnique
    leftWorld rightWorld leftRegistry rightRegistry leftChecked rightChecked) =
    Fired nameEq keyEq (ORemove (renameForward renaming actor)) ORemoveTag rightChecked

||| Finite actual paired native path with each stage labelled by TWO genuine
||| supplied-word occurrences (same action/tag and their physical ordinals).
||| Unlike the superseded-candidate lockstep family, these occurrence ordinals
||| need not increment together; A8's o20SynchronizationForwardOrdinalFixed
||| explains why that old restriction is inappropriate for a modulo-map goal.
||| Each insertion still owns its generation-map equation; no successor cut
||| or preservation callback is an input. No original-word equality is claimed.
||| whole-word / per-actor ordering and coverage producer remains to prove; arbitrary skips are NOT asserted to be zero native edges
public export
data O20OccurrenceStampedHistory :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (mapping : RegistrationGenerationBijection name) -> (renaming : NameBijection name) ->
  {wordInitial, leftWordFinal, rightWordFinal : SystemState name key value world error} ->
  (leftWord : Transitions wordInitial leftWordFinal) ->
  (rightWord : Transitions wordInitial rightWordFinal) ->
  (leftLive, rightLive, leftFinalLive, rightFinalLive : GenerationEnvironment name) ->
  (leftBefore, rightBefore, leftAfter, rightAfter : SystemState name key value world error) -> Type where
  OccurrenceHistoryEnd :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {keyEq : DecEq key} ->
    {mapping : RegistrationGenerationBijection name} -> {renaming : NameBijection name} ->
    {wordInitial, leftWordFinal, rightWordFinal : SystemState name key value world error} ->
    {leftWord : Transitions wordInitial leftWordFinal} ->
    {rightWord : Transitions wordInitial rightWordFinal} ->
    {leftLive, rightLive : GenerationEnvironment name} ->
    {left, right : SystemState name key value world error} ->
    O20OccurrenceStampedHistory name key world error value nameEq keyEq mapping renaming
      leftWord rightWord leftLive rightLive leftLive rightLive left right left right
  OccurrenceHistoryMore :
    {name, key, world, error : Type} -> {value : key -> Type} ->
    {nameEq : DecEq name} -> {keyEq : DecEq key} ->
    {mapping : RegistrationGenerationBijection name} -> {renaming : NameBijection name} ->
    {wordInitial, leftWordFinal, rightWordFinal : SystemState name key value world error} ->
    {leftWord : Transitions wordInitial leftWordFinal} ->
    {rightWord : Transitions wordInitial rightWordFinal} ->
    {leftOrdinal, rightOrdinal : Nat} ->
    {leftLive, rightLive, leftNext, rightNext, leftFinalLive, rightFinalLive : GenerationEnvironment name} ->
    {leftBefore, rightBefore, leftMiddle, rightMiddle, leftAfter, rightAfter : SystemState name key value world error} ->
    (0 stage : O20StampedStage name key world error value nameEq keyEq mapping renaming
      leftOrdinal rightOrdinal leftLive rightLive leftNext rightNext
      leftBefore rightBefore leftMiddle rightMiddle) ->
    (0 leftOccurrence : LocatedActionOccurrence (transitionAction (o20StampedLeftTransition stage)) leftWord) ->
    (0 rightOccurrence : LocatedActionOccurrence (transitionAction (o20StampedRightTransition stage)) rightWord) ->
    (0 leftStampExact : (locatedActionOrdinal leftOccurrence = leftOrdinal)) ->
    (0 rightStampExact : (locatedActionOrdinal rightOccurrence = rightOrdinal)) ->
    (0 leftTagExact : (transitionTag (locatedTransition leftOccurrence) = transitionTag (o20StampedLeftTransition stage))) ->
    (0 rightTagExact : (transitionTag (locatedTransition rightOccurrence) = transitionTag (o20StampedRightTransition stage))) ->
    (0 later : O20OccurrenceStampedHistory name key world error value nameEq keyEq mapping renaming
      leftWord rightWord leftNext rightNext leftFinalLive rightFinalLive
      leftMiddle rightMiddle leftAfter rightAfter) ->
    O20OccurrenceStampedHistory name key world error value nameEq keyEq mapping renaming
      leftWord rightWord leftLive rightLive leftFinalLive rightFinalLive
      leftBefore rightBefore leftAfter rightAfter

||| Actual conditional finite fold into the EXISTING O20HistoryCut. Only the
||| INITIAL cut is supplied. Each successor is produced by o20StampedStageCut;
||| differing genuine occurrence labels are related by its insertion map law.
||| A8's ordinal-fixity necessity motivates replacing lockstep labels, not the
||| native runtime laws. This does not produce the synchronization certificate.
||| whole-word / per-actor ordering and coverage producer remains to prove; arbitrary skips are NOT asserted to be zero native edges
export
0 o20OccurrenceStampedHistoryCut :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {mapping : RegistrationGenerationBijection name} -> {renaming : NameBijection name} ->
  {wordInitial, leftWordFinal, rightWordFinal : SystemState name key value world error} ->
  {leftWord : Transitions wordInitial leftWordFinal} ->
  {rightWord : Transitions wordInitial rightWordFinal} ->
  {leftLive, rightLive, leftFinalLive, rightFinalLive : GenerationEnvironment name} ->
  {leftBefore, rightBefore, leftAfter, rightAfter : SystemState name key value world error} ->
  O20OccurrenceStampedHistory name key world error value nameEq keyEq mapping renaming
    leftWord rightWord leftLive rightLive leftFinalLive rightFinalLive
    leftBefore rightBefore leftAfter rightAfter ->
  O20StampedCut name key world error value nameEq mapping renaming
    leftLive rightLive leftBefore rightBefore ->
  O20HistoryCut name key world error value nameEq mapping
    leftFinalLive rightFinalLive leftAfter rightAfter
o20OccurrenceStampedHistoryCut {renaming} OccurrenceHistoryEnd paired =
  MkO20HistoryCut renaming (stampedRuntime paired) (stampedForward paired) (stampedBackward paired)
o20OccurrenceStampedHistoryCut
  (OccurrenceHistoryMore stage leftOccurrence rightOccurrence leftStampExact rightStampExact leftTagExact rightTagExact later) paired =
    o20OccurrenceStampedHistoryCut later (o20StampedStageCut stage paired)

||| Modulo-map endpoint/scanner synchronization SPECIFICATION: actual native
||| paired paths, both genuine supplied-word scans, and occurrence-attached
||| (not lockstep) physical stamps. A8 proves the old candidate forces birth
||| ordinal preservation; this new target does not impose that restriction.
||| This record is not an accepted-input producer or an ALL-name current rebase.
||| whole-word / per-actor ordering and coverage producer remains to prove; arbitrary skips are NOT asserted to be zero native edges
public export
record O20HistorySynchronizationModulo
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key)
  (mapping : RegistrationGenerationBijection name)
  {initial, leftFinal, rightFinal : SystemState name key value world error}
  (leftWord : Transitions initial leftFinal) (rightWord : Transitions initial rightFinal) where
  constructor MkO20HistorySynchronizationModulo
  moduloBijection : NameBijection name
  moduloLeftLive : GenerationEnvironment name
  moduloRightLive : GenerationEnvironment name
  0 moduloLeftScan : GenerationTraceScan nameEq Z [] leftWord
    (transitionCount leftWord) moduloLeftLive
  0 moduloRightScan : GenerationTraceScan nameEq Z [] rightWord
    (transitionCount rightWord) moduloRightLive
  0 moduloStages : O20OccurrenceStampedHistory name key world error value nameEq keyEq
    mapping moduloBijection leftWord rightWord [] [] moduloLeftLive moduloRightLive
    initial initial leftFinal rightFinal

||| SUFFICIENCY of a supplied modulo synchronization for the existing history
||| cut. Its native fold produces every successor; empty-origin control is
||| produced here, so no runtime cut is an extra input. Current-name ALL-name
||| rebasing remains B debt. A8 motivates the replacement, not its inhabitation.
||| whole-word / per-actor ordering and coverage producer remains to prove; arbitrary skips are NOT asserted to be zero native edges
export
0 o20ModuloSynchronizationHistoryCut :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  {leftWord : Transitions initial leftFinal} -> {rightWord : Transitions initial rightFinal} ->
  (mapping : RegistrationGenerationBijection name) ->
  (synchronization : O20HistorySynchronizationModulo name key world error value nameEq keyEq mapping leftWord rightWord) ->
  (bindings (registry initial) = []) ->
  O20HistoryCut name key world error value nameEq mapping
    (moduloLeftLive synchronization) (moduloRightLive synchronization) leftFinal rightFinal
o20ModuloSynchronizationHistoryCut {nameEq} {initial} mapping synchronization empty =
  o20OccurrenceStampedHistoryCut (moduloStages synchronization)
    (MkO20StampedCut
      (o20AllNameEmptyOrigin nameEq (moduloBijection synchronization) initial empty)
      (\selected, stamp, found => absurd found) (\selected, stamp, found => absurd found))

||| The actual LEFT native path contained in an occurrence-stamped history.
||| No equation to the supplied-word trace token is claimed; that word supplies
||| original action/tag/ordinal labels, not a freely asserted replay equality.
export
0 o20OccurrenceHistoryLeftPath :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {mapping : RegistrationGenerationBijection name} -> {renaming : NameBijection name} ->
  {wordInitial, leftWordFinal, rightWordFinal : SystemState name key value world error} ->
  {leftWord : Transitions wordInitial leftWordFinal} ->
  {rightWord : Transitions wordInitial rightWordFinal} ->
  {leftLive, rightLive, leftFinalLive, rightFinalLive : GenerationEnvironment name} ->
  {leftBefore, rightBefore, leftAfter, rightAfter : SystemState name key value world error} ->
  O20OccurrenceStampedHistory name key world error value nameEq keyEq mapping renaming
    leftWord rightWord leftLive rightLive leftFinalLive rightFinalLive
    leftBefore rightBefore leftAfter rightAfter ->
  Transitions leftBefore leftAfter
o20OccurrenceHistoryLeftPath OccurrenceHistoryEnd = NoTransitions
o20OccurrenceHistoryLeftPath
  (OccurrenceHistoryMore stage leftOccurrence rightOccurrence leftStampExact rightStampExact leftTagExact rightTagExact later) =
    MoreTransitions (o20StampedLeftTransition stage) (o20OccurrenceHistoryLeftPath later)

||| The actual RIGHT native path contained in an occurrence-stamped history.
||| No equation to the supplied-word trace token is claimed; that word supplies
||| original action/tag/ordinal labels, not a freely asserted replay equality.
export
0 o20OccurrenceHistoryRightPath :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {mapping : RegistrationGenerationBijection name} -> {renaming : NameBijection name} ->
  {wordInitial, leftWordFinal, rightWordFinal : SystemState name key value world error} ->
  {leftWord : Transitions wordInitial leftWordFinal} ->
  {rightWord : Transitions wordInitial rightWordFinal} ->
  {leftLive, rightLive, leftFinalLive, rightFinalLive : GenerationEnvironment name} ->
  {leftBefore, rightBefore, leftAfter, rightAfter : SystemState name key value world error} ->
  O20OccurrenceStampedHistory name key world error value nameEq keyEq mapping renaming
    leftWord rightWord leftLive rightLive leftFinalLive rightFinalLive
    leftBefore rightBefore leftAfter rightAfter ->
  Transitions rightBefore rightAfter
o20OccurrenceHistoryRightPath OccurrenceHistoryEnd = NoTransitions
o20OccurrenceHistoryRightPath
  (OccurrenceHistoryMore stage leftOccurrence rightOccurrence leftStampExact rightStampExact leftTagExact rightTagExact later) =
    MoreTransitions (o20StampedRightTransition stage) (o20OccurrenceHistoryRightPath later)
