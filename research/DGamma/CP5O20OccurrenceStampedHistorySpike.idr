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
