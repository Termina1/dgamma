module DGamma.CP5O19ReachedBlocksSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCrossTraceSpike
import DGamma.CP5ConfluenceRankObservationSpike
import DGamma.CP5O19ReplayObservationSpike
import DGamma.CP5O19CartesianCursorSpike
import DGamma.CP5O19CartesianColumnsSpike
import DGamma.CP5O19CartesianNumericSpike
import DGamma.CP5O19OrdinalPlanSpike
import DGamma.CP5O19ActualCartesianSpike
import DGamma.CP5O19GridCertificationSpike
import DGamma.CP5O19WholeBlockSpike
import DGamma.CP5O19CartesianLengthSpike
import DGamma.CP5O19PaperBranchCompletenessSpike
import Data.List
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Extract the actual reached left/suffix cut using the SAME column run's
||| residual word. No source-trace bound is applied to an arbitrary target.
export
0 o19ColumnLeftCut :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} -> {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, sourceFinal, before : SystemState name key value world error} ->
  {source : Transitions initial sourceFinal} -> (earlier : Transitions initial before) ->
  (leftWord, rightWord, suffixWord : List (Action name key value world error)) ->
  (run : O19ColumnRun name key world error value protocol nameEq keyEq source earlier leftWord rightWord suffixWord) ->
  O19WordCut name key world error value leftWord suffixWord (columnRest run)
o19ColumnLeftCut earlier leftWord rightWord suffixWord run =
  o19CutByWord leftWord suffixWord (columnRest run) (columnRestWord run)

||| Authenticate the reached three-spine decomposition with the OWNED cut
||| equation and the OWNED column decomposition. No rebuilt replay equation.
export
0 o19ColumnCutDecomposition :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} -> {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, sourceFinal, before : SystemState name key value world error} ->
  {source : Transitions initial sourceFinal} -> (earlier : Transitions initial before) ->
  (leftWord, rightWord, suffixWord : List (Action name key value world error)) ->
  (run : O19ColumnRun name key world error value protocol nameEq keyEq source earlier leftWord rightWord suffixWord) ->
  (cut : O19WordCut name key world error value leftWord suffixWord (columnRest run)) ->
  (appendTransitions earlier (appendTransitions (columnRight run) (appendTransitions (cutPrefix cut) (cutSuffix cut))) =
    cursorTrace (columnCursor run))
o19ColumnCutDecomposition earlier leftWord rightWord suffixWord run cut =
  trans (cong (\rest => appendTransitions earlier (appendTransitions (columnRight run) rest)) (cutDecomposition cut))
    (columnDecomposition run)

||| Extract all three actual reached alignments from the OWN cursor bundle
||| through its exact decomposition and the SAME left/suffix cut.
export
0 o19ColumnCutAligned :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} -> {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, sourceFinal, before : SystemState name key value world error} ->
  {source : Transitions initial sourceFinal} -> (earlier : Transitions initial before) ->
  (leftWord, rightWord, suffixWord : List (Action name key value world error)) ->
  (run : O19ColumnRun name key world error value protocol nameEq keyEq source earlier leftWord rightWord suffixWord) ->
  (cut : O19WordCut name key world error value leftWord suffixWord (columnRest run)) ->
  (AlignedTransitions name key world error value nameEq keyEq (columnRight run),
   (AlignedTransitions name key world error value nameEq keyEq (cutPrefix cut),
    AlignedTransitions name key world error value nameEq keyEq (cutSuffix cut)))
o19ColumnCutAligned earlier leftWord rightWord suffixWord run cut =
  (fst (alignedAppendSplit (columnRight run) (columnRest run)
    (snd (alignedAppendSplit earlier (appendTransitions (columnRight run) (columnRest run))
      (replace {p = AlignedTransitions name key world error value nameEq keyEq}
        (sym (columnDecomposition run)) (replayAligned (cursorBundle (columnCursor run))))))),
   alignedAppendSplit (cutPrefix cut) (cutSuffix cut)
     (replace {p = AlignedTransitions name key world error value nameEq keyEq} (sym (cutDecomposition cut))
       (snd (alignedAppendSplit (columnRight run) (columnRest run)
         (snd (alignedAppendSplit earlier (appendTransitions (columnRight run) (columnRest run))
           (replace {p = AlignedTransitions name key world error value nameEq keyEq}
             (sym (columnDecomposition run)) (replayAligned (cursorBundle (columnCursor run))))))))))

||| Count the ACTUAL reached ranges and full trace. Full length uses the
||| sealed-suffix finite-chain theorem; cut counts use owned word equations.
export
0 o19ColumnRangeCounts :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {protocol : RegistrationProtocol key value world error} -> {nameEq : DecEq name} -> {keyEq : DecEq key} ->
  {initial, sourceFinal, before : SystemState name key value world error} ->
  {source : Transitions initial sourceFinal} -> (earlier : Transitions initial before) ->
  (leftWord, rightWord, suffixWord : List (Action name key value world error)) ->
  (run : O19ColumnRun name key world error value protocol nameEq keyEq source earlier leftWord rightWord suffixWord) ->
  (cut : O19WordCut name key world error value leftWord suffixWord (columnRest run)) ->
  ((transitionCount (columnRight run) = length rightWord),
   ((transitionCount (cutPrefix cut) = length leftWord),
    ((transitionCount (cutSuffix cut) = length suffixWord),
     (transitionCount (cursorTrace (columnCursor run)) = transitionCount source))))
o19ColumnRangeCounts earlier leftWord rightWord suffixWord run cut =
  (trans (sym (o19ActionWordLength (columnRight run))) (cong length (columnRightWord run)),
   (cutLeftCount cut,
    (trans (sym (o19ActionWordLength (cutSuffix cut))) (cong length (cutRightWord cut)),
     o19FiniteTraceCount (cursorDerivation (columnCursor run)))))

||| Actual Begin/body range. The canonical Begin transition equals the
||| reached head in the owned decomposition; installedness is proved later.
public export
record O19BeginRange
  (name, key, world, error : Type) (value : key -> Type)
  (nameEq : DecEq name) (keyEq : DecEq key) (selected : name)
  {first, last : SystemState name key value world error}
  (trace : Transitions first last)
  (bodyWord : List (Action name key value world error)) where
  constructor MkO19BeginRange
  rangeStart : SystemState name key value world error
  rangeOpening : BeginStep nameEq keyEq selected first rangeStart
  rangeBody : Transitions rangeStart last
  0 rangeBodyWord : (o19ActionWord rangeBody = bodyWord)
  0 rangeBodyAligned : AlignedTransitions name key world error value nameEq keyEq rangeBody
  0 rangeDecomposition : (MoreTransitions (beginTransition rangeOpening) rangeBody = trace)

||| One explicit checked Begin head, normalized by its ACTUAL rule tag.
export
0 o19BeginRangeTag :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {first, middle, last : SystemState name key value world error} ->
  (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} (LBegin selected) first = Just (tag, middle)) ->
  (rest : Transitions middle last) -> (bodyWord : List (Action name key value world error)) ->
  AlignedTransitions name key world error value nameEq keyEq rest ->
  (o19ActionWord rest = bodyWord) -> (tag = LBeginTag) ->
  O19BeginRange name key world error value nameEq keyEq selected
    (MoreTransitions (Fired {before = first} {afterState = middle} nameEq keyEq (LBegin selected) tag checked) rest) bodyWord
o19BeginRangeTag {middle} nameEq keyEq selected _ checked rest bodyWord aligned wordExact Refl =
  MkO19BeginRange middle (MkBeginStep checked) rest wordExact aligned Refl

||| One action-equality elimination identifies the ACTUAL reached Begin;
||| its rule tag is derived from checked evaluation, never assumed.
export
0 o19BeginRangeHead :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {first, middle, last : SystemState name key value world error} ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action first = Just (tag, middle)) ->
  (rest : Transitions middle last) -> (bodyWord : List (Action name key value world error)) ->
  AlignedTransitions name key world error value nameEq keyEq rest ->
  (o19ActionWord rest = bodyWord) -> (action = LBegin selected) ->
  O19BeginRange name key world error value nameEq keyEq selected
    (MoreTransitions (Fired {before = first} {afterState = middle} nameEq keyEq action tag checked) rest) bodyWord
o19BeginRangeHead {first} {middle} nameEq keyEq selected _ tag checked rest bodyWord aligned wordExact Refl =
  o19BeginRangeTag nameEq keyEq selected tag checked rest bodyWord aligned wordExact
    (fst (lBeginBoundary nameEq keyEq selected first middle tag checked))

||| The actual aligned range and its exact Begin-headed word produce its
||| own opening/body package. Only one explicit aligned spine is eliminated.
export
0 o19BeginRangeObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {first, last : SystemState name key value world error} ->
  (trace : Transitions first last) -> (bodyWord : List (Action name key value world error)) ->
  AlignedTransitions name key world error value nameEq keyEq trace ->
  (o19ActionWord trace = LBegin selected :: bodyWord) ->
  O19BeginRange name key world error value nameEq keyEq selected trace bodyWord
o19BeginRangeObserved nameEq keyEq selected _ bodyWord AlignedEnd wordExact = void (uninhabited (cong length wordExact))
o19BeginRangeObserved nameEq keyEq selected _ bodyWord (AlignedStep action tag checked rest aligned) wordExact =
  o19BeginRangeHead nameEq keyEq selected action tag checked rest bodyWord aligned
    (snd (consInjective wordExact)) (fst (consInjective wordExact))

||| Installedness survives a checked step unless it is the selected Unload.
||| Consume the actual four-way installation observation, not paper labels.
export
0 o19InstalledNoUnloadEvolution :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  (before, afterState : SystemState name key value world error) ->
  (action : Action name key value world error) -> (tag : RuleTag) ->
  (checked : checkedApplyAction @{nameEq} @{keyEq} action before = Just (tag, afterState)) ->
  (installedAt {name} {key} {value} {world} {error} @{nameEq} selected before = True) ->
  Not (action = LUnload selected) ->
  InstallationEvolution name key world error value nameEq keyEq selected before afterState action tag ->
  (installedAt {name} {key} {value} {world} {error} @{nameEq} selected afterState = True)
o19InstalledNoUnloadEvolution nameEq keyEq selected before afterState _ _ checked atStart excluded
  (RemainedUninstalled notInstalled atEnd) = void (uninhabited (trans (sym notInstalled) atStart))
o19InstalledNoUnloadEvolution nameEq keyEq selected before afterState _ _ checked atStart excluded
  (RemainedInstalled installed atEnd) = atEnd
o19InstalledNoUnloadEvolution nameEq keyEq selected before afterState _ _ checked atStart excluded
  OpenedInstallation = snd (snd (lBeginBoundary nameEq keyEq selected before afterState LBeginTag checked))
o19InstalledNoUnloadEvolution nameEq keyEq selected before afterState _ _ checked atStart excluded
  ClosedInstallation = void (excluded Refl)

||| Construct installedness at EVERY reached cut by the aligned trace's
||| own steps and actual installation observations. No arbitrary source bound.
export
0 o19InstalledNoUnloadTrace :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {first, last : SystemState name key value world error} ->
  (trace : Transitions first last) -> AlignedTransitions name key world error value nameEq keyEq trace ->
  NoParentUnload selected trace ->
  (installedAt {name} {key} {value} {world} {error} @{nameEq} selected first = True) ->
  InstalledTrace name key world error value nameEq keyEq selected trace
o19InstalledNoUnloadTrace nameEq keyEq selected _ AlignedEnd noUnload atStart = InstalledEnd atStart
o19InstalledNoUnloadTrace {first} nameEq keyEq selected _
  (AlignedStep {middle} action tag checked rest aligned) noUnload atStart =
    InstalledStep action tag checked rest atStart
      (o19InstalledNoUnloadTrace nameEq keyEq selected rest aligned
        (snd (o19NoUnloadAtCut selected NoTransitions (Fired nameEq keyEq action tag checked) rest noUnload))
        (o19InstalledNoUnloadEvolution nameEq keyEq selected first middle action tag checked atStart
          (fst (o19NoUnloadAtCut selected NoTransitions (Fired nameEq keyEq action tag checked) rest noUnload))
          (installationEvolutionStep nameEq keyEq selected action tag first middle checked)))

||| Negative Unload evidence transports through genuine located occurrence
||| origins. This is NOT action-word equality mistaken for correspondence.
||| Only the reached trace spine is eliminated; every source cut is owned by
||| its actual origin package and authenticated decomposition.
export
0 o19NoUnloadFromOrigins :
  {name, key, world, error : Type} -> {value : key -> Type} -> (selected : name) ->
  {sourceFirst, sourceLast, targetFirst, targetLast : SystemState name key value world error} ->
  (source : Transitions sourceFirst sourceLast) -> (target : Transitions targetFirst targetLast) ->
  ({action : Action name key value world error} -> LocatedActionOccurrence action target -> LocatedActionOccurrence action source) ->
  NoParentUnload selected source -> NoParentUnload selected target
o19NoUnloadFromOrigins selected source NoTransitions origins noUnload = NoParentUnloadEnd
o19NoUnloadFromOrigins {targetFirst} selected source (MoreTransitions {middle} step rest) origins noUnload =
  NoParentUnloadStep step rest
    (\same => fst (o19NoUnloadAtCut selected
      (beforeActionOccurrence (origins (MkLocatedActionOccurrence targetFirst middle NoTransitions step rest Refl Refl)))
      (locatedTransition (origins (MkLocatedActionOccurrence targetFirst middle NoTransitions step rest Refl Refl)))
      (afterActionOccurrence (origins (MkLocatedActionOccurrence targetFirst middle NoTransitions step rest Refl Refl)))
      (replace {p = NoParentUnload selected}
        (sym (actionOccurrenceDecomposition (origins (MkLocatedActionOccurrence targetFirst middle NoTransitions step rest Refl Refl)))) noUnload))
      (trans (locatedAction (origins (MkLocatedActionOccurrence targetFirst middle NoTransitions step rest Refl Refl))) same))
    (o19NoUnloadFromOrigins selected source rest
      (\occurrence => origins (MkLocatedActionOccurrence (actionBeforeState occurrence) (actionAfterState occurrence)
        (MoreTransitions step (beforeActionOccurrence occurrence)) (locatedTransition occurrence) (afterActionOccurrence occurrence)
        (locatedAction occurrence) (cong (MoreTransitions step) (actionOccurrenceDecomposition occurrence)))) noUnload)

||| Split no-Unload at an ACTUAL dependent append cut. One earlier spine
||| is inspected; the matching evidence is observed by the existing cut lemma.
export
0 o19NoUnloadAppendSplit :
  {name, key, world, error : Type} -> {value : key -> Type} -> (selected : name) ->
  {first, middle, last : SystemState name key value world error} ->
  (earlier : Transitions first middle) -> (later : Transitions middle last) ->
  NoParentUnload selected (appendTransitions earlier later) ->
  (NoParentUnload selected earlier, NoParentUnload selected later)
o19NoUnloadAppendSplit selected NoTransitions later noUnload = (NoParentUnloadEnd, noUnload)
o19NoUnloadAppendSplit selected (MoreTransitions step rest) later noUnload =
  (NoParentUnloadStep step rest
    (fst (o19NoUnloadAtCut selected NoTransitions step (appendTransitions rest later) noUnload))
    (fst (o19NoUnloadAppendSplit selected rest later
      (snd (o19NoUnloadAtCut selected NoTransitions step (appendTransitions rest later) noUnload)))),
   snd (o19NoUnloadAppendSplit selected rest later
     (snd (o19NoUnloadAtCut selected NoTransitions step (appendTransitions rest later) noUnload))))

||| The actual reached Begin establishes installedness; actual no-Unload
||| and alignment construct the entire reached body as an InstalledTrace.
export
0 o19BeginRangeInstalled :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {first, last : SystemState name key value world error} ->
  (trace : Transitions first last) -> (bodyWord : List (Action name key value world error)) ->
  (range : O19BeginRange name key world error value nameEq keyEq selected trace bodyWord) ->
  NoParentUnload selected trace ->
  InstalledTrace name key world error value nameEq keyEq selected (rangeBody range)
o19BeginRangeInstalled {first} nameEq keyEq selected trace bodyWord range noUnload =
  o19InstalledNoUnloadTrace nameEq keyEq selected (rangeBody range) (rangeBodyAligned range)
    (snd (o19NoUnloadAtCut selected NoTransitions (beginTransition (rangeOpening range)) (rangeBody range)
      (replace {p = NoParentUnload selected} (sym (rangeDecomposition range)) noUnload)))
    (snd (snd (lBeginBoundary nameEq keyEq selected first (rangeStart range) LBeginTag (beginEquation (rangeOpening range)))))

||| ACTUAL reached right Begin/body range, from original O19 inputs only.
||| Its trace, word and alignment all come from the SAME column run.
export
0 o19ActualRightBeginRange :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal : SystemState name key value world error} -> (source : Transitions initial sourceFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
  O19BeginRange name key world error value nameEq keyEq (actorRight swap)
    (columnRight (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)) (o19ActionWord (blockBody (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety))))
o19ActualRightBeginRange nameEq keyEq protocol swap source blocks premises safety unique =
  o19BeginRangeObserved nameEq keyEq (actorRight swap)
    (columnRight (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)) (o19ActionWord (blockBody (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety))))
    (fst (o19ColumnCutAligned (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))) (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19ActionWord (traceAfterBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique) (o19ColumnLeftCut (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))) (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19ActionWord (traceAfterBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)))) (columnRightWord (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique))
