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
import DGamma.CP5O19OriginalBlockClassSpike
import DGamma.CP5O19AdjacentReplayProducerSpike
import DGamma.CP5O19SameChainAssemblySpike
import Data.List
import Data.List.Elem
import Data.List.HasLength as HL
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

||| ACTUAL reached left Begin/body range from the SAME produced left cut.
||| The body word identifies the original block; its actual alignment is owned.
export
0 o19ActualLeftBeginRange :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal : SystemState name key value world error} -> (source : Transitions initial sourceFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
  O19BeginRange name key world error value nameEq keyEq (actorLeft swap)
    (cutPrefix (o19ColumnLeftCut (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))) (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19ActionWord (traceAfterBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique))) (o19ActionWord (blockBody (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))))
o19ActualLeftBeginRange nameEq keyEq protocol swap source blocks premises safety unique =
  o19BeginRangeObserved nameEq keyEq (actorLeft swap)
    (cutPrefix (o19ColumnLeftCut (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))) (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19ActionWord (traceAfterBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique))) (o19ActionWord (blockBody (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))))
    (fst (snd (o19ColumnCutAligned (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))) (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19ActionWord (traceAfterBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique) (o19ColumnLeftCut (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))) (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19ActionWord (traceAfterBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique))))) (cutLeftWord (o19ColumnLeftCut (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))) (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19ActionWord (traceAfterBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)))

||| BOTH ACTUAL moved bodies are installed at every reached cut. Negative
||| Unload evidence follows the SAME finite derivation occurrence map, then
||| the OWN reached column/cut/range decompositions. No source-bound shortcut
||| or action-word correspondence is used to assert reached installedness.
export
0 o19ActualMovedBodiesInstalled :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal : SystemState name key value world error} -> (source : Transitions initial sourceFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
  (InstalledTrace name key world error value nameEq keyEq (actorRight swap) (rangeBody (o19ActualRightBeginRange nameEq keyEq protocol swap source blocks premises safety unique)),
   InstalledTrace name key world error value nameEq keyEq (actorLeft swap) (rangeBody (o19ActualLeftBeginRange nameEq keyEq protocol swap source blocks premises safety unique)))
o19ActualMovedBodiesInstalled nameEq keyEq protocol swap source blocks premises safety unique =
  (o19BeginRangeInstalled nameEq keyEq (actorRight swap)
    (columnRight (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)) (o19ActionWord (blockBody (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19ActualRightBeginRange nameEq keyEq protocol swap source blocks premises safety unique)
    (fst (o19NoUnloadAppendSplit (actorRight swap) (columnRight (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)) (columnRest (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)) (snd (o19NoUnloadAppendSplit (actorRight swap) (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))) (appendTransitions (columnRight (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)) (columnRest (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)))
        (replace {p = NoParentUnload (actorRight swap)} (sym (columnDecomposition (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique))) (o19NoUnloadFromOrigins (actorRight swap) source (cursorTrace (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)))
          (\occurrence => replayActionOrigin (finiteDerivationOccurrenceCorrespondence (cursorDerivation (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)))) occurrence)
          (o19OriginalBlockNoUnload nameEq keyEq (actorRight swap) source (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety))))))))),
   o19BeginRangeInstalled nameEq keyEq (actorLeft swap)
    (cutPrefix (o19ColumnLeftCut (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))) (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19ActionWord (traceAfterBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique))) (o19ActionWord (blockBody (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) (o19ActualLeftBeginRange nameEq keyEq protocol swap source blocks premises safety unique)
    (fst (o19NoUnloadAppendSplit (actorLeft swap) (cutPrefix (o19ColumnLeftCut (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))) (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19ActionWord (traceAfterBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique))) (cutSuffix (o19ColumnLeftCut (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))) (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19ActionWord (traceAfterBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)))
      (replace {p = NoParentUnload (actorLeft swap)} (sym (cutDecomposition (o19ColumnLeftCut (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))) (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19ActionWord (traceAfterBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique))))
        (snd (o19NoUnloadAppendSplit (actorLeft swap) (columnRight (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)) (columnRest (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)) (snd (o19NoUnloadAppendSplit (actorLeft swap) (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))) (appendTransitions (columnRight (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)) (columnRest (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)))
        (replace {p = NoParentUnload (actorLeft swap)} (sym (columnDecomposition (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique))) (o19NoUnloadFromOrigins (actorLeft swap) source (cursorTrace (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)))
          (\occurrence => replayActionOrigin (finiteDerivationOccurrenceCorrespondence (cursorDerivation (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)))) occurrence)
          (o19OriginalBlockNoUnload nameEq keyEq (actorLeft swap) source (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))))))))))))

||| C2 extension: consume one original word observation for the ACTUAL
||| reached head. Lifecycle ownership and yielded registration are retained.
export
0 o19ActorOnlyPrependObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (selected, forbidden : name) ->
  {first, middle, last : SystemState name key value world error} ->
  (step : Transition first middle) -> (rest : Transitions middle last) ->
  ActorLifecycleOnly selected rest ->
  O19BlockWordObservation name key world error value selected forbidden (transitionAction step) ->
  ActorLifecycleOnly selected (MoreTransitions step rest)
o19ActorOnlyPrependObserved selected forbidden step rest tail (BlockOwnLifecycle lifecycle owner) =
  ActorLifecycleStep step rest lifecycle (trans (o19TransitionActorOwner step) owner) tail
o19ActorOnlyPrependObserved selected forbidden step rest tail (BlockGenerated child component inserted safe) =
  ActorYieldedRegistrationStep step rest inserted tail

||| Fold actual reached heads using bounded word observations. A caller's
||| classifier is an internal boundary; original blocks supply it at assembly.
export
0 o19ActorOnlyFromWord :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (selected, forbidden : name) ->
  {first, last : SystemState name key value world error} ->
  (trace : Transitions first last) ->
  ((action : Action name key value world error) -> Elem action (o19ActionWord trace) ->
    O19BlockWordObservation name key world error value selected forbidden action) ->
  ActorLifecycleOnly selected trace
o19ActorOnlyFromWord selected forbidden NoTransitions observations = ActorLifecycleEnd
o19ActorOnlyFromWord selected forbidden (MoreTransitions step rest) observations =
  o19ActorOnlyPrependObserved selected forbidden step rest
    (o19ActorOnlyFromWord selected forbidden rest (\action, member => observations action (There member)))
    (observations (transitionAction step) Here)

||| NoLifecycleBy excludes every lifecycle label in its ACTUAL action word.
||| This predicate will transport along authenticated outside-range words.
export
0 o19NoLifecycleWordMember :
  {name, key, world, error : Type} -> {value : key -> Type} -> (selected : name) ->
  {first, last : SystemState name key value world error} ->
  (trace : Transitions first last) -> NoLifecycleBy selected trace ->
  (action : Action name key value world error) -> Elem action (o19ActionWord trace) ->
  (isLifecycleAction action = True) -> Not (actionOwner action = selected)
o19NoLifecycleWordMember selected _ NoLifecycleByEnd action member lifecycle owner = void (uninhabited member)
o19NoLifecycleWordMember selected _ (NoLifecycleByStep step rest excluded tail) _ Here lifecycle owner =
  excluded lifecycle (trans (o19TransitionActorOwner step) owner)
o19NoLifecycleWordMember selected _ (NoLifecycleByStep step rest excluded tail) action (There member) lifecycle owner =
  o19NoLifecycleWordMember selected rest tail action member lifecycle owner

||| Build NoLifecycleBy on the ACTUAL target segment from its word-member
||| exclusions. This does not assert state/occurrence correspondence.
export
0 o19NoLifecycleFromWord :
  {name, key, world, error : Type} -> {value : key -> Type} -> (selected : name) ->
  {first, last : SystemState name key value world error} ->
  (trace : Transitions first last) ->
  ((action : Action name key value world error) -> Elem action (o19ActionWord trace) ->
    (isLifecycleAction action = True) -> Not (actionOwner action = selected)) ->
  NoLifecycleBy selected trace
o19NoLifecycleFromWord selected NoTransitions excluded = NoLifecycleByEnd
o19NoLifecycleFromWord selected (MoreTransitions step rest) excluded =
  NoLifecycleByStep step rest
    (\lifecycle, owner => excluded (transitionAction step) Here lifecycle (trans (sym (o19TransitionActorOwner step)) owner))
    (o19NoLifecycleFromWord selected rest (\action, member => excluded action (There member)))

||| Isolate the single lifecycle-control elimination. The lookup observer
||| consumes this top-level law instead of nesting lifecycle case analysis.
export
0 o19LifecycleControlActiveSame :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {deps : List key} -> {provision : CoeffectSpec key} ->
  {left, right : Lifecycle key value world error name deps provision} ->
  LifecycleControlRelated left right -> (isActive left = isActive right)
o19LifecycleControlActiveSame (InactiveControls outcomes) = Refl
o19LifecycleControlActiveSame (ReloadingControls remaining accumulator view) = Refl
o19LifecycleControlActiveSame (ActiveControls accumulator view) = Refl
o19LifecycleControlActiveSame (UnloadingControls accumulator view outcome) = Refl

||| Explicit observed lookups plus the actual pointwise control relation
||| preserve active truth. No lookup case is taken on a computed existential.
export
0 o19SupportedActiveObserved :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (selected : name) ->
  (source, target : SystemState name key value world error) ->
  (sourceFiber, targetFiber : Maybe (Fiber name key value world error)) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry source) = sourceFiber) ->
  (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry target) = targetFiber) ->
  FiberControlMaybeRelated sourceFiber targetFiber ->
  (supportedActiveAt {name} {key} {value} {world} {error} @{nameEq} selected source =
    supportedActiveAt {name} {key} {value} {world} {error} @{nameEq} selected target)
o19SupportedActiveObserved nameEq selected source target _ _ sourceFound targetFound NoControlFibers =
  rewrite sourceFound in rewrite targetFound in Refl
o19SupportedActiveObserved nameEq selected source target _ _ sourceFound targetFound
  (SomeControlFibers (FibersControlRelated lp rp lr rr lt rt leftLifecycle rightLifecycle parents retired lifecycle)) =
    rewrite sourceFound in rewrite targetFound in o19LifecycleControlActiveSame lifecycle

||| Preserve source-final active truth at the SAME actual reached endpoint.
||| This consumes D1 on its real chain, never a detached endpoint assertion.
export
0 o19ActualFinalActive :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal : SystemState name key value world error} -> (source : Transitions initial sourceFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
  (selected : name) ->
  (supportedActiveAt {name} {key} {value} {world} {error} @{nameEq} selected sourceFinal = True) ->
  (supportedActiveAt {name} {key} {value} {world} {error} @{nameEq} selected (cursorFinal (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique))) = True)
o19ActualFinalActive {sourceFinal} nameEq keyEq protocol swap source blocks premises safety unique selected active =
  trans (sym (o19SupportedActiveObserved nameEq selected sourceFinal (cursorFinal (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)))
    (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry sourceFinal))
    (lookupFiber {name} {key} {value} {world} {error} @{nameEq} selected (registry (cursorFinal (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique))))) Refl Refl
    (controlPointwise (replayedControls (o19FiniteEndpoint nameEq keyEq (cursorDerivation (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique))) (replayFinalWellFormed premises))) selected))) active

||| Cancel one common final action from explicit words. Impossible unequal
||| empty/nonempty cases use exact append lengths, not action decidability.
export
0 o19SnocInjective : {item : Type} -> (first, second : List item) -> (last : item) ->
  (first ++ [last] = second ++ [last]) -> (first = second)
o19SnocInjective [] [] last exact = Refl
o19SnocInjective [] (head :: rest) last exact =
  void (uninhabited (trans (cong length exact)
    (cong S (trans (HL.hasLengthUnique (HL.hasLength (rest ++ [last])) (HL.hasLengthAppend (HL.hasLength rest) (HL.hasLength [last]))) (plusCommutative (length rest) 1)))))
o19SnocInjective (head :: rest) [] last exact =
  void (uninhabited (trans (cong length (sym exact))
    (cong S (trans (HL.hasLengthUnique (HL.hasLength (rest ++ [last])) (HL.hasLengthAppend (HL.hasLength rest) (HL.hasLength [last]))) (plusCommutative (length rest) 1)))))
o19SnocInjective (first :: firstRest) (second :: secondRest) last exact =
  cong2 (::) (fst (consInjective exact)) (o19SnocInjective firstRest secondRest last (snd (consInjective exact)))

||| Authenticate the ORIGINAL right-before word from BlockBefore's exact
||| opening-prefix equation. Cancelling its actual final Begin is sound for
||| arbitrary words, including repeated lifecycle action labels.
export
0 o19OrderedBeforeWord :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {leftActor, rightActor : name} ->
  {initial, finalState : SystemState name key value world error} -> {source : Transitions initial finalState} ->
  (leftBlock : LocatedOpenEpisodeBlock name key world error value nameEq keyEq leftActor source) ->
  (rightBlock : LocatedOpenEpisodeBlock name key world error value nameEq keyEq rightActor source) ->
  (ordered : BlockBefore name key world error value nameEq keyEq source leftActor rightActor leftBlock rightBlock) ->
  (o19ActionWord (traceBeforeBlock rightBlock) = o19ActionWord (prefixThroughBlock leftBlock) ++ o19ActionWord (betweenBlocks ordered))
o19OrderedBeforeWord {rightActor} leftBlock rightBlock ordered =
  o19SnocInjective (o19ActionWord (traceBeforeBlock rightBlock))
    (o19ActionWord (prefixThroughBlock leftBlock) ++ o19ActionWord (betweenBlocks ordered)) (LBegin rightActor)
    (trans (sym (o19ActionWordAppend (traceBeforeBlock rightBlock) (MoreTransitions (beginTransition (blockOpening rightBlock)) NoTransitions)))
      (trans (cong o19ActionWord (blocksOrderedInGlobal ordered))
        (trans (o19ActionWordAppend (prefixThroughBlock leftBlock)
          (appendTransitions (betweenBlocks ordered) (MoreTransitions (beginTransition (blockOpening rightBlock)) NoTransitions)))
          (trans (cong (o19ActionWord (prefixThroughBlock leftBlock) ++)
            (o19ActionWordAppend (betweenBlocks ordered) (MoreTransitions (beginTransition (blockOpening rightBlock)) NoTransitions)))
            (appendAssociative (o19ActionWord (prefixThroughBlock leftBlock)) (o19ActionWord (betweenBlocks ordered)) [LBegin rightActor])))))

||| Cancel a common explicit leading word, without deciding any action label.
export
0 o19AppendLeftInjective : {item : Type} -> (leading, first, second : List item) ->
  (leading ++ first = leading ++ second) -> (first = second)
o19AppendLeftInjective [] first second exact = exact
o19AppendLeftInjective (head :: rest) first second exact =
  o19AppendLeftInjective rest first second (snd (consInjective exact))

||| Authenticate the ORIGINAL after-left word as the actual gap/right/after
||| word. Both source decompositions are used; no arbitrary suffix is assumed.
export
0 o19OrderedAfterWord :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {leftActor, rightActor : name} ->
  {initial, finalState : SystemState name key value world error} -> {source : Transitions initial finalState} ->
  (leftBlock : LocatedOpenEpisodeBlock name key world error value nameEq keyEq leftActor source) ->
  (rightBlock : LocatedOpenEpisodeBlock name key world error value nameEq keyEq rightActor source) ->
  (ordered : BlockBefore name key world error value nameEq keyEq source leftActor rightActor leftBlock rightBlock) ->
  (o19ActionWord (traceAfterBlock leftBlock) = o19ActionWord (betweenBlocks ordered) ++
    (o19ActionWord (actorBlockTrace rightBlock) ++ o19ActionWord (traceAfterBlock rightBlock)))
o19OrderedAfterWord leftBlock rightBlock ordered =
  o19AppendLeftInjective (o19ActionWord (actorBlockTrace leftBlock)) (o19ActionWord (traceAfterBlock leftBlock))
    (o19ActionWord (betweenBlocks ordered) ++ (o19ActionWord (actorBlockTrace rightBlock) ++ o19ActionWord (traceAfterBlock rightBlock)))
    (o19AppendLeftInjective (o19ActionWord (traceBeforeBlock leftBlock))
      (o19ActionWord (actorBlockTrace leftBlock) ++ o19ActionWord (traceAfterBlock leftBlock))
      (o19ActionWord (actorBlockTrace leftBlock) ++ (o19ActionWord (betweenBlocks ordered) ++
        (o19ActionWord (actorBlockTrace rightBlock) ++ o19ActionWord (traceAfterBlock rightBlock))))
      (trans (cong (o19ActionWord (traceBeforeBlock leftBlock) ++)
        (sym (o19ActionWordAppend (actorBlockTrace leftBlock) (traceAfterBlock leftBlock))))
      (trans (sym (o19ActionWordAppend (traceBeforeBlock leftBlock) (appendTransitions (actorBlockTrace leftBlock) (traceAfterBlock leftBlock))))
      (trans (cong o19ActionWord (blockDecomposition leftBlock))
      (trans (sym (cong o19ActionWord (o19ActualBlockSpines leftBlock rightBlock ordered)))
      (trans (o19ActionWordAppend (traceBeforeBlock leftBlock)
        (appendTransitions (actorBlockTrace leftBlock) (appendTransitions (betweenBlocks ordered) (appendTransitions (actorBlockTrace rightBlock) (traceAfterBlock rightBlock)))))
        (cong (o19ActionWord (traceBeforeBlock leftBlock) ++)
          (trans (o19ActionWordAppend (actorBlockTrace leftBlock)
            (appendTransitions (betweenBlocks ordered) (appendTransitions (actorBlockTrace rightBlock) (traceAfterBlock rightBlock))))
            (cong (o19ActionWord (actorBlockTrace leftBlock) ++)
              (trans (o19ActionWordAppend (betweenBlocks ordered) (appendTransitions (actorBlockTrace rightBlock) (traceAfterBlock rightBlock)))
                (cong (o19ActionWord (betweenBlocks ordered) ++)
                  (o19ActionWordAppend (actorBlockTrace rightBlock) (traceAfterBlock rightBlock)))))))))))))

||| Cross-actor outer exclusions are DERIVED from the original ordered
||| source words, not supplied as extra O19 safety assumptions.
export
0 o19OrderedOuterNoLifecycle :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {leftActor, rightActor : name} ->
  {initial, finalState : SystemState name key value world error} -> {source : Transitions initial finalState} ->
  (leftBlock : LocatedOpenEpisodeBlock name key world error value nameEq keyEq leftActor source) ->
  (rightBlock : LocatedOpenEpisodeBlock name key world error value nameEq keyEq rightActor source) ->
  (ordered : BlockBefore name key world error value nameEq keyEq source leftActor rightActor leftBlock rightBlock) ->
  (NoLifecycleBy rightActor (traceBeforeBlock leftBlock), NoLifecycleBy leftActor (traceAfterBlock rightBlock))
o19OrderedOuterNoLifecycle {leftActor} {rightActor} leftBlock rightBlock ordered =
  (o19NoLifecycleFromWord rightActor (traceBeforeBlock leftBlock)
    (\action, member => o19NoLifecycleWordMember rightActor (traceBeforeBlock rightBlock) (noEarlierLifecycle rightBlock) action
      (replace {p = Elem action} (sym (o19OrderedBeforeWord leftBlock rightBlock ordered))
      (fst (o19ElemAppendInjections (o19ActionWord (prefixThroughBlock leftBlock)) (o19ActionWord (betweenBlocks ordered))) (replace {p = Elem action} (sym (o19ActionWordAppend (prefixToBlockOpening leftBlock) (blockBody leftBlock)))
        (fst (o19ElemAppendInjections (o19ActionWord (prefixToBlockOpening leftBlock)) (o19ActionWord (blockBody leftBlock))) (replace {p = Elem action} (sym (o19ActionWordAppend (traceBeforeBlock leftBlock) (MoreTransitions (beginTransition (blockOpening leftBlock)) NoTransitions)))
          (fst (o19ElemAppendInjections (o19ActionWord (traceBeforeBlock leftBlock)) [LBegin leftActor]) member))))))),
   o19NoLifecycleFromWord leftActor (traceAfterBlock rightBlock)
    (\action, member => o19NoLifecycleWordMember leftActor (traceAfterBlock leftBlock) (noLaterLifecycle leftBlock) action
      (replace {p = Elem action} (sym (o19OrderedAfterWord leftBlock rightBlock ordered))
      (snd (o19ElemAppendInjections (o19ActionWord (betweenBlocks ordered)) ((o19ActionWord (actorBlockTrace rightBlock)) ++ (o19ActionWord (traceAfterBlock rightBlock))))
        (snd (o19ElemAppendInjections (o19ActionWord (actorBlockTrace rightBlock)) (o19ActionWord (traceAfterBlock rightBlock))) member)))))

||| A genuine original block-word observation excludes lifecycle ownership
||| by a distinct actor. Yielded registrations are not lifecycle actions.
export
0 o19ForeignBlockWordNoLifecycle :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {actor, forbidden, selected : name} -> {action : Action name key value world error} ->
  Not (actor = selected) -> O19BlockWordObservation name key world error value actor forbidden action ->
  (isLifecycleAction action = True) -> Not (actionOwner action = selected)
o19ForeignBlockWordNoLifecycle distinct (BlockOwnLifecycle lifecycle owner) active same = distinct (trans (sym owner) same)
o19ForeignBlockWordNoLifecycle distinct (BlockGenerated child component inserted safe) active same =
  uninhabited (trans (sym (trans (cong isLifecycleAction inserted) Refl)) active)

||| ALL FOUR outside-lifecycle properties on the actual reached cuts.
||| Cross-actor exclusions come from authenticated original ordering; moved
||| words come from the OWN run/cut, with no new safety or ordering premise.
export
0 o19ActualMovedOutsideLifecycle :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal : SystemState name key value world error} -> (source : Transitions initial sourceFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
  ((NoLifecycleBy (actorRight swap) (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))), NoLifecycleBy (actorRight swap) (columnRest (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique))),
   (NoLifecycleBy (actorLeft swap) (appendTransitions (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))) (columnRight (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique))), NoLifecycleBy (actorLeft swap) (cutSuffix (o19ColumnLeftCut (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))) (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19ActionWord (traceAfterBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)))))
o19ActualMovedOutsideLifecycle nameEq keyEq protocol swap source blocks premises safety unique =
  ((fst (o19OrderedOuterNoLifecycle (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)) (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)) (safetyBlocksOrdered safety)),
    o19NoLifecycleFromWord (actorRight swap) (columnRest (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique))
      (\action, member => o19ElemAppendCases (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) (o19ActionWord (traceAfterBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety))))
        (\inLeft => o19ForeignBlockWordNoLifecycle (actorDistinct swap)
          (o19OriginalBlockWord (actorLeft swap) (actorRight swap) (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)) (safetyLeftDoesNotGenerateRight safety) action inLeft))
        (\inSuffix => o19NoLifecycleWordMember (actorRight swap) (traceAfterBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety))) (noLaterLifecycle (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety))) action inSuffix)
        (replace {p = Elem action} (columnRestWord (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)) member))),
   (o19NoLifecycleFromWord (actorLeft swap) (appendTransitions (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))) (columnRight (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)))
      (\action, member => o19ElemAppendCases (o19ActionWord (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) (o19ActionWord (columnRight (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)))
        (\inEarlier => o19NoLifecycleWordMember (actorLeft swap) (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))) (noEarlierLifecycle (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))) action inEarlier)
        (\inRight => o19ForeignBlockWordNoLifecycle (\same => actorDistinct swap (sym same))
          (o19OriginalBlockWord (actorRight swap) (actorLeft swap) (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)) (safetyRightDoesNotGenerateLeft safety) action
            (replace {p = Elem action} (columnRightWord (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)) inRight)))
        (replace {p = Elem action} (o19ActionWordAppend (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))) (columnRight (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique))) member)),
    o19NoLifecycleFromWord (actorLeft swap) (cutSuffix (o19ColumnLeftCut (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))) (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19ActionWord (traceAfterBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)))
      (\action, member => o19NoLifecycleWordMember (actorLeft swap) (traceAfterBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety))) (snd (o19OrderedOuterNoLifecycle (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)) (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)) (safetyBlocksOrdered safety))) action
        (replace {p = Elem action} (cutRightWord (o19ColumnLeftCut (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))) (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19ActionWord (traceAfterBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique))) member))))

||| BOTH ACTUAL reached bodies retain actor lifecycle/generated-child
||| ownership, deriving every word observation from the selected original body.
export
0 o19ActualMovedBodiesActorOnly :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal : SystemState name key value world error} -> (source : Transitions initial sourceFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
  (ActorLifecycleOnly (actorRight swap) (rangeBody (o19ActualRightBeginRange nameEq keyEq protocol swap source blocks premises safety unique)),
   ActorLifecycleOnly (actorLeft swap) (rangeBody (o19ActualLeftBeginRange nameEq keyEq protocol swap source blocks premises safety unique)))
o19ActualMovedBodiesActorOnly nameEq keyEq protocol swap source blocks premises safety unique =
  (o19ActorOnlyFromWord (actorRight swap) (actorLeft swap) (rangeBody (o19ActualRightBeginRange nameEq keyEq protocol swap source blocks premises safety unique))
    (\action, member => o19OwnedSafeWord (actorRight swap) (actorLeft swap) (blockBody (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety))) (blockActorOnly (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety))) (safetyRightDoesNotGenerateLeft safety)
      action (replace {p = Elem action} (rangeBodyWord (o19ActualRightBeginRange nameEq keyEq protocol swap source blocks premises safety unique)) member)),
   o19ActorOnlyFromWord (actorLeft swap) (actorRight swap) (rangeBody (o19ActualLeftBeginRange nameEq keyEq protocol swap source blocks premises safety unique))
    (\action, member => o19OwnedSafeWord (actorLeft swap) (actorRight swap) (blockBody (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))) (blockActorOnly (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))) (safetyLeftDoesNotGenerateRight safety)
      action (replace {p = Elem action} (rangeBodyWord (o19ActualLeftBeginRange nameEq keyEq protocol swap source blocks premises safety unique)) member)))

||| FULL ACTUAL moved-right located open episode: its installed/actor-only
||| body, both outside exclusions, final-active and exact global decomposition
||| are ALL produced from O19 inputs on the SAME actual Cartesian trace.
export
0 o19ActualRightLocatedBlock :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal : SystemState name key value world error} -> (source : Transitions initial sourceFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
  LocatedOpenEpisodeBlock name key world error value nameEq keyEq (actorRight swap)
    (cursorTrace (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)))
o19ActualRightLocatedBlock nameEq keyEq protocol swap source blocks premises safety unique =
  MkLocatedOpenEpisodeBlock (blockPreStart (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))) (rangeStart (o19ActualRightBeginRange nameEq keyEq protocol swap source blocks premises safety unique)) (columnMiddle (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique))
    (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))) (rangeOpening (o19ActualRightBeginRange nameEq keyEq protocol swap source blocks premises safety unique)) (rangeBody (o19ActualRightBeginRange nameEq keyEq protocol swap source blocks premises safety unique))
    (fst (o19ActualMovedBodiesInstalled nameEq keyEq protocol swap source blocks premises safety unique)) (fst (o19ActualMovedBodiesActorOnly nameEq keyEq protocol swap source blocks premises safety unique)) (columnRest (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique))
    (fst (fst (o19ActualMovedOutsideLifecycle nameEq keyEq protocol swap source blocks premises safety unique))) (snd (fst (o19ActualMovedOutsideLifecycle nameEq keyEq protocol swap source blocks premises safety unique)))
    (o19ActualFinalActive nameEq keyEq protocol swap source blocks premises safety unique (actorRight swap) (blockActiveAtFinal (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety))))
    (trans (cong (\spine => appendTransitions (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))) (appendTransitions spine (columnRest (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)))) (rangeDecomposition (o19ActualRightBeginRange nameEq keyEq protocol swap source blocks premises safety unique)))
      (columnDecomposition (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)))

||| FULL ACTUAL moved-left located open episode, with all fields derived
||| on the SAME reached cut/trace. Neither moved block is now a caller oracle.
export
0 o19ActualLeftLocatedBlock :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal : SystemState name key value world error} -> (source : Transitions initial sourceFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
  LocatedOpenEpisodeBlock name key world error value nameEq keyEq (actorLeft swap)
    (cursorTrace (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)))
o19ActualLeftLocatedBlock nameEq keyEq protocol swap source blocks premises safety unique =
  MkLocatedOpenEpisodeBlock (columnMiddle (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)) (rangeStart (o19ActualLeftBeginRange nameEq keyEq protocol swap source blocks premises safety unique)) (cutMiddle (o19ColumnLeftCut (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))) (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19ActionWord (traceAfterBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)))
    (appendTransitions (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))) (columnRight (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique))) (rangeOpening (o19ActualLeftBeginRange nameEq keyEq protocol swap source blocks premises safety unique)) (rangeBody (o19ActualLeftBeginRange nameEq keyEq protocol swap source blocks premises safety unique))
    (snd (o19ActualMovedBodiesInstalled nameEq keyEq protocol swap source blocks premises safety unique)) (snd (o19ActualMovedBodiesActorOnly nameEq keyEq protocol swap source blocks premises safety unique)) (cutSuffix (o19ColumnLeftCut (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))) (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19ActionWord (traceAfterBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)))
    (fst (snd (o19ActualMovedOutsideLifecycle nameEq keyEq protocol swap source blocks premises safety unique))) (snd (snd (o19ActualMovedOutsideLifecycle nameEq keyEq protocol swap source blocks premises safety unique)))
    (o19ActualFinalActive nameEq keyEq protocol swap source blocks premises safety unique (actorLeft swap) (blockActiveAtFinal (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))))
    (trans (cong (\spine => appendTransitions (appendTransitions (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))) (columnRight (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique))) (appendTransitions spine (cutSuffix (o19ColumnLeftCut (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))) (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19ActionWord (traceAfterBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique))))) (rangeDecomposition (o19ActualLeftBeginRange nameEq keyEq protocol swap source blocks premises safety unique)))
      (trans (appendTransitionsAssociative (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))) (columnRight (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)) (appendTransitions (cutPrefix (o19ColumnLeftCut (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))) (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19ActionWord (traceAfterBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique))) (cutSuffix (o19ColumnLeftCut (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))) (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19ActionWord (traceAfterBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)))))
        (o19ColumnCutDecomposition (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))) (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19ActionWord (traceAfterBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique) (o19ColumnLeftCut (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))) (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19ActionWord (traceAfterBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)))))

||| The two FULL actual moved blocks are in the reversed adjacent order.
||| The empty gap and prefix equation come from their OWN reached ranges.
export
0 o19ActualMovedBlocksOrdered :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal : SystemState name key value world error} -> (source : Transitions initial sourceFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
  BlockBefore name key world error value nameEq keyEq (cursorTrace (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)))
    (actorRight swap) (actorLeft swap) (o19ActualRightLocatedBlock nameEq keyEq protocol swap source blocks premises safety unique) (o19ActualLeftLocatedBlock nameEq keyEq protocol swap source blocks premises safety unique)
o19ActualMovedBlocksOrdered nameEq keyEq protocol swap source blocks premises safety unique =
  MkBlockBefore NoTransitions
    (cong (\leading => appendTransitions leading (MoreTransitions (beginTransition (rangeOpening (o19ActualLeftBeginRange nameEq keyEq protocol swap source blocks premises safety unique))) NoTransitions))
      (sym (trans (appendTransitionsAssociative (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))) (MoreTransitions (beginTransition (rangeOpening (o19ActualRightBeginRange nameEq keyEq protocol swap source blocks premises safety unique))) NoTransitions) (rangeBody (o19ActualRightBeginRange nameEq keyEq protocol swap source blocks premises safety unique)))
        (cong (appendTransitions (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) (rangeDecomposition (o19ActualRightBeginRange nameEq keyEq protocol swap source blocks premises safety unique))))))

||| Actor-only structure transports along exact body words, even for an
||| untouched block with no selected-pair NoGeneratedChild hypothesis.
||| This is a label-property theorem, NOT replay/external correspondence.
export
0 o19ActorOnlySameWord :
  {name, key, world, error : Type} -> {value : key -> Type} -> (selected : name) ->
  {sourceFirst, sourceLast, targetFirst, targetLast : SystemState name key value world error} ->
  (source : Transitions sourceFirst sourceLast) -> (target : Transitions targetFirst targetLast) ->
  ActorLifecycleOnly selected source -> (o19ActionWord target = o19ActionWord source) ->
  ActorLifecycleOnly selected target
o19ActorOnlySameWord selected _ NoTransitions ActorLifecycleEnd exact = ActorLifecycleEnd
o19ActorOnlySameWord selected _ (MoreTransitions step rest) ActorLifecycleEnd exact = void (uninhabited (cong length exact))
o19ActorOnlySameWord selected _ NoTransitions (ActorLifecycleStep step rest lifecycle owner tail) exact = void (uninhabited (cong length exact))
o19ActorOnlySameWord selected _ NoTransitions (ActorYieldedRegistrationStep step rest inserted tail) exact = void (uninhabited (cong length exact))
o19ActorOnlySameWord selected _ (MoreTransitions reached reachedRest) (ActorLifecycleStep step rest lifecycle owner tail) exact =
  ActorLifecycleStep reached reachedRest
    (trans (cong isLifecycleAction (fst (consInjective exact))) lifecycle)
    (trans (o19TransitionActorOwner reached) (trans (cong actionOwner (fst (consInjective exact)))
      (trans (sym (o19TransitionActorOwner step)) owner)))
    (o19ActorOnlySameWord selected rest reachedRest tail (snd (consInjective exact)))
o19ActorOnlySameWord selected _ (MoreTransitions reached reachedRest) (ActorYieldedRegistrationStep step rest inserted tail) exact =
  ActorYieldedRegistrationStep reached reachedRest (trans (fst (consInjective exact)) inserted)
    (o19ActorOnlySameWord selected rest reachedRest tail (snd (consInjective exact)))

||| Internal generic reconstruction boundary for an untouched source block.
||| Actual dependent segments/range and genuine occurrence origins determine
||| the reached body/installedness; outside and active proofs remain explicit.
export
0 o19LocatedFromActualSegments :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {initial, sourceFinal, targetFinal, before, rangeEnd : SystemState name key value world error} ->
  (source : Transitions initial sourceFinal) ->
  (block : LocatedOpenEpisodeBlock name key world error value nameEq keyEq selected source) ->
  (target : Transitions initial targetFinal) ->
  (origins : ActionRegistrationReplayCorrespondence name key world error value source target) ->
  (earlier : Transitions initial before) -> (middle : Transitions before rangeEnd) -> (later : Transitions rangeEnd targetFinal) ->
  (appendTransitions earlier (appendTransitions middle later) = target) ->
  (range : O19BeginRange name key world error value nameEq keyEq selected middle (o19ActionWord (blockBody block))) ->
  NoLifecycleBy selected earlier -> NoLifecycleBy selected later ->
  (supportedActiveAt {name} {key} {value} {world} {error} @{nameEq} selected targetFinal = True) ->
  LocatedOpenEpisodeBlock name key world error value nameEq keyEq selected target
o19LocatedFromActualSegments {before} {rangeEnd} nameEq keyEq selected source block target origins earlier middle later decomposition range noEarlier noLater active =
  MkLocatedOpenEpisodeBlock before (rangeStart range) rangeEnd earlier (rangeOpening range) (rangeBody range)
    (o19BeginRangeInstalled nameEq keyEq selected middle (o19ActionWord (blockBody block)) range
      (fst (o19NoUnloadAppendSplit selected middle later
        (snd (o19NoUnloadAppendSplit selected earlier (appendTransitions middle later)
          (replace {p = NoParentUnload selected} (sym decomposition)
            (o19NoUnloadFromOrigins selected source target (\occurrence => replayActionOrigin origins occurrence)
              (o19OriginalBlockNoUnload nameEq keyEq selected source block))))))))
    (o19ActorOnlySameWord selected (blockBody block) (rangeBody range) (blockActorOnly block) (rangeBodyWord range))
    later noEarlier noLater active
    (trans (cong (\spine => appendTransitions earlier (appendTransitions spine later)) (rangeDecomposition range)) decomposition)

||| Typed observation boundary for two ACTUAL word cuts. Their own
||| decompositions/alignments determine the reached Begin and every segment.
export
0 o19LocatedFromWordCuts :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {initial, sourceFinal, targetFinal : SystemState name key value world error} ->
  (source : Transitions initial sourceFinal) ->
  (block : LocatedOpenEpisodeBlock name key world error value nameEq keyEq selected source) ->
  (target : Transitions initial targetFinal) ->
  AlignedTransitions name key world error value nameEq keyEq target ->
  ActionRegistrationReplayCorrespondence name key world error value source target ->
  (supportedActiveAt {name} {key} {value} {world} {error} @{nameEq} selected targetFinal = True) ->
  (beforeWord, afterWord : List (Action name key value world error)) ->
  ((action : Action name key value world error) -> Elem action beforeWord ->
    (isLifecycleAction action = True) -> Not (actionOwner action = selected)) ->
  ((action : Action name key value world error) -> Elem action afterWord ->
    (isLifecycleAction action = True) -> Not (actionOwner action = selected)) ->
  (firstCut : O19WordCut name key world error value beforeWord (o19ActionWord (actorBlockTrace block) ++ afterWord) target) ->
  (secondCut : O19WordCut name key world error value (o19ActionWord (actorBlockTrace block)) afterWord (cutSuffix firstCut)) ->
  LocatedOpenEpisodeBlock name key world error value nameEq keyEq selected target
o19LocatedFromWordCuts nameEq keyEq selected source block target aligned origins active beforeWord afterWord noEarlier noLater firstCut secondCut =
  o19LocatedFromActualSegments nameEq keyEq selected source block target origins
    (cutPrefix firstCut) (cutPrefix secondCut) (cutSuffix secondCut)
    (trans (cong (appendTransitions (cutPrefix firstCut)) (cutDecomposition secondCut)) (cutDecomposition firstCut))
    (o19BeginRangeObserved nameEq keyEq selected (cutPrefix secondCut) (o19ActionWord (blockBody block))
      (fst (alignedAppendSplit (cutPrefix secondCut) (cutSuffix secondCut)
        (replace {p = AlignedTransitions name key world error value nameEq keyEq} (sym (cutDecomposition secondCut))
          (snd (alignedAppendSplit (cutPrefix firstCut) (cutSuffix firstCut)
            (replace {p = AlignedTransitions name key world error value nameEq keyEq} (sym (cutDecomposition firstCut)) aligned))))))
      (cutLeftWord secondCut))
    (o19NoLifecycleFromWord selected (cutPrefix firstCut)
      (\action, member => noEarlier action (replace {p = Elem action} (cutLeftWord firstCut) member)))
    (o19NoLifecycleFromWord selected (cutSuffix secondCut)
      (\action, member => noLater action (replace {p = Elem action} (cutRightWord secondCut) member))) active

||| The second actual cut is constructed from the FIRST cut's owned
||| residual word; no caller block cut or independent reached trace is used.
export
0 o19LocatedAfterFirstCut :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {initial, sourceFinal, targetFinal : SystemState name key value world error} ->
  (source : Transitions initial sourceFinal) ->
  (block : LocatedOpenEpisodeBlock name key world error value nameEq keyEq selected source) ->
  (target : Transitions initial targetFinal) ->
  AlignedTransitions name key world error value nameEq keyEq target ->
  ActionRegistrationReplayCorrespondence name key world error value source target ->
  (supportedActiveAt {name} {key} {value} {world} {error} @{nameEq} selected targetFinal = True) ->
  (beforeWord, afterWord : List (Action name key value world error)) ->
  ((action : Action name key value world error) -> Elem action beforeWord ->
    (isLifecycleAction action = True) -> Not (actionOwner action = selected)) ->
  ((action : Action name key value world error) -> Elem action afterWord ->
    (isLifecycleAction action = True) -> Not (actionOwner action = selected)) ->
  (firstCut : O19WordCut name key world error value beforeWord (o19ActionWord (actorBlockTrace block) ++ afterWord) target) ->
  LocatedOpenEpisodeBlock name key world error value nameEq keyEq selected target
o19LocatedAfterFirstCut nameEq keyEq selected source block target aligned origins active beforeWord afterWord noEarlier noLater firstCut =
  o19LocatedFromWordCuts nameEq keyEq selected source block target aligned origins active beforeWord afterWord noEarlier noLater firstCut
    (o19CutByWord (o19ActionWord (actorBlockTrace block)) afterWord (cutSuffix firstCut) (cutRightWord firstCut))

||| Generic full block reconstruction from an exact TARGET word placement.
||| Both reached dependent cuts, Begin and installed body are derived. The
||| word placement/outside laws are separately discharged for untouched blocks.
export
0 o19LocatedByWord :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {initial, sourceFinal, targetFinal : SystemState name key value world error} ->
  (source : Transitions initial sourceFinal) ->
  (block : LocatedOpenEpisodeBlock name key world error value nameEq keyEq selected source) ->
  (target : Transitions initial targetFinal) ->
  AlignedTransitions name key world error value nameEq keyEq target ->
  ActionRegistrationReplayCorrespondence name key world error value source target ->
  (supportedActiveAt {name} {key} {value} {world} {error} @{nameEq} selected targetFinal = True) ->
  (beforeWord, afterWord : List (Action name key value world error)) ->
  ((action : Action name key value world error) -> Elem action beforeWord ->
    (isLifecycleAction action = True) -> Not (actionOwner action = selected)) ->
  ((action : Action name key value world error) -> Elem action afterWord ->
    (isLifecycleAction action = True) -> Not (actionOwner action = selected)) ->
  (o19ActionWord target = beforeWord ++ (o19ActionWord (actorBlockTrace block) ++ afterWord)) ->
  LocatedOpenEpisodeBlock name key world error value nameEq keyEq selected target
o19LocatedByWord nameEq keyEq selected source block target aligned origins active beforeWord afterWord noEarlier noLater placement =
  o19LocatedAfterFirstCut nameEq keyEq selected source block target aligned origins active beforeWord afterWord noEarlier noLater
    (o19CutByWord beforeWord (o19ActionWord (actorBlockTrace block) ++ afterWord) target placement)

||| Word of an actual prefix-through-block, with dependent append and the
||| real opening normalized. Used to place untouched blocks in reached words.
export
0 o19PrefixThroughWord :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {selected : name} ->
  {initial, finalState : SystemState name key value world error} -> {source : Transitions initial finalState} ->
  (block : LocatedOpenEpisodeBlock name key world error value nameEq keyEq selected source) ->
  (o19ActionWord (prefixThroughBlock block) = o19ActionWord (traceBeforeBlock block) ++ o19ActionWord (actorBlockTrace block))
o19PrefixThroughWord {selected} block =
  trans (o19ActionWordAppend (prefixToBlockOpening block) (blockBody block))
    (trans (cong (\word => word ++ o19ActionWord (blockBody block))
      (o19ActionWordAppend (traceBeforeBlock block) (MoreTransitions (beginTransition (blockOpening block)) NoTransitions)))
      (sym (appendAssociative (o19ActionWord (traceBeforeBlock block)) [LBegin selected] (o19ActionWord (blockBody block)))))

||| Exact ACTUAL whole reached word, derived from the OWN column trace
||| decomposition and residual words. This is not occurrence correspondence.
export
0 o19ActualSwapWord :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal : SystemState name key value world error} -> (source : Transitions initial sourceFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
  (o19ActionWord (cursorTrace (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique))) =
    o19ActionWord (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))) ++ ((o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) ++ ((o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) ++ (o19ActionWord (traceAfterBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))))))
o19ActualSwapWord nameEq keyEq protocol swap source blocks premises safety unique =
  trans (sym (cong o19ActionWord (columnDecomposition (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique))))
    (trans (o19ActionWordAppend (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))) (appendTransitions (columnRight (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)) (columnRest (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique))))
      (cong (o19ActionWord (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))) ++)
        (trans (o19ActionWordAppend (columnRight (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)) (columnRest (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)))
          (cong2 (++) (columnRightWord (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)) (columnRestWord (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique))))))

||| Authentic TARGET word placement for any original block before the
||| selected pair. Its source BlockBefore determines the actual untouched gap.
export
0 o19UntouchedBeforePlacement :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal : SystemState name key value world error} -> (source : Transitions initial sourceFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
  (selected : name) ->
  (untouched : LocatedOpenEpisodeBlock name key world error value nameEq keyEq selected source) ->
  (ordered : BlockBefore name key world error value nameEq keyEq source selected (actorLeft swap) untouched (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))) ->
  (o19ActionWord (cursorTrace (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique))) = (o19ActionWord (traceBeforeBlock untouched)) ++ ((o19ActionWord (actorBlockTrace untouched)) ++ ((o19ActionWord (betweenBlocks ordered)) ++ ((o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) ++ ((o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) ++ (o19ActionWord (traceAfterBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))))))))
o19UntouchedBeforePlacement nameEq keyEq protocol swap source blocks premises safety unique selected untouched ordered =
  trans (o19ActualSwapWord nameEq keyEq protocol swap source blocks premises safety unique)
    (trans (cong (\word => word ++ ((o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) ++ ((o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) ++ (o19ActionWord (traceAfterBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))))))
      (trans (o19OrderedBeforeWord untouched (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)) ordered)
        (cong (\word => word ++ (o19ActionWord (betweenBlocks ordered))) (o19PrefixThroughWord untouched))))
      (trans (sym (appendAssociative ((o19ActionWord (traceBeforeBlock untouched)) ++ (o19ActionWord (actorBlockTrace untouched))) (o19ActionWord (betweenBlocks ordered)) ((o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) ++ ((o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) ++ (o19ActionWord (traceAfterBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety))))))))
        (sym (appendAssociative (o19ActionWord (traceBeforeBlock untouched)) (o19ActionWord (actorBlockTrace untouched)) ((o19ActionWord (betweenBlocks ordered)) ++ ((o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) ++ ((o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) ++ (o19ActionWord (traceAfterBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))))))))))

||| Authentic TARGET placement for any original block after the pair.
||| The actual sealed/reached suffix word is used, not a source trace bound.
export
0 o19UntouchedAfterPlacement :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal : SystemState name key value world error} -> (source : Transitions initial sourceFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
  (selected : name) ->
  (untouched : LocatedOpenEpisodeBlock name key world error value nameEq keyEq selected source) ->
  (ordered : BlockBefore name key world error value nameEq keyEq source (actorRight swap) selected (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)) untouched) ->
  (o19ActionWord (cursorTrace (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique))) = ((o19ActionWord (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) ++ ((o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) ++ ((o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) ++ (o19ActionWord (betweenBlocks ordered))))) ++ ((o19ActionWord (actorBlockTrace untouched)) ++ (o19ActionWord (traceAfterBlock untouched))))
o19UntouchedAfterPlacement nameEq keyEq protocol swap source blocks premises safety unique selected untouched ordered =
  trans (o19ActualSwapWord nameEq keyEq protocol swap source blocks premises safety unique)
    (trans (cong (\word => (o19ActionWord (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) ++ ((o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) ++ ((o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) ++ word))) (o19OrderedAfterWord (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)) untouched ordered))
      (trans (cong ((o19ActionWord (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) ++) (cong ((o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) ++) (appendAssociative (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) (o19ActionWord (betweenBlocks ordered)) ((o19ActionWord (actorBlockTrace untouched)) ++ (o19ActionWord (traceAfterBlock untouched))))))
        (trans (cong ((o19ActionWord (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) ++) (appendAssociative (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) ((o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) ++ (o19ActionWord (betweenBlocks ordered))) ((o19ActionWord (actorBlockTrace untouched)) ++ (o19ActionWord (traceAfterBlock untouched)))))
          (appendAssociative (o19ActionWord (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) ((o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) ++ ((o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) ++ (o19ActionWord (betweenBlocks ordered)))) ((o19ActionWord (actorBlockTrace untouched)) ++ (o19ActionWord (traceAfterBlock untouched)))))))

||| FULL reached transport of ANY original block before the swapped pair.
||| Its actual placement, outside exclusions, Begin/body/install/active and
||| decomposition are all derived; no reached-block/cut/word oracle remains.
export
0 o19ActualUntouchedBeforeBlock :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal : SystemState name key value world error} -> (source : Transitions initial sourceFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
  (selected : name) ->
  (untouched : LocatedOpenEpisodeBlock name key world error value nameEq keyEq selected source) ->
  (ordered : BlockBefore name key world error value nameEq keyEq source selected (actorLeft swap) untouched (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))) ->
  LocatedOpenEpisodeBlock name key world error value nameEq keyEq selected (cursorTrace (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)))
o19ActualUntouchedBeforeBlock nameEq keyEq protocol swap source blocks premises safety unique selected untouched ordered =
  o19LocatedByWord nameEq keyEq selected source untouched (cursorTrace (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)))
    (replayAligned (cursorBundle (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique))))
    (finiteDerivationOccurrenceCorrespondence (cursorDerivation (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique))))
    (o19ActualFinalActive nameEq keyEq protocol swap source blocks premises safety unique selected (blockActiveAtFinal untouched))
    (o19ActionWord (traceBeforeBlock untouched)) ((o19ActionWord (betweenBlocks ordered)) ++ ((o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) ++ ((o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) ++ (o19ActionWord (traceAfterBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))))))
    (o19NoLifecycleWordMember selected (traceBeforeBlock untouched) (noEarlierLifecycle untouched))
    (\action, member => o19NoLifecycleWordMember selected (traceAfterBlock untouched) (noLaterLifecycle untouched) action
      (replace {p = Elem action} (sym (o19OrderedAfterWord untouched (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)) ordered))
      (o19ElemAppendCases (o19ActionWord (betweenBlocks ordered)) ((o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) ++ ((o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) ++ (o19ActionWord (traceAfterBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety))))))
        (\inGap => fst (o19ElemAppendInjections (o19ActionWord (betweenBlocks ordered)) ((o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) ++ (o19ActionWord (traceAfterBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))))) inGap)
        (\inRest => snd (o19ElemAppendInjections (o19ActionWord (betweenBlocks ordered)) ((o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) ++ (o19ActionWord (traceAfterBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))))) (o19ElemAppendCases (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) ((o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) ++ (o19ActionWord (traceAfterBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))))
          (\inRight => (snd (o19ElemAppendInjections (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) (o19ActionWord (traceAfterBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))))) (replace {p = Elem action} (sym (o19OrderedAfterWord (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)) (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)) (safetyBlocksOrdered safety))) (snd (o19ElemAppendInjections (o19ActionWord (betweenBlocks (safetyBlocksOrdered safety))) ((o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) ++ (o19ActionWord (traceAfterBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))))) (fst (o19ElemAppendInjections (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19ActionWord (traceAfterBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety))))) inRight)))))
          (\inLeftSuffix => o19ElemAppendCases (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) (o19ActionWord (traceAfterBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety))))
            (\inLeft => (fst (o19ElemAppendInjections (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) (o19ActionWord (traceAfterBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))))) inLeft))
            (\inSuffix => (snd (o19ElemAppendInjections (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) (o19ActionWord (traceAfterBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))))) (replace {p = Elem action} (sym (o19OrderedAfterWord (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)) (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)) (safetyBlocksOrdered safety))) (snd (o19ElemAppendInjections (o19ActionWord (betweenBlocks (safetyBlocksOrdered safety))) ((o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) ++ (o19ActionWord (traceAfterBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))))) (snd (o19ElemAppendInjections (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19ActionWord (traceAfterBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety))))) inSuffix))))) inLeftSuffix) inRest)) member)))
    (o19UntouchedBeforePlacement nameEq keyEq protocol swap source blocks premises safety unique selected untouched ordered)

||| FULL reached transport of ANY original block after the swapped pair.
||| All fields use derived target placement/outside words, actual alignment
||| and SAME-chain occurrence origins. No arbitrary reached block is assumed.
export
0 o19ActualUntouchedAfterBlock :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal : SystemState name key value world error} -> (source : Transitions initial sourceFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
  (selected : name) ->
  (untouched : LocatedOpenEpisodeBlock name key world error value nameEq keyEq selected source) ->
  (ordered : BlockBefore name key world error value nameEq keyEq source (actorRight swap) selected (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)) untouched) ->
  LocatedOpenEpisodeBlock name key world error value nameEq keyEq selected (cursorTrace (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)))
o19ActualUntouchedAfterBlock nameEq keyEq protocol swap source blocks premises safety unique selected untouched ordered =
  o19LocatedByWord nameEq keyEq selected source untouched (cursorTrace (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)))
    (replayAligned (cursorBundle (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique))))
    (finiteDerivationOccurrenceCorrespondence (cursorDerivation (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique))))
    (o19ActualFinalActive nameEq keyEq protocol swap source blocks premises safety unique selected (blockActiveAtFinal untouched))
    ((o19ActionWord (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) ++ ((o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) ++ ((o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) ++ (o19ActionWord (betweenBlocks ordered))))) (o19ActionWord (traceAfterBlock untouched))
    (\action, member => o19NoLifecycleWordMember selected (traceBeforeBlock untouched) (noEarlierLifecycle untouched) action
      (o19ElemAppendCases (o19ActionWord (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) ((o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) ++ ((o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) ++ (o19ActionWord (betweenBlocks ordered))))
      (\inEarlier => (replace {p = Elem action} (sym (o19OrderedBeforeWord (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)) untouched ordered)) (fst (o19ElemAppendInjections (o19ActionWord (prefixThroughBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19ActionWord (betweenBlocks ordered))) (replace {p = Elem action} (sym (o19PrefixThroughWord (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (fst (o19ElemAppendInjections (o19ActionWord (traceBeforeBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety))))) (replace {p = Elem action} (sym (o19OrderedBeforeWord (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)) (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)) (safetyBlocksOrdered safety))) (fst (o19ElemAppendInjections (o19ActionWord (prefixThroughBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) (o19ActionWord (betweenBlocks (safetyBlocksOrdered safety)))) (replace {p = Elem action} (sym (o19PrefixThroughWord (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) (fst (o19ElemAppendInjections (o19ActionWord (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))))) inEarlier)))))))))
      (\inRest => o19ElemAppendCases (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) ((o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) ++ (o19ActionWord (betweenBlocks ordered)))
        (\inRight => (replace {p = Elem action} (sym (o19OrderedBeforeWord (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)) untouched ordered)) (fst (o19ElemAppendInjections (o19ActionWord (prefixThroughBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19ActionWord (betweenBlocks ordered))) (replace {p = Elem action} (sym (o19PrefixThroughWord (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (snd (o19ElemAppendInjections (o19ActionWord (traceBeforeBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety))))) inRight)))))
        (\inLeftGap => o19ElemAppendCases (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) (o19ActionWord (betweenBlocks ordered))
          (\inLeft => (replace {p = Elem action} (sym (o19OrderedBeforeWord (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)) untouched ordered)) (fst (o19ElemAppendInjections (o19ActionWord (prefixThroughBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19ActionWord (betweenBlocks ordered))) (replace {p = Elem action} (sym (o19PrefixThroughWord (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (fst (o19ElemAppendInjections (o19ActionWord (traceBeforeBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety))))) (replace {p = Elem action} (sym (o19OrderedBeforeWord (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)) (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)) (safetyBlocksOrdered safety))) (fst (o19ElemAppendInjections (o19ActionWord (prefixThroughBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) (o19ActionWord (betweenBlocks (safetyBlocksOrdered safety)))) (replace {p = Elem action} (sym (o19PrefixThroughWord (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) (snd (o19ElemAppendInjections (o19ActionWord (traceBeforeBlock (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety)))) (o19ActionWord (actorBlockTrace (decomposedBlock blocks (actorLeft swap) (safetyLeftInOrder safety))))) inLeft)))))))))
          (\inGap => (replace {p = Elem action} (sym (o19OrderedBeforeWord (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)) untouched ordered)) (snd (o19ElemAppendInjections (o19ActionWord (prefixThroughBlock (decomposedBlock blocks (actorRight swap) (safetyRightInOrder safety)))) (o19ActionWord (betweenBlocks ordered))) inGap))) inLeftGap) inRest) member))
    (o19NoLifecycleWordMember selected (traceAfterBlock untouched) (noLaterLifecycle untouched))
    (o19UntouchedAfterPlacement nameEq keyEq protocol swap source blocks premises safety unique selected untouched ordered)

||| Positional classification in the target order, retaining prefix/suffix
||| membership rather than testing names (repeated labels are not conflated).
public export
data O19SwapSite : {name : Type} -> (leading : List name) -> (left, right : name) ->
  (trailing : List name) -> (selected : name) -> Type where
  O19SiteBefore : {name : Type} -> {leading, trailing : List name} -> {left, right, selected : name} ->
    Elem selected leading -> O19SwapSite leading left right trailing selected
  O19SiteRight : {name : Type} -> {leading, trailing : List name} -> {left, right : name} ->
    O19SwapSite leading left right trailing right
  O19SiteLeft : {name : Type} -> {leading, trailing : List name} -> {left, right : name} ->
    O19SwapSite leading left right trailing left
  O19SiteAfter : {name : Type} -> {leading, trailing : List name} -> {left, right, selected : name} ->
    Elem selected trailing -> O19SwapSite leading left right trailing selected

||| Single structural observation of the two selected target positions or
||| the actual trailing member. No equality-of-label classification is used.
export
0 o19ClassifySwapTail : {name : Type} -> (leading : List name) -> (left, right : name) ->
  (trailing : List name) -> {selected : name} -> Elem selected (right :: left :: trailing) ->
  O19SwapSite leading left right trailing selected
o19ClassifySwapTail leading left right trailing Here = O19SiteRight
o19ClassifySwapTail leading left right trailing (There Here) = O19SiteLeft
o19ClassifySwapTail leading left right trailing (There (There member)) = O19SiteAfter member

||| Complete positional classifier for the actual target list shape.
export
0 o19ClassifySwapSite : {name : Type} -> (leading : List name) -> (left, right : name) ->
  (trailing : List name) -> {selected : name} -> Elem selected (leading ++ (right :: left :: trailing)) ->
  O19SwapSite leading left right trailing selected
o19ClassifySwapSite leading left right trailing member =
  o19ElemAppendCases leading (right :: left :: trailing) O19SiteBefore
    (o19ClassifySwapTail leading left right trailing) member

||| Each prefix occurrence is before the first appended selected actor.
export
0 o19BeforeAppendedSelected : {name : Type} -> (leading : List name) -> (left : name) ->
  (trailing : List name) -> {selected : name} -> Elem selected leading ->
  BeforeIn selected left (leading ++ (left :: trailing))
o19BeforeAppendedSelected [] left trailing member = void (uninhabited member)
o19BeforeAppendedSelected (head :: rest) left trailing Here =
  BeforeHere (snd (o19ElemAppendInjections rest (left :: trailing)) Here)
o19BeforeAppendedSelected (head :: rest) left trailing (There member) =
  BeforeThere (o19BeforeAppendedSelected rest left trailing member)

||| Preserve a concrete finite order under a leading list.
export
0 o19BeforeInPrepend : {name : Type} -> (leading : List name) ->
  {left, right : name} -> {trailing : List name} -> BeforeIn left right trailing ->
  BeforeIn left right (leading ++ trailing)
o19BeforeInPrepend [] ordered = ordered
o19BeforeInPrepend (head :: rest) ordered = BeforeThere (o19BeforeInPrepend rest ordered)

||| Assemble ALL four classes of reached blocks using only actual target
||| sites and the ORIGINAL block decomposition. Untouched order evidence is
||| derived from exact list positions, not added to the O19 safety surface.
export
0 o19ActualBlockAtSite :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal : SystemState name key value world error} -> (source : Transitions initial sourceFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
  {selected : name} -> O19SwapSite (actorPrefix swap) (actorLeft swap) (actorRight swap) (actorSuffix swap) selected ->
  LocatedOpenEpisodeBlock name key world error value nameEq keyEq selected (cursorTrace (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)))
o19ActualBlockAtSite {selected} nameEq keyEq protocol swap source blocks premises safety unique (O19SiteBefore member) =
  o19ActualUntouchedBeforeBlock nameEq keyEq protocol swap source blocks premises safety unique selected (decomposedBlock blocks selected (replace {p = Elem selected} (sym (actorBeforeExact swap)) (fst (o19ElemAppendInjections (actorPrefix swap) ((actorLeft swap) :: (actorRight swap) :: (actorSuffix swap))) member)))
    (decomposedBlocksFollowOrder blocks selected (actorLeft swap) (replace {p = Elem selected} (sym (actorBeforeExact swap)) (fst (o19ElemAppendInjections (actorPrefix swap) ((actorLeft swap) :: (actorRight swap) :: (actorSuffix swap))) member)) (safetyLeftInOrder safety) (replace {p = BeforeIn selected (actorLeft swap)} (sym (actorBeforeExact swap)) (o19BeforeAppendedSelected (actorPrefix swap) (actorLeft swap) ((actorRight swap) :: (actorSuffix swap)) member)))
o19ActualBlockAtSite nameEq keyEq protocol swap source blocks premises safety unique O19SiteRight = o19ActualRightLocatedBlock nameEq keyEq protocol swap source blocks premises safety unique
o19ActualBlockAtSite nameEq keyEq protocol swap source blocks premises safety unique O19SiteLeft = o19ActualLeftLocatedBlock nameEq keyEq protocol swap source blocks premises safety unique
o19ActualBlockAtSite {selected} nameEq keyEq protocol swap source blocks premises safety unique (O19SiteAfter member) =
  o19ActualUntouchedAfterBlock nameEq keyEq protocol swap source blocks premises safety unique selected (decomposedBlock blocks selected (replace {p = Elem selected} (sym (actorBeforeExact swap)) (snd (o19ElemAppendInjections (actorPrefix swap) ((actorLeft swap) :: (actorRight swap) :: (actorSuffix swap))) (There (There member)))))
    (decomposedBlocksFollowOrder blocks (actorRight swap) selected (safetyRightInOrder safety) (replace {p = Elem selected} (sym (actorBeforeExact swap)) (snd (o19ElemAppendInjections (actorPrefix swap) ((actorLeft swap) :: (actorRight swap) :: (actorSuffix swap))) (There (There member)))) (replace {p = BeforeIn (actorRight swap) selected} (sym (actorBeforeExact swap)) (o19BeforeInPrepend (actorPrefix swap) (BeforeThere (BeforeHere member)))))

||| COMPLETE block selector at the actual TARGET actor order, all fields
||| of each LocatedOpenEpisodeBlock derived on the SAME actual reached trace.
||| Global order/disjointness/coverage obligations are deliberately separate.
export
0 o19ActualTargetBlock :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal : SystemState name key value world error} -> (source : Transitions initial sourceFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
  (selected : name) -> Elem selected targetOrder ->
  LocatedOpenEpisodeBlock name key world error value nameEq keyEq selected (cursorTrace (columnCursor (o19CartesianActualBlocks nameEq keyEq protocol swap source blocks premises safety unique)))
o19ActualTargetBlock nameEq keyEq protocol swap source blocks premises safety unique selected member =
  o19ActualBlockAtSite nameEq keyEq protocol swap source blocks premises safety unique
    (o19ClassifySwapSite (actorPrefix swap) (actorLeft swap) (actorRight swap) (actorSuffix swap)
      (replace {p = Elem selected} (actorAfterExact swap) member))

||| Structural front of ONE actual dependent trace. Constructor indices
||| retain the very same transitions/states, not merely equal action labels.
public export
data O19TracePrefix : {name, key, world, error : Type} -> {value : key -> Type} ->
  {initial, middle, finalState : SystemState name key value world error} ->
  (front : Transitions initial middle) -> (whole : Transitions initial finalState) -> Type where
  O19PrefixEmpty : {name, key, world, error : Type} -> {value : key -> Type} ->
    {initial, finalState : SystemState name key value world error} ->
    (0 whole : Transitions initial finalState) -> O19TracePrefix NoTransitions whole
  O19PrefixMore : {name, key, world, error : Type} -> {value : key -> Type} ->
    {initial, next, middle, finalState : SystemState name key value world error} ->
    (0 step : Transition initial next) -> (0 front : Transitions next middle) -> (0 whole : Transitions next finalState) ->
    (0 smaller : O19TracePrefix front whole) ->
    O19TracePrefix (MoreTransitions step front) (MoreTransitions step whole)

||| The actual left dependent append is structurally a prefix, retaining
||| exact states/transitions. No determinism or label injectivity is assumed.
export
0 o19PrefixAppended : {name, key, world, error : Type} -> {value : key -> Type} ->
  {initial, middle, finalState : SystemState name key value world error} ->
  (front : Transitions initial middle) -> (rest : Transitions middle finalState) ->
  O19TracePrefix front (appendTransitions front rest)
o19PrefixAppended NoTransitions rest = O19PrefixEmpty rest
o19PrefixAppended (MoreTransitions step smaller) rest =
  O19PrefixMore step smaller (appendTransitions smaller rest) (o19PrefixAppended smaller rest)

||| Actual dependent gap between two prefixes with an owned exact equation.
public export
record O19PrefixGap (name, key, world, error : Type) (value : key -> Type)
  {initial, firstEnd, secondEnd : SystemState name key value world error}
  (first : Transitions initial firstEnd) (second : Transitions initial secondEnd) where
  constructor MkO19PrefixGap
  prefixGapTrace : Transitions firstEnd secondEnd
  0 prefixGapExact : appendTransitions first prefixGapTrace = second

||| Typed single-constructor consumer: retain one actual recursive gap
||| while prepending the SAME transition to both prefix endpoints.
export
0 o19PrefixGapCons : {name, key, world, error : Type} -> {value : key -> Type} ->
  {initial, next, firstEnd, secondEnd : SystemState name key value world error} ->
  (step : Transition initial next) -> (first : Transitions next firstEnd) -> (second : Transitions next secondEnd) ->
  O19PrefixGap name key world error value first second ->
  O19PrefixGap name key world error value (MoreTransitions step first) (MoreTransitions step second)
o19PrefixGapCons step first second gap =
  MkO19PrefixGap (prefixGapTrace gap) (cong (MoreTransitions step) (prefixGapExact gap))

||| Quantitative order of TWO prefixes of the SAME ACTUAL trace produces
||| a real dependent gap with exact trace equality. Word equality alone is
||| deliberately insufficient; structural prefix evidence drives the proof.
export
0 o19PrefixGapByCount : {name, key, world, error : Type} -> {value : key -> Type} ->
  {initial, firstEnd, secondEnd, finalState : SystemState name key value world error} ->
  (first : Transitions initial firstEnd) -> (second : Transitions initial secondEnd) -> (whole : Transitions initial finalState) ->
  O19TracePrefix first whole -> O19TracePrefix second whole ->
  LTE (transitionCount first) (transitionCount second) ->
  O19PrefixGap name key world error value first second
o19PrefixGapByCount _ second _ (O19PrefixEmpty _) secondProof bound = MkO19PrefixGap second Refl
o19PrefixGapByCount _ _ _ (O19PrefixMore step firstRest rest firstProof) (O19PrefixEmpty _) bound = void (uninhabited bound)
o19PrefixGapByCount _ _ _ (O19PrefixMore step firstRest rest firstProof)
  (O19PrefixMore _ secondRest _ secondProof) (LTESucc smaller) =
  o19PrefixGapCons step firstRest secondRest (o19PrefixGapByCount firstRest secondRest rest firstProof secondProof smaller)

||| BOTH actual located-block prefixes structurally belong to its original
||| whole trace, via its OWN exact decomposition and dependent append laws.
export
0 o19LocatedBlockPrefixes : {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {selected : name} ->
  {initial, finalState : SystemState name key value world error} -> {source : Transitions initial finalState} ->
  (block : LocatedOpenEpisodeBlock name key world error value nameEq keyEq selected source) ->
  (O19TracePrefix (prefixThroughBlock block) source, O19TracePrefix (traceBeforeBlock block) source)
o19LocatedBlockPrefixes block =
  (replace {p = O19TracePrefix (prefixThroughBlock block)}
    (trans (appendTransitionsAssociative (prefixToBlockOpening block) (blockBody block) (traceAfterBlock block))
      (trans (appendTransitionsAssociative (traceBeforeBlock block) (MoreTransitions (beginTransition (blockOpening block)) NoTransitions)
        (appendTransitions (blockBody block) (traceAfterBlock block))) (blockDecomposition block)))
    (o19PrefixAppended (prefixThroughBlock block) (traceAfterBlock block)),
   replace {p = O19TracePrefix (traceBeforeBlock block)} (blockDecomposition block)
    (o19PrefixAppended (traceBeforeBlock block)
      (MoreTransitions (beginTransition (blockOpening block)) (appendTransitions (blockBody block) (traceAfterBlock block)))))

||| A typed ACTUAL prefix-gap observation constructs full BlockBefore,
||| retaining its dependent gap and exact opening-prefix equation.
export
0 o19BlockBeforeFromGap :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {leftActor, rightActor : name} ->
  {initial, finalState : SystemState name key value world error} -> (source : Transitions initial finalState) ->
  (leftBlock : LocatedOpenEpisodeBlock name key world error value nameEq keyEq leftActor source) ->
  (rightBlock : LocatedOpenEpisodeBlock name key world error value nameEq keyEq rightActor source) ->
  O19PrefixGap name key world error value (prefixThroughBlock leftBlock) (traceBeforeBlock rightBlock) ->
  BlockBefore name key world error value nameEq keyEq source leftActor rightActor leftBlock rightBlock
o19BlockBeforeFromGap source leftBlock rightBlock gap =
  MkBlockBefore (prefixGapTrace gap)
    (trans (cong (\leading => appendTransitions leading (MoreTransitions (beginTransition (blockOpening rightBlock)) NoTransitions)) (sym (prefixGapExact gap)))
      (appendTransitionsAssociative (prefixThroughBlock leftBlock) (prefixGapTrace gap)
        (MoreTransitions (beginTransition (blockOpening rightBlock)) NoTransitions)))

||| Convert a quantified boundary inequality into FULL physical BlockBefore
||| for two located blocks of ONE actual trace. Actual structural prefixes
||| derive the dependent gap/equation; no count-to-prefix injectivity premise.
export
0 o19BlockBeforeByCount :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {leftActor, rightActor : name} ->
  {initial, finalState : SystemState name key value world error} -> (source : Transitions initial finalState) ->
  (leftBlock : LocatedOpenEpisodeBlock name key world error value nameEq keyEq leftActor source) ->
  (rightBlock : LocatedOpenEpisodeBlock name key world error value nameEq keyEq rightActor source) ->
  LTE (transitionCount (prefixThroughBlock leftBlock)) (transitionCount (traceBeforeBlock rightBlock)) ->
  BlockBefore name key world error value nameEq keyEq source leftActor rightActor leftBlock rightBlock
o19BlockBeforeByCount source leftBlock rightBlock bound =
  o19BlockBeforeFromGap source leftBlock rightBlock
    (o19PrefixGapByCount (prefixThroughBlock leftBlock) (traceBeforeBlock rightBlock) source
      (fst (o19LocatedBlockPrefixes leftBlock)) (snd (o19LocatedBlockPrefixes rightBlock)) bound)

||| Two blocks of the SAME actor cannot be ordered in one actual trace:
||| the earlier real Begin would violate the later block's no-earlier law.
export
0 o19BlockBeforeNotSame : {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> {selected : name} ->
  {initial, finalState : SystemState name key value world error} -> {source : Transitions initial finalState} ->
  (first, second : LocatedOpenEpisodeBlock name key world error value nameEq keyEq selected source) ->
  Not (BlockBefore name key world error value nameEq keyEq source selected selected first second)
o19BlockBeforeNotSame {selected} first second ordered =
  o19NoLifecycleWordMember selected (traceBeforeBlock second) (noEarlierLifecycle second) (LBegin selected)
    (replace {p = Elem (LBegin selected)} (sym (o19OrderedBeforeWord first second ordered))
      (fst (o19ElemAppendInjections (o19ActionWord (prefixThroughBlock first)) (o19ActionWord (betweenBlocks ordered)))
        (replace {p = Elem (LBegin selected)} (sym (o19PrefixThroughWord first))
          (snd (o19ElemAppendInjections (o19ActionWord (traceBeforeBlock first)) (o19ActionWord (actorBlockTrace first))) Here))))
    Refl Refl

||| Both exact enumeration members from an actual BeforeIn witness.
export
0 o19BeforeMembers : {name : Type} -> {left, right : name} -> {order : List name} ->
  BeforeIn left right order -> (Elem left order, Elem right order)
o19BeforeMembers (BeforeHere member) = (Here, There member)
o19BeforeMembers (BeforeThere ordered) =
  (There (fst (o19BeforeMembers ordered)), There (snd (o19BeforeMembers ordered)))

||| Irreflexivity of actual finite order implies a unique enumeration.
export
0 o19UniqueFromNoSelfBefore : {name : Type} -> (order : List name) ->
  ((selected : name) -> Not (BeforeIn selected selected order)) -> UniqueKeys order
o19UniqueFromNoSelfBefore [] noSelf = UniqueNil
o19UniqueFromNoSelfBefore (head :: rest) noSelf =
  UniqueCons (\member => noSelf head (BeforeHere member))
    (o19UniqueFromNoSelfBefore rest (\selected, ordered => noSelf selected (BeforeThere ordered)))

||| Uniqueness is DERIVED from the original decomposition, not added as
||| an O19 safety premise: repeated actors would have two ordered episodes.
export
0 o19DecomposedOrderUnique : {name, key, world, error : Type} -> {value : key -> Type} ->
  {nameEq : DecEq name} -> {keyEq : DecEq key} -> (order : List name) ->
  {initial, finalState : SystemState name key value world error} -> {source : Transitions initial finalState} ->
  ActorBlockDecomposition name key world error value nameEq keyEq order source -> UniqueKeys order
o19DecomposedOrderUnique order blocks =
  o19UniqueFromNoSelfBefore order (\selected, ordered =>
    o19BlockBeforeNotSame (decomposedBlock blocks selected (fst (o19BeforeMembers ordered)))
      (decomposedBlock blocks selected (snd (o19BeforeMembers ordered)))
      (decomposedBlocksFollowOrder blocks selected selected (fst (o19BeforeMembers ordered)) (snd (o19BeforeMembers ordered)) ordered))

||| Exact finite actor-list membership under a selected pair transposition.
||| This is enumeration membership, NOT action/external correspondence.
export
0 o19SwapTailMember : {name : Type} -> {left, right, selected : name} -> {trailing : List name} ->
  Elem selected (right :: left :: trailing) -> Elem selected (left :: right :: trailing)
o19SwapTailMember Here = There Here
o19SwapTailMember (There Here) = Here
o19SwapTailMember (There (There member)) = There (There member)

||| Typed absence observation for the new head of a transposed unique pair.
export
0 o19SwapTailAbsent : {name : Type} -> {left, right : name} -> {trailing : List name} ->
  Not (Elem left (right :: trailing)) -> Not (Elem right trailing) -> Not (Elem right (left :: trailing))
o19SwapTailAbsent absentLeft absentRight Here = absentLeft Here
o19SwapTailAbsent absentLeft absentRight (There member) = absentRight member

||| A transposed unique pair remains unique, without a new distinctness axiom.
export
0 o19SwapTailUnique : {name : Type} -> {left, right : name} -> {trailing : List name} ->
  UniqueKeys (left :: right :: trailing) -> UniqueKeys (right :: left :: trailing)
o19SwapTailUnique (UniqueCons absentLeft (UniqueCons absentRight unique)) =
  UniqueCons (o19SwapTailAbsent absentLeft absentRight)
    (UniqueCons (\member => absentLeft (There member)) unique)

||| Preserve the exact leading enumeration while transposing its unique
||| adjacent pair. Prefix-head absence is transported by actual membership.
export
0 o19SwapLeadingUnique : {name : Type} -> (leading : List name) -> (left, right : name) -> (trailing : List name) ->
  UniqueKeys (leading ++ (left :: right :: trailing)) -> UniqueKeys (leading ++ (right :: left :: trailing))
o19SwapLeadingUnique [] left right trailing unique = o19SwapTailUnique unique
o19SwapLeadingUnique (head :: rest) left right trailing (UniqueCons absent unique) =
  UniqueCons (\member => absent
    (o19ElemAppendCases rest (right :: left :: trailing)
      (fst (o19ElemAppendInjections rest (left :: right :: trailing)))
      (\tailMember => snd (o19ElemAppendInjections rest (left :: right :: trailing)) (o19SwapTailMember tailMember)) member))
    (o19SwapLeadingUnique rest left right trailing unique)

||| ACTUAL target-order uniqueness, derived from the original blocks and
||| exact adjacent transposition. No target uniqueness premise is assumed.
export
0 o19ActualTargetUnique :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (protocol : RegistrationProtocol key value world error) ->
  {sourceOrder, targetOrder : List name} -> (swap : AdjacentActorOrderSwap name sourceOrder targetOrder) ->
  {initial, sourceFinal : SystemState name key value world error} -> (source : Transitions initial sourceFinal) ->
  (blocks : ActorBlockDecomposition name key world error value nameEq keyEq sourceOrder source) ->
  (premises : ReplayInvariantBundle name key world error value protocol nameEq keyEq source) ->
  (safety : AdjacentActorSwapSafety name key world error value protocol nameEq keyEq swap source blocks premises) ->
  (unique : UniqueRawNameInsertions name key world error value nameEq keyEq source) ->
  UniqueKeys targetOrder
o19ActualTargetUnique {sourceOrder} nameEq keyEq protocol swap source blocks premises safety unique =
  replace {p = UniqueKeys} (sym (actorAfterExact swap))
    (o19SwapLeadingUnique (actorPrefix swap) (actorLeft swap) (actorRight swap) (actorSuffix swap)
      (replace {p = UniqueKeys} (actorBeforeExact swap) (o19DecomposedOrderUnique sourceOrder blocks)))

||| OWN word observations of the direct single-constructor segment producer.
||| The prefix is its explicit earlier argument; the body word is the explicit
||| range witness. No scalar observer evaluates a nested replay/cut builder.
export
0 o19LocatedFromSegmentsWords :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {initial, sourceFinal, targetFinal, before, rangeEnd : SystemState name key value world error} ->
  (source : Transitions initial sourceFinal) ->
  (block : LocatedOpenEpisodeBlock name key world error value nameEq keyEq selected source) ->
  (target : Transitions initial targetFinal) ->
  (origins : ActionRegistrationReplayCorrespondence name key world error value source target) ->
  (earlier : Transitions initial before) -> (middle : Transitions before rangeEnd) -> (later : Transitions rangeEnd targetFinal) ->
  (decomposition : appendTransitions earlier (appendTransitions middle later) = target) ->
  (range : O19BeginRange name key world error value nameEq keyEq selected middle (o19ActionWord (blockBody block))) ->
  (noEarlier : NoLifecycleBy selected earlier) -> (noLater : NoLifecycleBy selected later) ->
  (active : supportedActiveAt {name} {key} {value} {world} {error} @{nameEq} selected targetFinal = True) ->
  (o19ActionWord (traceBeforeBlock (o19LocatedFromActualSegments nameEq keyEq selected source block target origins earlier middle later decomposition range noEarlier noLater active)) = o19ActionWord earlier,
   o19ActionWord (actorBlockTrace (o19LocatedFromActualSegments nameEq keyEq selected source block target origins earlier middle later decomposition range noEarlier noLater active)) = o19ActionWord (actorBlockTrace block))
o19LocatedFromSegmentsWords nameEq keyEq selected source block target origins earlier middle later decomposition range noEarlier noLater active = (Refl, cong (LBegin selected ::) (rangeBodyWord range))

||| Typed OWN-cut observation: the constructed block starts at the actual
||| first cut and retains the source block word, via its explicit Begin range.
export
0 o19LocatedFromWordCutsWords :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {initial, sourceFinal, targetFinal : SystemState name key value world error} ->
  (source : Transitions initial sourceFinal) ->
  (block : LocatedOpenEpisodeBlock name key world error value nameEq keyEq selected source) ->
  (target : Transitions initial targetFinal) ->
  (aligned : AlignedTransitions name key world error value nameEq keyEq target) ->
  (origins : ActionRegistrationReplayCorrespondence name key world error value source target) ->
  (active : supportedActiveAt {name} {key} {value} {world} {error} @{nameEq} selected targetFinal = True) ->
  (beforeWord, afterWord : List (Action name key value world error)) ->
  (noEarlier : (action : Action name key value world error) -> Elem action beforeWord ->
    (isLifecycleAction action = True) -> Not (actionOwner action = selected)) ->
  (noLater : (action : Action name key value world error) -> Elem action afterWord ->
    (isLifecycleAction action = True) -> Not (actionOwner action = selected)) ->
  (firstCut : O19WordCut name key world error value beforeWord (o19ActionWord (actorBlockTrace block) ++ afterWord) target) ->
  (secondCut : O19WordCut name key world error value (o19ActionWord (actorBlockTrace block)) afterWord (cutSuffix firstCut)) ->
  (o19ActionWord (traceBeforeBlock (o19LocatedFromWordCuts nameEq keyEq selected source block target aligned origins active beforeWord afterWord noEarlier noLater firstCut secondCut)) = beforeWord,
   o19ActionWord (actorBlockTrace (o19LocatedFromWordCuts nameEq keyEq selected source block target aligned origins active beforeWord afterWord noEarlier noLater firstCut secondCut)) = o19ActionWord (actorBlockTrace block))
o19LocatedFromWordCutsWords nameEq keyEq selected source block target aligned origins active beforeWord afterWord noEarlier noLater firstCut secondCut =
  (trans (fst (o19LocatedFromSegmentsWords nameEq keyEq selected source block target origins
    (cutPrefix firstCut) (cutPrefix secondCut) (cutSuffix secondCut)
    (trans (cong (appendTransitions (cutPrefix firstCut)) (cutDecomposition secondCut)) (cutDecomposition firstCut))
    (o19BeginRangeObserved nameEq keyEq selected (cutPrefix secondCut) (o19ActionWord (blockBody block))
      (fst (alignedAppendSplit (cutPrefix secondCut) (cutSuffix secondCut)
        (replace {p = AlignedTransitions name key world error value nameEq keyEq} (sym (cutDecomposition secondCut))
          (snd (alignedAppendSplit (cutPrefix firstCut) (cutSuffix firstCut)
            (replace {p = AlignedTransitions name key world error value nameEq keyEq} (sym (cutDecomposition firstCut)) aligned))))))
      (cutLeftWord secondCut))
    (o19NoLifecycleFromWord selected (cutPrefix firstCut)
      (\action, member => noEarlier action (replace {p = Elem action} (cutLeftWord firstCut) member)))
    (o19NoLifecycleFromWord selected (cutSuffix secondCut)
      (\action, member => noLater action (replace {p = Elem action} (cutRightWord secondCut) member))) active)) (cutLeftWord firstCut),
   snd (o19LocatedFromSegmentsWords nameEq keyEq selected source block target origins
    (cutPrefix firstCut) (cutPrefix secondCut) (cutSuffix secondCut)
    (trans (cong (appendTransitions (cutPrefix firstCut)) (cutDecomposition secondCut)) (cutDecomposition firstCut))
    (o19BeginRangeObserved nameEq keyEq selected (cutPrefix secondCut) (o19ActionWord (blockBody block))
      (fst (alignedAppendSplit (cutPrefix secondCut) (cutSuffix secondCut)
        (replace {p = AlignedTransitions name key world error value nameEq keyEq} (sym (cutDecomposition secondCut))
          (snd (alignedAppendSplit (cutPrefix firstCut) (cutSuffix firstCut)
            (replace {p = AlignedTransitions name key world error value nameEq keyEq} (sym (cutDecomposition firstCut)) aligned))))))
      (cutLeftWord secondCut))
    (o19NoLifecycleFromWord selected (cutPrefix firstCut)
      (\action, member => noEarlier action (replace {p = Elem action} (cutLeftWord firstCut) member)))
    (o19NoLifecycleFromWord selected (cutSuffix secondCut)
      (\action, member => noLater action (replace {p = Elem action} (cutRightWord secondCut) member))) active))

||| Transport OWN word metadata through the constructed second cut,
||| using only the first cut's residual equation and the typed cut observer.
export
0 o19LocatedAfterFirstCutWords :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {initial, sourceFinal, targetFinal : SystemState name key value world error} ->
  (source : Transitions initial sourceFinal) ->
  (block : LocatedOpenEpisodeBlock name key world error value nameEq keyEq selected source) ->
  (target : Transitions initial targetFinal) ->
  (aligned : AlignedTransitions name key world error value nameEq keyEq target) ->
  (origins : ActionRegistrationReplayCorrespondence name key world error value source target) ->
  (active : supportedActiveAt {name} {key} {value} {world} {error} @{nameEq} selected targetFinal = True) ->
  (beforeWord, afterWord : List (Action name key value world error)) ->
  (noEarlier : (action : Action name key value world error) -> Elem action beforeWord ->
    (isLifecycleAction action = True) -> Not (actionOwner action = selected)) ->
  (noLater : (action : Action name key value world error) -> Elem action afterWord ->
    (isLifecycleAction action = True) -> Not (actionOwner action = selected)) ->
  (firstCut : O19WordCut name key world error value beforeWord (o19ActionWord (actorBlockTrace block) ++ afterWord) target) ->
  (o19ActionWord (traceBeforeBlock (o19LocatedAfterFirstCut nameEq keyEq selected source block target aligned origins active beforeWord afterWord noEarlier noLater firstCut)) = beforeWord,
   o19ActionWord (actorBlockTrace (o19LocatedAfterFirstCut nameEq keyEq selected source block target aligned origins active beforeWord afterWord noEarlier noLater firstCut)) = o19ActionWord (actorBlockTrace block))
o19LocatedAfterFirstCutWords nameEq keyEq selected source block target aligned origins active beforeWord afterWord noEarlier noLater firstCut =
  o19LocatedFromWordCutsWords nameEq keyEq selected source block target aligned origins active beforeWord afterWord noEarlier noLater firstCut
    (o19CutByWord (o19ActionWord (actorBlockTrace block)) afterWord (cutSuffix firstCut) (cutRightWord firstCut))

||| FULL constructed reached block retains its exact prefix and original
||| whole block word. All metadata comes through OWN typed cut observations.
export
0 o19LocatedByWordWords :
  {name, key, world, error : Type} -> {value : key -> Type} ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {initial, sourceFinal, targetFinal : SystemState name key value world error} ->
  (source : Transitions initial sourceFinal) ->
  (block : LocatedOpenEpisodeBlock name key world error value nameEq keyEq selected source) ->
  (target : Transitions initial targetFinal) ->
  (aligned : AlignedTransitions name key world error value nameEq keyEq target) ->
  (origins : ActionRegistrationReplayCorrespondence name key world error value source target) ->
  (active : supportedActiveAt {name} {key} {value} {world} {error} @{nameEq} selected targetFinal = True) ->
  (beforeWord, afterWord : List (Action name key value world error)) ->
  (noEarlier : (action : Action name key value world error) -> Elem action beforeWord ->
    (isLifecycleAction action = True) -> Not (actionOwner action = selected)) ->
  (noLater : (action : Action name key value world error) -> Elem action afterWord ->
    (isLifecycleAction action = True) -> Not (actionOwner action = selected)) ->
  (placement : o19ActionWord target = beforeWord ++ (o19ActionWord (actorBlockTrace block) ++ afterWord)) ->
  (o19ActionWord (traceBeforeBlock (o19LocatedByWord nameEq keyEq selected source block target aligned origins active beforeWord afterWord noEarlier noLater placement)) = beforeWord,
   o19ActionWord (actorBlockTrace (o19LocatedByWord nameEq keyEq selected source block target aligned origins active beforeWord afterWord noEarlier noLater placement)) = o19ActionWord (actorBlockTrace block))
o19LocatedByWordWords nameEq keyEq selected source block target aligned origins active beforeWord afterWord noEarlier noLater placement =
  o19LocatedAfterFirstCutWords nameEq keyEq selected source block target aligned origins active beforeWord afterWord noEarlier noLater
    (o19CutByWord beforeWord (o19ActionWord (actorBlockTrace block) ++ afterWord) target placement)
