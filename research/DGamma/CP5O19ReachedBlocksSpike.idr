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
