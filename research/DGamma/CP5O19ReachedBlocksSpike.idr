module DGamma.CP5O19ReachedBlocksSpike

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5UniqueRawNameInsertions
import DGamma.CP5ConfluenceLocalDiamondSpike
import DGamma.CP5ConfluenceCrossTraceSpike
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
