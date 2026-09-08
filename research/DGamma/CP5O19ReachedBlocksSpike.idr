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
