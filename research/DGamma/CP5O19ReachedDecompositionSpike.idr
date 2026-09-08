module DGamma.CP5O19ReachedDecompositionSpike

import DGamma.CP5O19ReachedBlocksSpike
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

||| Ordered half-open numeric ranges cannot share a position. The upper
||| boundary is supplied by genuine BlockBefore in the next lemma.
export
0 o19OrderedRangeSeparation :
  (earlyStart, earlySize, lateStart, earlyPosition, latePosition : Nat) ->
  LTE (earlyStart + earlySize) lateStart ->
  LTE (S earlyPosition) earlySize ->
  Not ((earlyStart + earlyPosition) = (lateStart + latePosition))
o19OrderedRangeSeparation earlyStart earlySize lateStart earlyPosition latePosition ordered bounded exact =
  succNotLTEpred
    (replace {p = LTE (S (earlyStart + earlyPosition))} (sym exact)
      (transitive
        (replace {p = \count => LTE count (earlyStart + earlySize)}
          (sym (plusSuccRightSucc earlyStart earlyPosition))
          (plusLteMonotoneLeft earlyStart (S earlyPosition) earlySize bounded))
        (transitive ordered (lteAddRight lateStart))))
