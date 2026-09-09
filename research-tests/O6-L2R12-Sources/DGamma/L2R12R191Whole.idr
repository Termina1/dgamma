module DGamma.L2R12R191Whole

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import Prelude.Num
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
import DGamma.CP5L2R1ChildRelocation
import DGamma.CP5L2R1ExtendedZeroGap
import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import DGamma.R191CanonicalChildRetirementGap
import DGamma.L2R2ForeignReplay
import DGamma.L2R11WordInventory
import DGamma.L2R12KindDispatch
import DGamma.L2R12InventoryDomain
import DGamma.L2R12ClosedFold
import DGamma.L2R12ValidWordFold
import DGamma.L2R12SnapshotSuffix
import DGamma.L2R12R191Segments
import Data.List
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| A whole native R191 replay from the common original source. Runtime
||| snapshots compare complete worlds/ordered bindings, not core endpoints.
||| Construction below must splice original prefix, folded early-retirement
||| span and natively replayed suffix, not project the old relocated fixture.
public export
record R191FoldReplay where
  constructor MkR191FoldReplay
  foldedFinal : SystemState Nat R45Key R45Value Unit String
  foldedWhole : Transitions (r191ChildGapState 0) foldedFinal
  0 foldedCount : transitionCount foldedWhole = 11
  0 foldedEndpoint : runtimeSnapshot foldedFinal = runtimeSnapshot (r191ChildGapState 11)
  0 foldedValid : registryWellFormed @{r45NameEq} @{r45KeyEq} foldedFinal = True

||| Splice a produced foreign-span replay into its AUTHENTIC source prefix
||| and a natively replayed original suffix. Endpoint validity is received
||| from the strengthened fold, not assumed of an opaque computed packet.
export
0 spliceR191FoldedSpan : (segments : R191RetirementSegments) ->
  (current : SystemState Nat R45Key R45Value Unit String) ->
  (spanRun : Transitions (MkSystemState (worldState (r191ChildGapState 6)) (replaceBinding @{r45NameEq} 3 (retireFiber r45ChildFresh) (registry (r191ChildGapState 6)))) current) ->
  (0 count : transitionCount spanRun = transitionCount (r191Span segments)) ->
  (0 same : runtimeSnapshot current = runtimeSnapshot
    (MkSystemState (worldState (r191ChildGapState 8))
      (replaceBinding @{r45NameEq} 3 (retireFiber r45ChildFresh) (registry (r191ChildGapState 8))))) ->
  (0 valid : registryWellFormed @{r45NameEq} @{r45KeyEq} current = True) -> R191FoldReplay
spliceR191FoldedSpan segments current spanRun count same valid =
  replaySnapshotSuffixCPS r45NameEq r45KeyEq (r191ChildGapState 9) (r191ChildGapState 11)
    (r191Suffix segments) (r191SuffixAligned segments) current
    (trans same (r191RetirementSnapshot segments)) valid R191FoldReplay
    (\target, suffixRun, suffixCount, endpoint, targetValid => MkR191FoldReplay target
      (appendTransitions (r191Prefix segments) (MoreTransitions (Fired {before = r191ChildGapState 6} {afterState = (MkSystemState (worldState (r191ChildGapState 6)) (replaceBinding @{r45NameEq} 3 (retireFiber r45ChildFresh) (registry (r191ChildGapState 6))))} r45NameEq r45KeyEq (ORetire 3) ORetireTag (childRetireBeforeForeignRun r45NameEq r45KeyEq 3 r45ChildFresh (r191ChildGapState 6) (r191ChildGapState 8) (r191Span segments) (r191Foreign segments) (r191ChildFound segments) (r191SourceValid segments))) (appendTransitions spanRun suffixRun)))
      (trans (extendedCountAppend (r191Prefix segments)
        (MoreTransitions (Fired {before = r191ChildGapState 6} {afterState = (MkSystemState (worldState (r191ChildGapState 6)) (replaceBinding @{r45NameEq} 3 (retireFiber r45ChildFresh) (registry (r191ChildGapState 6))))} r45NameEq r45KeyEq (ORetire 3) ORetireTag (childRetireBeforeForeignRun r45NameEq r45KeyEq 3 r45ChildFresh (r191ChildGapState 6) (r191ChildGapState 8) (r191Span segments) (r191Foreign segments) (r191ChildFound segments) (r191SourceValid segments))) (appendTransitions spanRun suffixRun)))
        (cong2 (+) (r191PrefixCount segments)
          (cong S (trans (extendedCountAppend spanRun suffixRun)
            (cong2 (+) (trans count (r191SpanCount segments))
              (trans suffixCount (r191SuffixCount segments)))))))
      endpoint targetValid)
