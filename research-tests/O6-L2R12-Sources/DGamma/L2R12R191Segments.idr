module DGamma.L2R12R191Segments

import Prelude.Types
import Prelude.Interfaces
import Prelude.Basics
import Prelude.Num
import Prelude.EqOrd
import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4RuntimeBindings
import DGamma.CP5L2R1ChildRelocation
import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import DGamma.R191CanonicalChildRetirementGap
import DGamma.L2R11WordInventory
import Data.List
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality
import Decidable.Equality.Core
import Decidable.Decidable

%default total
%unbound_implicits off

||| Native factorization of the ACTUAL R191 source into prefix, foreign
||| actor1 span, Retire3 and suffix. Fields authenticate provenance, not a
||| replay oracle. The producer must construct all data/equations together.
public export
record R191RetirementSegments where
  constructor MkR191RetirementSegments
  r191Prefix : Transitions (r191ChildGapState 0) (r191ChildGapState 6)
  r191Span : Transitions (r191ChildGapState 6) (r191ChildGapState 8)
  0 r191Foreign : ForeignChildRun r45NameEq r45KeyEq 3 r191Span
  r191Suffix : Transitions (r191ChildGapState 9) (r191ChildGapState 11)
  0 r191SuffixAligned : AlignedTransitions Nat R45Key Unit String R45Value r45NameEq r45KeyEq r191Suffix
  0 r191PrefixCount : transitionCount r191Prefix = 6
  0 r191SpanCount : transitionCount r191Span = 2
  0 r191SuffixCount : transitionCount r191Suffix = 2
  0 r191PhysicalSplit : appendTransitions r191Prefix (appendTransitions r191Span
    (MoreTransitions (Fired {before = r191ChildGapState 8} {afterState = r191ChildGapState 9}
      r45NameEq r45KeyEq (ORetire 3) ORetireTag (nativeCheckedAt 8 r191ChildGapTrace)) r191Suffix)) = r191ChildGapTrace
  0 r191SourceValid : registryWellFormed @{r45NameEq} @{r45KeyEq} (r191ChildGapState 6) = True
  0 r191ChildFound : lookupFiber {name = Nat} {key = R45Key} {value = R45Value} {world = Unit} {error = String}
    @{r45NameEq} 3 (registry (r191ChildGapState 8)) = Just r45ChildFresh
  0 r191OwnChild : fiberParent r45ChildFresh = ChildOf 0
  0 r191SpanRestricted : all (\code => not (wordActionInventory (replayActionWord r191Span) code) ||
    elemDec code [0, 1, 2, 3, 4]) [0, 1, 2, 3, 4, 5, 6, 7] = True
  0 r191RetirementSnapshot : runtimeSnapshot
    (MkSystemState (worldState (r191ChildGapState 8))
      (replaceBinding @{r45NameEq} 3 (retireFiber r45ChildFresh) (registry (r191ChildGapState 8)))) =
    runtimeSnapshot (r191ChildGapState 9)

||| Simultaneously decode the ACTUAL source prefix/span/suffix, child3's
||| own-parent provenance, finite inventory and native retirement endpoint.
||| No previous relocated trace or local exchange fixture is projected.
public export
r191RetirementSegments : R191RetirementSegments
r191RetirementSegments = MkR191RetirementSegments
  (MoreTransitions (Fired {before = r191ChildGapState 0} {afterState = r191ChildGapState 1} r45NameEq r45KeyEq (OInsert 0 Root r45Parent) OInsertTag (nativeCheckedAt 0 r191ChildGapTrace)) (MoreTransitions (Fired {before = r191ChildGapState 1} {afterState = r191ChildGapState 2} r45NameEq r45KeyEq (OInsert 1 Root r45Child) OInsertTag (nativeCheckedAt 1 r191ChildGapTrace)) (MoreTransitions (Fired {before = r191ChildGapState 2} {afterState = r191ChildGapState 3} r45NameEq r45KeyEq (OInsert 2 Root r45Child) OInsertTag (nativeCheckedAt 2 r191ChildGapTrace)) (MoreTransitions (Fired {before = r191ChildGapState 3} {afterState = r191ChildGapState 4} r45NameEq r45KeyEq (LBegin 0) LBeginTag (nativeCheckedAt 3 r191ChildGapTrace)) (MoreTransitions (Fired {before = r191ChildGapState 4} {afterState = r191ChildGapState 5} r45NameEq r45KeyEq (OInsert 3 (ChildOf 0) r45Child) OInsertTag (nativeCheckedAt 4 r191ChildGapTrace)) (MoreTransitions (Fired {before = r191ChildGapState 5} {afterState = r191ChildGapState 6} r45NameEq r45KeyEq (LAdvance 0) LFinishTag (nativeCheckedAt 5 r191ChildGapTrace)) NoTransitions))))))
  (MoreTransitions (Fired {before = r191ChildGapState 6} {afterState = r191ChildGapState 7} r45NameEq r45KeyEq (LBegin 1) LBeginTag (nativeCheckedAt 6 r191ChildGapTrace)) (MoreTransitions (Fired {before = r191ChildGapState 7} {afterState = r191ChildGapState 8} r45NameEq r45KeyEq (LAdvance 1) LFinishTag (nativeCheckedAt 7 r191ChildGapTrace)) NoTransitions))
  (ForeignChildStep {child = 3} (LBegin 1) LBeginTag (nativeCheckedAt 6 r191ChildGapTrace) (MoreTransitions (Fired {before = r191ChildGapState 7} {afterState = r191ChildGapState 8} r45NameEq r45KeyEq (LAdvance 1) LFinishTag (nativeCheckedAt 7 r191ChildGapTrace)) NoTransitions) (\same => SIsNotZ {x = 1} (cong pred same)) (ForeignChildStep {child = 3} (LAdvance 1) LFinishTag (nativeCheckedAt 7 r191ChildGapTrace) NoTransitions (\same => SIsNotZ {x = 1} (cong pred same)) ForeignChildEnd))
  (MoreTransitions (Fired {before = r191ChildGapState 9} {afterState = r191ChildGapState 10} r45NameEq r45KeyEq (LBegin 2) LBeginTag (nativeCheckedAt 9 r191ChildGapTrace)) (MoreTransitions (Fired {before = r191ChildGapState 10} {afterState = r191ChildGapState 11} r45NameEq r45KeyEq (LAdvance 2) LFinishTag (nativeCheckedAt 10 r191ChildGapTrace)) NoTransitions))
  (AlignedStep (LBegin 2) LBeginTag (nativeCheckedAt 9 r191ChildGapTrace) (MoreTransitions (Fired {before = r191ChildGapState 10} {afterState = r191ChildGapState 11} r45NameEq r45KeyEq (LAdvance 2) LFinishTag (nativeCheckedAt 10 r191ChildGapTrace)) NoTransitions) (AlignedStep (LAdvance 2) LFinishTag (nativeCheckedAt 10 r191ChildGapTrace) NoTransitions AlignedEnd))
  Refl Refl Refl Refl
  (checkedActionTargetValid r45NameEq r45KeyEq (LAdvance 0)
    (r191ChildGapState 5) (r191ChildGapState 6) LFinishTag (nativeCheckedAt 5 r191ChildGapTrace))
  Refl Refl Refl Refl
