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
