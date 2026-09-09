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
