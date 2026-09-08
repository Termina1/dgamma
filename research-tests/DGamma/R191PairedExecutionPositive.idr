module DGamma.R191PairedExecutionPositive

import DGamma.Core
import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5O19SurfaceSpike
import DGamma.CP5O20AllNameSynchronizationSpike
import DGamma.CP5O20PairedAdvanceSpike
import DGamma.CP5O20PairedExecutionSpike
import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import DGamma.R191CanonicalChildRetirementGap
import Data.List
import Data.Maybe
import Decidable.Equality

%default total
%unbound_implicits off

||| The SAME eleven physical cuts as the retained child-retirement candidate,
||| now as two native paired executions. All five stage constructors occur:
||| root/child inserts, general Begin, successful last-step Advance, empty
||| Finish and the intervening child retirement. This is NOT an accepted
||| canonical schedule/decomposition and is not a new attempt at exhausted F7.
public export
0 r191PairedChildRetirementRun :
  O20PairedExecution Nat R45Key Unit String R45Value r45NameEq r45KeyEq identityNameBijection
    (r191ChildGapState 0) (r191ChildGapState 0) (r191ChildGapState 11) (r191ChildGapState 11)
r191PairedChildRetirementRun =
  (PairedExecutionMore {leftMiddle = r191ChildGapState 1} {rightMiddle = r191ChildGapState 1}
    (PairedInsertStage r45NameEq r45KeyEq identityNameBijection 0 r45Parent Root Root RootsRelated () () (registry (r191ChildGapState 0)) (registry (r191ChildGapState 0)) Refl Refl Refl Refl)
    (PairedExecutionMore {leftMiddle = r191ChildGapState 2} {rightMiddle = r191ChildGapState 2}
    (PairedInsertStage r45NameEq r45KeyEq identityNameBijection 1 r45Child Root Root RootsRelated () () (registry (r191ChildGapState 1)) (registry (r191ChildGapState 1)) Refl Refl Refl Refl)
    (PairedExecutionMore {leftMiddle = r191ChildGapState 3} {rightMiddle = r191ChildGapState 3}
    (PairedInsertStage r45NameEq r45KeyEq identityNameBijection 2 r45Child Root Root RootsRelated () () (registry (r191ChildGapState 2)) (registry (r191ChildGapState 2)) Refl Refl Refl Refl)
    (PairedExecutionMore {leftMiddle = r191ChildGapState 4} {rightMiddle = r191ChildGapState 4}
    (PairedBeginStage r45NameEq r45KeyEq identityNameBijection 0 (r191ChildGapState 3) (r191ChildGapState 4) (r191ChildGapState 3) (r191ChildGapState 4) (MkBeginStep Refl) (MkBeginStep Refl) Refl)
    (PairedExecutionMore {leftMiddle = r191ChildGapState 5} {rightMiddle = r191ChildGapState 5}
    (PairedInsertStage r45NameEq r45KeyEq identityNameBijection 3 r45Child (ChildOf 0) (ChildOf 0) (ChildrenRelated Refl) () () (registry (r191ChildGapState 4)) (registry (r191ChildGapState 4)) Refl Refl Refl Refl)
    (PairedExecutionMore {leftMiddle = r191ChildGapState 6} {rightMiddle = r191ChildGapState 6}
    (PairedAdvanceStage r45NameEq r45KeyEq identityNameBijection 0 r45Parent r45YieldingStep [] Root Root False False emptyOwned emptyOwned id id EmptyView EmptyView () () (registry (r191ChildGapState 5)) (registry (r191ChildGapState 5)) (MkLocalState () (restrictOwnedPreservingOrder @{r45KeyEq} r45Spec emptyContext)) (MkLocalState () (restrictOwnedPreservingOrder @{r45KeyEq} r45Spec emptyContext)) id id NoDepValues NoDepValues LFinishTag LFinishTag Refl Refl Refl Refl Refl Refl Refl Refl)
    (PairedExecutionMore {leftMiddle = r191ChildGapState 7} {rightMiddle = r191ChildGapState 7}
    (PairedBeginStage r45NameEq r45KeyEq identityNameBijection 1 (r191ChildGapState 6) (r191ChildGapState 7) (r191ChildGapState 6) (r191ChildGapState 7) (MkBeginStep Refl) (MkBeginStep Refl) Refl)
    (PairedExecutionMore {leftMiddle = r191ChildGapState 8} {rightMiddle = r191ChildGapState 8}
    (PairedEmptyFinishStage r45NameEq r45KeyEq identityNameBijection 1 r45Child Root Root False False emptyOwned emptyOwned id id EmptyView EmptyView () () (registry (r191ChildGapState 7)) (registry (r191ChildGapState 7)) Refl Refl Refl Refl)
    (PairedExecutionMore {leftMiddle = r191ChildGapState 9} {rightMiddle = r191ChildGapState 9}
    (PairedRetireStage r45NameEq r45KeyEq identityNameBijection 3 () () (registry (r191ChildGapState 8)) (registry (r191ChildGapState 8)) r45ChildFresh r45ChildFresh Refl Refl Refl Refl)
    (PairedExecutionMore {leftMiddle = r191ChildGapState 10} {rightMiddle = r191ChildGapState 10}
    (PairedBeginStage r45NameEq r45KeyEq identityNameBijection 2 (r191ChildGapState 9) (r191ChildGapState 10) (r191ChildGapState 9) (r191ChildGapState 10) (MkBeginStep Refl) (MkBeginStep Refl) Refl)
    (PairedExecutionMore {leftMiddle = r191ChildGapState 11} {rightMiddle = r191ChildGapState 11}
    (PairedEmptyFinishStage r45NameEq r45KeyEq identityNameBijection 2 r45Child Root Root False False emptyOwned emptyOwned id id EmptyView EmptyView () () (registry (r191ChildGapState 10)) (registry (r191ChildGapState 10)) Refl Refl Refl Refl)
    PairedExecutionDone)))))))))))

||| End-to-end producer packet: BOTH full physical traces and the ALL-NAME
||| endpoint cut come from this run and its genuine empty origin. No endpoint
||| relation, callback equality or table/control oracle is a fixture premise.
export
0 r191PairedRunProducesEndpoint :
  (Transitions (r191ChildGapState 0) (r191ChildGapState 11),
   Transitions (r191ChildGapState 0) (r191ChildGapState 11),
   O20AllNameCut Nat R45Key Unit String R45Value r45NameEq identityNameBijection
     (r191ChildGapState 11) (r191ChildGapState 11))
r191PairedRunProducesEndpoint =
  case o20PairedExecutionTraces r191PairedChildRetirementRun of
    (leftTrace, rightTrace) => (leftTrace, rightTrace,
      o20PairedExecutionCut r45NameEq r45KeyEq identityNameBijection r191PairedChildRetirementRun
        (o20AllNameEmptyOrigin r45NameEq identityNameBijection (r191ChildGapState 0) Refl))
