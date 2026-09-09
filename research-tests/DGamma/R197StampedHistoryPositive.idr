module DGamma.R197StampedHistoryPositive

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

import DGamma.CP5O20StampedHistoryFoldSpike
import DGamma.CP5O20HistoryNameTransportSpike

%default total
%unbound_implicits off

||| All eleven actual R191 native edges instantiate the stamped family, with
||| root stamps0/1/2 and generated child stamp4. No canonical decomposition
||| or universal stage synchronization is claimed by this identity fixture.
public export
0 r197StampedElevenRun :
  O20StampedHistory Nat R45Key Unit String R45Value r45NameEq r45KeyEq
    identityRegistrationGenerationBijection identityNameBijection 0 0 [] []
    [(0, MkRegistrationGeneration 0 0), (1, MkRegistrationGeneration 1 1), (2, MkRegistrationGeneration 2 2), (3, MkRegistrationGeneration 3 4)]
    [(0, MkRegistrationGeneration 0 0), (1, MkRegistrationGeneration 1 1), (2, MkRegistrationGeneration 2 2), (3, MkRegistrationGeneration 3 4)]
    (r191ChildGapState 0) (r191ChildGapState 0) (r191ChildGapState 11) (r191ChildGapState 11)
r197StampedElevenRun =
  (StampedHistoryMore {leftMiddle = r191ChildGapState 1} {rightMiddle = r191ChildGapState 1}
    (StampedInsertStage r45NameEq r45KeyEq identityNameBijection 0 r45Parent Root Root RootsRelated () () (registry (r191ChildGapState 0)) (registry (r191ChildGapState 0)) Refl Refl Refl Refl Refl)
    (StampedHistoryMore {leftMiddle = r191ChildGapState 2} {rightMiddle = r191ChildGapState 2}
    (StampedInsertStage r45NameEq r45KeyEq identityNameBijection 1 r45Child Root Root RootsRelated () () (registry (r191ChildGapState 1)) (registry (r191ChildGapState 1)) Refl Refl Refl Refl Refl)
    (StampedHistoryMore {leftMiddle = r191ChildGapState 3} {rightMiddle = r191ChildGapState 3}
    (StampedInsertStage r45NameEq r45KeyEq identityNameBijection 2 r45Child Root Root RootsRelated () () (registry (r191ChildGapState 2)) (registry (r191ChildGapState 2)) Refl Refl Refl Refl Refl)
    (StampedHistoryMore {leftMiddle = r191ChildGapState 4} {rightMiddle = r191ChildGapState 4}
    (StampedBeginStage r45NameEq r45KeyEq identityNameBijection 0 (r191ChildGapState 3) (r191ChildGapState 4) (r191ChildGapState 3) (r191ChildGapState 4) (MkBeginStep Refl) (MkBeginStep Refl) Refl)
    (StampedHistoryMore {leftMiddle = r191ChildGapState 5} {rightMiddle = r191ChildGapState 5}
    (StampedInsertStage r45NameEq r45KeyEq identityNameBijection 3 r45Child (ChildOf 0) (ChildOf 0) (ChildrenRelated Refl) () () (registry (r191ChildGapState 4)) (registry (r191ChildGapState 4)) Refl Refl Refl Refl Refl)
    (StampedHistoryMore {leftMiddle = r191ChildGapState 6} {rightMiddle = r191ChildGapState 6}
    (StampedAdvanceStage r45NameEq r45KeyEq identityNameBijection 0 r45Parent r45YieldingStep [] Root Root False False emptyOwned emptyOwned id id EmptyView EmptyView () () (registry (r191ChildGapState 5)) (registry (r191ChildGapState 5)) (MkLocalState () (restrictOwnedPreservingOrder @{r45KeyEq} r45Spec emptyContext)) (MkLocalState () (restrictOwnedPreservingOrder @{r45KeyEq} r45Spec emptyContext)) id id NoDepValues NoDepValues LFinishTag LFinishTag Refl Refl Refl Refl Refl Refl Refl Refl)
    (StampedHistoryMore {leftMiddle = r191ChildGapState 7} {rightMiddle = r191ChildGapState 7}
    (StampedBeginStage r45NameEq r45KeyEq identityNameBijection 1 (r191ChildGapState 6) (r191ChildGapState 7) (r191ChildGapState 6) (r191ChildGapState 7) (MkBeginStep Refl) (MkBeginStep Refl) Refl)
    (StampedHistoryMore {leftMiddle = r191ChildGapState 8} {rightMiddle = r191ChildGapState 8}
    (StampedEmptyFinishStage r45NameEq r45KeyEq identityNameBijection 1 r45Child Root Root False False emptyOwned emptyOwned id id EmptyView EmptyView () () (registry (r191ChildGapState 7)) (registry (r191ChildGapState 7)) Refl Refl Refl Refl)
    (StampedHistoryMore {leftMiddle = r191ChildGapState 9} {rightMiddle = r191ChildGapState 9}
    (StampedRetireStage r45NameEq r45KeyEq identityNameBijection 3 () () (registry (r191ChildGapState 8)) (registry (r191ChildGapState 8)) r45ChildFresh r45ChildFresh Refl Refl Refl Refl)
    (StampedHistoryMore {leftMiddle = r191ChildGapState 10} {rightMiddle = r191ChildGapState 10}
    (StampedBeginStage r45NameEq r45KeyEq identityNameBijection 2 (r191ChildGapState 9) (r191ChildGapState 10) (r191ChildGapState 9) (r191ChildGapState 10) (MkBeginStep Refl) (MkBeginStep Refl) Refl)
    (StampedHistoryMore {leftMiddle = r191ChildGapState 11} {rightMiddle = r191ChildGapState 11}
    (StampedEmptyFinishStage r45NameEq r45KeyEq identityNameBijection 2 r45Child Root Root False False emptyOwned emptyOwned id id EmptyView EmptyView () () (registry (r191ChildGapState 10)) (registry (r191ChildGapState 10)) Refl Refl Refl Refl)
    StampedHistoryEnd)))))))))))

||| The conditional fold runs from the literal empty R191 origin and returns
||| all three history-cut fields at its actual eleven-edge endpoint. This is
||| not an assumed endpoint relation or a canonical decomposition fixture.
export
0 r197StampedElevenEndpoint :
  O20HistoryCut Nat R45Key Unit String R45Value r45NameEq identityRegistrationGenerationBijection
    [(0, MkRegistrationGeneration 0 0), (1, MkRegistrationGeneration 1 1), (2, MkRegistrationGeneration 2 2), (3, MkRegistrationGeneration 3 4)]
    [(0, MkRegistrationGeneration 0 0), (1, MkRegistrationGeneration 1 1), (2, MkRegistrationGeneration 2 2), (3, MkRegistrationGeneration 3 4)]
    (r191ChildGapState 11) (r191ChildGapState 11)
r197StampedElevenEndpoint =
  o20StampedHistoryCut r197StampedElevenRun
    (MkO20StampedCut
      (o20AllNameEmptyOrigin r45NameEq identityNameBijection (r191ChildGapState 0) Refl)
      (\selected, stamp, found => absurd found) (\selected, stamp, found => absurd found))
