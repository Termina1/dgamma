module DGamma.R193VestigialHistoryTransportPositive

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4ProgressNoDeadlock
import DGamma.CP5O20HistoryNameTransportSpike
import DGamma.CP5ConfluenceDeletionChainSpike
import DGamma.CP5ConfluenceRenamingCompositionSpike
import DGamma.R45BareDiamondDisciplineCounterexamplePositive
import DGamma.R178GeneratedOrchestrationFixtures
import DGamma.R192RemovedBirthCurrentNameProbe
import Data.List.Elem
import Data.Maybe
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| The exact native parent callback result already used by R178's actual
||| checked Finish. This fixture concerns original historical endpoints, not
||| a copied placement grammar or independent canonical capital.
public export
r193HistoricalParentActive : Fiber Nat R45Key R45Value Unit String
r193HistoricalParentActive = setFiberRuntime r45ParentBegun
  (restrictOwnedPreservingOrder @{r45KeyEq} r45Spec (ownedValues (fiberTable r45ParentBegun)))
  (Active (pushLocalUndo @{r45KeyEq} r45Spec id id) EmptyView)

||| Parent retirement follows the actual already-retired child endpoint.
public export
r193HistoricalParentRetired : SystemState Nat R45Key R45Value Unit String
r193HistoricalParentRetired = MkSystemState ()
  (replaceBinding @{r45NameEq} 0 (retireFiber r193HistoricalParentActive) (registry r178RightFinal))

||| The old checked child Retire owns the source well-formedness here.
public export
r193HistoricalRetire : Transition r178RightFinal r193HistoricalParentRetired
r193HistoricalRetire = Fired r45NameEq r45KeyEq (ORetire 0) ORetireTag
  (DGamma.CP4ProgressNoDeadlock.checkedFromRaw r45NameEq r45KeyEq
    (ORetire 0) r178RightFinal r193HistoricalParentRetired ORetireTag
    (checkedTransitionTargetValid r178ChildRetire) Refl)
