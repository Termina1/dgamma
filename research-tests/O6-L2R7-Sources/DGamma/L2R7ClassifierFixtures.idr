module DGamma.L2R7ClassifierFixtures

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R2SmallStates
import DGamma.L2R2SmallExecution
import DGamma.L2R3BarrierStates
import DGamma.L2R3BarrierExecution
import DGamma.L2R5RootCatalog
import DGamma.L2R6ForcedScan
import DGamma.L2R6ForcedFixtures
import DGamma.L2R7Classifier
import Data.List
import Data.List.Elem
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Instantiations of the GENERAL correspondence producer on the exact two
||| retained full fixture trails, not new hand-supplied soundness callbacks.
public export
record ClassifierCorrespondenceFixtures where
  constructor MkClassifierCorrespondenceFixtures
  singleCorrespondence : ForcedClassificationAt Nat Bool Unit String (\key => Unit) %search %search
    (singleForcedTrail forcedClassifierFixtures) (MkRootCatalogEntry 4 3 (smallComponent True))
  barrierCorrespondence : ForcedClassificationAt Nat Bool Unit String (\key => Unit) %search %search
    (barrierForcedTrail forcedClassifierFixtures) (MkRootCatalogEntry 5 4 (smallComponent False))
  0 singleFlagTrue : classifierObserved singleCorrespondence = True
  0 barrierFlagTrue : classifierObserved barrierCorrespondence = True

||| Both flags follow by the GENERAL completeness proof applied to retained
||| independent KeyForces/OrderForces derivations, not by scalar Refl over a
||| nested fixture builder. Each observation also contains general soundness.
public export
0 classifierCorrespondenceFixtures : ClassifierCorrespondenceFixtures
classifierCorrespondenceFixtures = MkClassifierCorrespondenceFixtures
  (observeForcedClassification %search %search (singleForcedTrail forcedClassifierFixtures) (MkRootCatalogEntry 4 3 (smallComponent True)) Here)
  (observeForcedClassification %search %search (barrierForcedTrail forcedClassifierFixtures) (MkRootCatalogEntry 5 4 (smallComponent False)) (There Here))
  (classifierComplete (observeForcedClassification %search %search (singleForcedTrail forcedClassifierFixtures) (MkRootCatalogEntry 4 3 (smallComponent True)) Here) (singleClosure forcedClassifierFixtures))
  (classifierComplete (observeForcedClassification %search %search (barrierForcedTrail forcedClassifierFixtures) (MkRootCatalogEntry 5 4 (smallComponent False)) (There Here)) (barrierClosure forcedClassifierFixtures))
