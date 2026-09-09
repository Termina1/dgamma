module DGamma.L2R4AnchorFixtures

import DGamma.Calculus
import DGamma.Coeffects
import DGamma.Metatheory
import DGamma.CP3
import DGamma.CP4ProgressNoDeadlock
import DGamma.CP5AvailabilityAwarePlacement
import DGamma.L2R2SmallStates
import DGamma.L2R2SmallExecution
import DGamma.L2R2SmallPlacement
import DGamma.L2R2RootSnapshot
import DGamma.L2R2RootPhase
import DGamma.L2R3Attached
import DGamma.L2R3SmallAttached
import DGamma.L2R3BarrierBlocks
import DGamma.L2R3AttachedGap
import DGamma.L2R3FixtureCoverage
import DGamma.L2R3BarrierStates
import DGamma.L2R3BarrierExecution
import DGamma.L2R3BundlePhaseStates
import DGamma.L2R3BundlePhase
import DGamma.L2R4AnchorMeasure
import DGamma.L2R4AnchorNative
import DGamma.L2R4AnchorDecrease
import Data.List
import Data.Nat
import Decidable.Equality

%default total
%unbound_implicits off

||| Whole native moved trails from cut0, their exact annotations, real anchor
||| cut/bundle facts, global zeros and 2->1->0 for the two admitted R/S moves.
||| Earlier lifecycle events are PRESENT, not dropped as a local suffix.
||| EarliestAvailableRootBirth is retained as legality, NOT redefined as count.
public export
record AnchorFixtureEvidence where
  constructor MkAnchorFixtureEvidence
  singleTrail : AvailabilityTrace Nat Bool Unit String (\key => Unit)
    (rootPhaseTrace (smallPhase smallRootPhaseEvidence))
  bundleTrail : AvailabilityTrace Nat Bool Unit String (\key => Unit)
    (appendTransitions (beforeActionOccurrence smallRootBirth) (rootPhaseTrace (sPhase bundlePhaseEvidence)))
  singleEvents : List (AnchorEvent Nat)
  bundleEvents : List (AnchorEvent Nat)
  originalEvents : List (AnchorEvent Nat)
  middleEvents : List (AnchorEvent Nat)
  0 singleEventsNative : singleEvents = annotateAnchors (\ordinal, root => Just 4) 0 singleTrail
  0 bundleEventsNative : bundleEvents = annotateAnchors (\ordinal, root => Just 4) 0 bundleTrail
  0 originalEventsNative : originalEvents =
    annotateAnchors (\ordinal, root => Just 4) 0 smallAvailabilityTrail ++
    annotateAnchors (\ordinal, root => Just 4) 4 (originalTrail bundlePhaseEvidence)
  0 middleEventsNative : middleEvents =
    annotateAnchors (\ordinal, root => Just 4) 0 smallAvailabilityTrail ++
    annotateAnchors (\ordinal, root => Just 4) 4 (middleTrail bundlePhaseEvidence)
  0 releaseCut : locatedActionOrdinal smallRootBirth = 4
  0 rLegalEarliest : EarliestAvailableRootBirth Nat Bool Unit String (\key => Unit)
    %search %search smallTrace 3 (smallComponent True) smallRootBirth
  0 rAttachedAnchor : bundleOffset (c12CatalogR fixtureCoverage) = 4
  0 sBarrierAnchor : bundleOffset (barrierCatalogS fixtureCoverage) = 4
  0 singleGlobalZero : anchorInversions %search [] singleEvents = 0
  0 bundleGlobalZero : anchorInversions %search [] bundleEvents = 0
  0 originalGlobalTwo : anchorInversions %search [] originalEvents = 2
  0 middleGlobalOne : anchorInversions %search [] middleEvents = 1
  0 firstGlobalDecreases : anchorInversions %search [] originalEvents = S (anchorInversions %search [] middleEvents)
  0 secondGlobalDecreases : anchorInversions %search [] middleEvents = S (anchorInversions %search [] bundleEvents)

||| Simultaneously annotate the ACTUAL full moved trails and both original/
||| middle R/S paths, preserving cut0's blocked lifecycle prefix. All forced
||| fixture roots use their real release cut4, including barrier-forced S.
||| Global 2->1->0 follows C10 with the unchanged prefix and suffix, not by
||| pretending compatible-cut counting decreases on R's hoist.
public export
0 anchorFixtureEvidence : AnchorFixtureEvidence
anchorFixtureEvidence = MkAnchorFixtureEvidence
  (smallMovedTrail smallRootPhaseEvidence)
  (AvailabilityStep (smallState 0)
    (Fired {before = smallState 0} {afterState = smallState 1} %search %search (LBegin 0) LBeginTag (smallBegin0 smallNativeExecution)) _
    (AvailabilityStep (smallState 1)
      (Fired {before = smallState 1} {afterState = smallState 2} %search %search (LAdvance 0) LFinishTag (smallFinish0 smallNativeExecution)) _
      (AvailabilityStep (smallState 2)
        (Fired {before = smallState 2} {afterState = smallState 3} %search %search (ORetire 1) ORetireTag (smallRetire1 smallNativeExecution)) _
        (AvailabilityStep (smallState 3)
          (Fired {before = smallState 3} {afterState = smallState 4} %search %search (ORemove 1) ORemoveTag (smallRemove1 smallNativeExecution)) _
          (movedTrail bundlePhaseEvidence)))))
  [AnchorLife 0, AnchorLife 0, AnchorOther, AnchorRelease 4, AnchorBirth 3 (Just 4), AnchorLife 2]
  [AnchorLife 0, AnchorLife 0, AnchorOther, AnchorRelease 4, AnchorBirth 3 (Just 4), AnchorBirth 4 (Just 4), AnchorLife 2]
  [AnchorLife 0, AnchorLife 0, AnchorOther, AnchorRelease 4, AnchorLife 2, AnchorBirth 3 (Just 4), AnchorBirth 4 (Just 4)]
  [AnchorLife 0, AnchorLife 0, AnchorOther, AnchorRelease 4, AnchorBirth 3 (Just 4), AnchorLife 2, AnchorBirth 4 (Just 4)]
  Refl Refl Refl Refl Refl smallRootEarliest
  (cong fst (c12CatalogInterval fixtureCoverage))
  (cong fst (barrierCatalogSInterval fixtureCoverage))
  Refl Refl
  (trans (anchorSwapDecreases %search 2 3 (Just 4)
    [AnchorLife 0, AnchorLife 0, AnchorOther, AnchorRelease 4]
    [AnchorBirth 4 (Just 4)] (\same => case same of Refl impossible) [])
    (cong S (anchorSwapDecreases %search 2 4 (Just 4)
      [AnchorLife 0, AnchorLife 0, AnchorOther, AnchorRelease 4, AnchorBirth 3 (Just 4)]
      [] (\same => case same of Refl impossible) [])))
  (anchorSwapDecreases %search 2 4 (Just 4)
    [AnchorLife 0, AnchorLife 0, AnchorOther, AnchorRelease 4, AnchorBirth 3 (Just 4)]
    [] (\same => case same of Refl impossible) [])
  (anchorSwapDecreases %search 2 3 (Just 4)
    [AnchorLife 0, AnchorLife 0, AnchorOther, AnchorRelease 4]
    [AnchorBirth 4 (Just 4)] (\same => case same of Refl impossible) [])
  (anchorSwapDecreases %search 2 4 (Just 4)
    [AnchorLife 0, AnchorLife 0, AnchorOther, AnchorRelease 4, AnchorBirth 3 (Just 4)]
    [] (\same => case same of Refl impossible) [])
