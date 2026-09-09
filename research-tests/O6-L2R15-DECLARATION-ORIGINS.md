# L2R15 declaration origins and exact scope

Source boundary **67829724**; **42 checked declarations in 15 modules**.
{'proof': 40, 'executable': 0, 'type': 2}
This is bounded PARTIAL connector research, not Theorem73 or a normalizer.
See GRIND-SHIFT-AUDIT and CP3-DIFF-DRAFT-OVERLAY for exact premises/residues.
Each row adds ONE declaration; no predecessor bodies/comments were changed.

| Unit | File:line / name | Kind/status | Fresh invocation | Guarded commit |
|---|---|---|---|---|
| A1 | `L2R15PhaseOccurrence.idr:23` / `phaseEventAtNativeHead` | proof: proved at exact documented scope | A1-1 | `039821b6` |
| A2 | `L2R15PhaseOccurrence.idr:36` / `phaseEventThroughNativeHead` | proof: proved at exact documented scope | A2-1 | `878e99d1` |
| A3 | `L2R15PhaseOccurrence.idr:52` / `phaseEventAtNativePrefix` | proof: proved at exact documented scope | A3-1 | `fe6fad79` |
| A4 | `L2R15PhaseOccurrence.idr:70` / `phaseEventAtNativeSplit` | proof: proved at exact documented scope | A4-1 | `c43a6f2c` |
| A5 | `L2R15PhaseOccurrence.idr:86` / `phaseEventAtOccurrence` | proof: proved at exact documented scope | A5-1 | `e3e0db38` |
| A6 | `L2R15PhaseActor.idr:31` / `phaseReleaseActorIdentity` | proof: proved at exact documented scope | A6-1 | `2fd1b969` |
| A7 | `L2R15PhaseActor.idr:52` / `phaseSeedNativeHistory` | proof: proved at exact documented scope | A7-2 | `6087a4f8` |
| A8 | `L2R15PhaseHistory.idr:33` / `PhaseHistoryPath` | type: checked TYPE declaration; inhabitance reported separately | A8-1 | `4f4dbc3e` |
| A9 | `L2R15PhaseHistory.idr:48` / `phaseOwnerAtDecision` | proof: proved at exact documented scope | A9-1 | `3901bf58` |
| A10 | `L2R15PhaseHistory.idr:59` / `phaseMaybeOwnerDecoded` | proof: proved at exact documented scope | A10-1 | `2faa145f` |
| A11 | `L2R15PhaseHistory.idr:71` / `phaseHistoryPastOwner` | proof: proved at exact documented scope | A11-1 | `903ca0e2` |
| A12 | `L2R15PhaseHistory.idr:85` / `phaseHistoryAtPositionGuard` | proof: proved at exact documented scope | A12-1 | `8df8e09a` |
| A13 | `L2R15PhaseHistory.idr:115` / `phaseHistoryAtNativePosition` | proof: proved at exact documented scope | A13-3 | `9014a654` |
| A14 | `L2R15PhaseHistory.idr:134` / `phaseReleaseHistoryDecoded` | proof: proved at exact documented scope | A14-1 | `8b005273` |
| B1 | `L2R15SuffixScans.idr:29` / `nativeSuffixAligned` | proof: proved at exact documented scope | B1-1 | `af2b89c4` |
| B2 | `L2R15SuffixScans.idr:50` / `nativeHeadScanEquations` | proof: proved at exact documented scope | B2-3 | `080c3189` |
| B3 | `L2R15SuffixScans.idr:69` / `nativeSuffixCatalog` | proof: proved at exact documented scope | B3-1 | `beb11b0b` |
| B4 | `L2R15SuffixScans.idr:93` / `nativeNonReleaseTail` | proof: proved at exact documented scope | B4-1 | `4a34bcf6` |
| B5 | `L2R15SuffixScans.idr:114` / `nativeSuffixReleases` | proof: proved at exact documented scope | B5-1 | `4d202744` |
| B6 | `L2R15ScanCongruence.idr:15` / `scanFoldPointwise` | proof: proved at exact documented scope | B6-1 | `cb6e0874` |
| B7 | `L2R15ScanCongruence.idr:27` / `scanMapPointwise` | proof: proved at exact documented scope | B7-1 | `9c6be29a` |
| B8 | `L2R15ScanCongruence.idr:37` / `scanFilterAtGuard` | proof: proved at exact documented scope | B8-3 | `c604132d` |
| B9 | `L2R15ScanCongruence.idr:50` / `scanFilterPointwise` | proof: proved at exact documented scope | B9-1 | `d0062c3c` |
| B10 | `L2R15SuffixAnchors.idr:31` / `nativeSuffixAnchorKey` | proof: proved at exact documented scope | B10-1 | `dab39030` |
| B11 | `L2R15SuffixAnchors.idr:64` / `nativeSuffixTarget` | proof: proved at exact documented scope | B11-1 | `e9cab3c6` |
| B12 | `L2R15SuffixAnchors.idr:89` / `nativeDistanceAtAnchorGuard` | proof: proved at exact documented scope | B12-1 | `dff6bbef` |
| B13 | `L2R15SuffixAnchors.idr:110` / `nativeSuffixDistances` | proof: proved at exact documented scope | B13-1 | `10191478` |
| B14 | `L2R15GlobalFrames.idr:39` / `GlobalDistanceFramesFromNativeSuffix` | type: checked TYPE declaration; NOT inhabited | B14-1 | `04f0b5f9` |
| B15 | `L2R15PhaseIterationAssembly.idr:33` / `phaseIterationAtZero` | proof: proved at exact documented scope | B15-1 | `ac0f1297` |
| B16 | `L2R15PhaseIterationAssembly.idr:55` / `phaseIterationPrepend` | proof: proved at exact documented scope | B16-1 | `6bab23be` |
| C1 | `L2R15NativeInsertShape.idr:27` / `nativeInsertShapeFromView` | proof: proved at exact documented scope | C1-1 | `f2c22131` |
| C2 | `L2R15NativeInsertShape.idr:48` / `nativeInsertShape` | proof: proved at exact documented scope | C2-1 | `7005fa0d` |
| C3 | `L2R15OperationSnapshots.idr:21` / `nativeReplaceSnapshot` | proof: proved at exact documented scope | C3-1 | `132e177e` |
| C4 | `L2R15OperationSnapshots.idr:32` / `nativeDeleteSnapshot` | proof: proved at exact documented scope | C4-1 | `946b8815` |
| C5 | `L2R15NativeControlShapes.idr:26` / `nativeRetireShapeFromView` | proof: proved at exact documented scope | C5-1 | `29cf9c41` |
| C6 | `L2R15NativeControlShapes.idr:48` / `nativeRetireShape` | proof: proved at exact documented scope | C6-1 | `28adfe46` |
| C7 | `L2R15NativeControlShapes.idr:65` / `nativeRemoveShapeFromView` | proof: proved at exact documented scope | C7-1 | `f1905e7c` |
| C8 | `L2R15NativeControlShapes.idr:83` / `nativeRemoveShape` | proof: proved at exact documented scope | C8-1 | `ae7b06de` |
| C9 | `L2R15PacketControlShapes.idr:30` / `nativeCoreControlShapes` | proof: proved at exact documented scope | C9-1 | `daf94863` |
| C10 | `L2R15LocalShapeAssembly.idr:34` / `localShapesFromLifecycle` | proof: proved at exact documented scope | C10-1 | `90a88317` |
| C11 | `L2R15LocalSquareProduction.idr:40` / `packetWholeTransportFromLifecycleShapes` | proof: proved at exact documented scope | C11-2 | `fbca866e` |
| C12 | `L2R15LocalSquareFixture.idr:50` / `fixtureLocalSquareFromNativeControls` | proof: proved at exact documented scope | C12-1 | `67829724` |

## Origins and exact boundary

- A: 14/14 checked: actual occurrence/source/actor alignment and accepted native history path; physical interval/localized lifecycle+release/full phase production OPEN, research obligation not a blocker.
- B: 16/16 checked: Root/Retire suffix-only scans/alignment/anchor/target/distance and PhaseIterationResult base/step; global frames TYPE-only, invariant/move existence/general normalizer OPEN, research obligations not blockers.
- C: 12/12 checked: eight arbitrary native orchestration shapes and LOCAL square conditional on four common-payload lifecycle shapes; actual twelve fixture shape types and LOCAL6~16/derived whole7~17 reproduced. Four general lifecycle shapes OPEN, research obligation not a blocker.
- D: Owner-signed same-bundle Tier 1 exact CP3 patch and full lane recheck/repair inventory; CP3 unchanged and candidate NOT typechecked. Final validation/evidence only; after final gate NO lane2 compiler until R205 rebuild finishes, next shift re-seeds build/.

All retained sources are total and free of new holes/postulates/unsafe escapes. Exact source snapshots, bounded attempts, guarded receipts and plan-first final validations are archived. Mechanical verification is NOT parent-owned mathematical review. Tier 1 diff signable and signed by the owner on 2026-09-09; Tier 2 = open research obligations. Open research is not a Tier 1 blocker.
