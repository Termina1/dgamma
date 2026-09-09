# L2R11 declaration origins and exact scope

Source boundary **5e9c0f64**; **50 checked declarations in 12 modules**.
{'proof': 36, 'executable': 9, 'type': 5}
This is bounded PARTIAL connector research, not Theorem73 or a normalizer.
See GRIND-SHIFT-AUDIT and CP3-DIFF-DRAFT-OVERLAY for exact premises/residues.
Each row adds ONE declaration; no predecessor bodies/comments were changed.

| Unit | File:line / name | Kind/status | Fresh invocation | Guarded commit |
|---|---|---|---|---|
| A1 | `L2R11ReleaseAgreement.idr:31` / `releaseOverlapAgrees` | proof: proved at exact documented scope | A1-3 | `e4cfc60b` |
| A2 | `L2R11ReleaseAgreement.idr:43` / `overlapOrdinalsAgrees` | proof: proved at exact documented scope | A2-1 | `cff4efbe` |
| A3 | `L2R11ReleaseAgreement.idr:55` / `parentOrdinalsAgrees` | proof: proved at exact documented scope | A3-1 | `55a5152a` |
| A4 | `L2R11ReleaseAgreement.idr:72` / `lookupOrdinalsAgrees` | proof: proved at exact documented scope | A4-1 | `11f59232` |
| A5 | `L2R11ReleaseAgreement.idr:88` / `actionOrdinalsAgrees` | proof: proved at exact documented scope | A5-1 | `fb2f255a` |
| A6 | `L2R11ReleaseAgreement.idr:110` / `releaseOffsetShift` | proof: proved at exact documented scope | A6-1 | `1e48fec4` |
| A8 | `L2R11PhaseDecode.idr:28` / `phaseParentDecoded` | proof: proved at exact documented scope | A8-1 | `9181ded6` |
| A9 | `L2R11PhaseDecode.idr:36` / `phaseControlDecoded` | proof: proved at exact documented scope | A9-1 | `e0eddcfc` |
| A10 | `L2R11PhaseDecode.idr:55` / `phaseActionExtended` | proof: proved at exact documented scope | A10-2 | `1459b5e4` |
| A11 | `L2R11PhaseDecode.idr:100` / `phaseEventsExtended` | proof: proved at exact documented scope | A11-1 | `71873a4b` |
| A12 | `L2R11PhaseDecode.idr:116` / `locatePhaseEventCore` | proof: proved at exact documented scope | A12-2 | `9ae72cd8` |
| A13 | `L2R11PhaseDecode.idr:136` / `phaseEventsCount` | proof: proved at exact documented scope | A13-1 | `68f53d84` |
| A14 | `L2R11PhaseDecode.idr:148` / `phaseLifeOwnerDecoded` | proof: proved at exact documented scope | A14-1 | `46069054` |
| B1 | `L2R11WordInventory.idr:28` / `actionKindCode` | executable: checked total executable definition | B1-1 | `b4544852` |
| B2 | `L2R11WordInventory.idr:43` / `wordActionInventory` | executable: checked total executable definition | B2-1 | `50552719` |
| B3 | `L2R11WordInventory.idr:50` / `actionKindSelf` | proof: proved at exact documented scope | B3-1 | `bf5abcfd` |
| B4 | `L2R11WordInventory.idr:65` / `wordInventoryHead` | proof: proved at exact documented scope | B4-1 | `1e910194` |
| B5 | `L2R11WordInventory.idr:77` / `wordInventoryTail` | proof: proved at exact documented scope | B5-1 | `b64fa36f` |
| B6 | `L2R11WordInventory.idr:89` / `ObservedWordInventory` | type: checked type; inhabitance at exact declared scope | B6-1 | `3a2f03a2` |
| B7 | `L2R11WordInventory.idr:102` / `observeWordActionInventory` | executable: checked total executable definition | B7-1 | `21c2b532` |
| B8 | `L2R11WordInventory.idr:112` / `replayActionWord` | executable: checked total executable definition | B8-1 | `a052eab3` |
| B9 | `L2R11ActualWordReplay.idr:27` / `replayActualWordCPS` | proof: proved at exact documented scope | B9-1 | `652926eb` |
| B10 | `L2R11ActualWordReplay.idr:89` / `replayOverActualWord` | proof: proved at exact documented scope | B10-1 | `5bb30557` |
| B11 | `L2R11LifecycleSnapshot.idr:29` / `snapshotStepAtSame` | proof: proved at exact documented scope | B11-1 | `becb3f25` |
| B12 | `L2R11LifecycleSnapshot.idr:47` / `replayLifecycleAtFound` | proof: proved at exact documented scope | B12-1 | `c66db5d2` |
| B13 | `L2R11LifecycleSnapshot.idr:78` / `lifecycleRoleMissing` | proof: proved at exact documented scope | B13-1 | `f38306d7` |
| B14 | `L2R11LifecycleDispatch.idr:31` / `replayLifecycleAtLookup` | proof: proved at exact documented scope | B14-1 | `93eae1e1` |
| B15 | `L2R11LifecycleDispatch.idr:63` / `replayAdmittedRetirementRole` | proof: proved at exact documented scope | B15-1 | `f4fa032e` |
| B16 | `L2R11R191Inventory.idr:29` / `r191ActualInventory` | proof: proved at exact documented scope | B16-1 | `c6fc314d` |
| C1 | `L2R11LocatedCut.idr:26` / `LocatedSourceAction` | type: checked type; inhabitance at exact declared scope | C1-1 | `23142be5` |
| C2 | `L2R11LocatedCut.idr:40` / `locatedSourceThroughHead` | proof: proved at exact documented scope | C2-1 | `cb4db354` |
| C3 | `L2R11LocatedCut.idr:57` / `sourceQueryEmpty` | proof: proved at exact documented scope | C3-1 | `bd2f75a2` |
| C4 | `L2R11LocatedCut.idr:65` / `locateSourceAtStep` | proof: proved at exact documented scope | C4-1 | `8276d82d` |
| C5 | `L2R11LocatedCut.idr:89` / `locateSourceAction` | proof: proved at exact documented scope | C5-1 | `00ec6e36` |
| C6 | `L2R11LocatedCut.idr:108` / `selectedCutLocated` | proof: proved at exact documented scope | C6-1 | `0cd0e7c8` |
| C7 | `L2R11ClassifierSquare.idr:35` / `ClassifierSquare` | type: checked type; inhabitance at exact declared scope | C7-2 | `d20f789f` |
| C8 | `L2R11ClassifierSquare.idr:54` / `snapshotPacketMatches` | proof: proved at exact documented scope | C8-1 | `6ebb82ab` |
| C9 | `L2R11ClassifierSquare.idr:69` / `originalRetireSnapshot` | proof: proved at exact documented scope | C9-1 | `3c78abdb` |
| C10 | `L2R11ClassifierSquare.idr:87` / `produceRetireClassifierSquare` | proof: proved at exact documented scope | C10-1 | `710ed7c3` |
| C11 | `L2R11ClassifierSquare.idr:123` / `earlyRootDistinctFromChild` | proof: proved at exact documented scope | C11-1 | `72e9cdc0` |
| C12 | `L2R11ClassifierSquare.idr:141` / `retireSquareOnClassifier` | proof: proved at exact documented scope | C12-1 | `a40adf40` |
| C13 | `L2R11ClassifierSquare.idr:168` / `selectedRetireSquare` | proof: proved at exact documented scope | C13-1 | `996c8a4b` |
| D1 | `L2R11OpaqueCore.idr:30` / `CoreNativePacket` | type: checked type; inhabitance at exact declared scope | D1-1 | `a2a264ee` |
| D2 | `L2R11OpaqueCore.idr:51` / `CoreNativeRun` | type: checked type; inhabitance at exact declared scope | D2-1 | `c7dba527` |
| D3 | `L2R11OpaqueCore.idr:64` / `assembleCoreNative` | executable: checked total executable definition | D3-1 | `09884333` |
| D4 | `L2R11CorePackets.idr:30` / `originalCorePacket` | executable: checked total executable definition | D4-1 | `62e87602` |
| D5 | `L2R11CorePackets.idr:42` / `restoredCorePacket` | executable: checked total executable definition | D5-1 | `d269ef71` |
| D6 | `L2R11CorePackets.idr:54` / `originalCoreNative` | executable: checked total executable definition | D6-1 | `1ab882e5` |
| D7 | `L2R11CorePackets.idr:60` / `restoredCoreNative` | executable: checked total executable definition | D7-1 | `32202b7b` |
| D8 | `L2R11CoreFixture.idr:44` / `coreRestorationFromPackets` | proof: proved at exact documented scope | D8-1 | `5e9c0f64` |

## Origins and boundary

- A1–A6: new all-key/head/offset agreement; A7 bounded-filter formulation STOP3/3. A8–A14: native phase event decoders; not produceForcedRootPhases.
- B1–B10: executable actual-word set, observations, and NEW kind-restricted structural replay. B11–B15: original-edge role dispatcher and native actor/frame/snapshot transport. B16: ACTUAL R191 inventory, not whole relocated replay.
- C1–C6: exact source/action located occurrence decoder. C7–C13: generic genuine Retire/root local square and classifier/request branch. C14 local fixture STOP3/3 and fully reverted; no concrete application success claimed.
- D: state-family parameter stays abstract in generic core assembly. Original/restored B packets supply native equations; no split8->9 edge normalized or asserted. See audit for final D8 status.

All retained sources are total and free of new holes/postulates/unsafe escapes. Source snapshots, bounded failed attempts, guard receipts and plan-first final validations are archived. Mechanical verification is NOT independent human mathematical review; the parent owns that review gate.
