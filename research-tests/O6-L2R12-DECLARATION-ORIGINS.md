# L2R12 declaration origins and exact scope

Source boundary **1251199e**; **50 checked declarations in 18 modules**.
{'proof': 40, 'executable': 4, 'type': 6}
This is bounded PARTIAL connector research, not Theorem73 or a normalizer.
See GRIND-SHIFT-AUDIT and CP3-DIFF-DRAFT-OVERLAY for exact premises/residues.
Each row adds ONE declaration; no predecessor bodies/comments were changed.

| Unit | File:line / name | Kind/status | Fresh invocation | Guarded commit |
|---|---|---|---|---|
| A1 | `L2R12PhaseContract.idr:29` / `ForcedRootPhaseFromObservedAgreement` | type: checked TYPE declaration; NOT inhabited | A1-1 | `fc95f4d4` |
| A2 | `L2R12PhaseAgreement.idr:33` / `phaseFixtureBoundedAgreement` | proof: proved at exact documented scope | A2-1 | `6123399a` |
| A3 | `L2R12PhaseAccepted.idr:28` / `phaseAllFoldFalse` | proof: proved at exact documented scope | A3-1 | `65b4b4e9` |
| A4 | `L2R12PhaseAccepted.idr:35` / `phaseAllFoldObserved` | proof: proved at exact documented scope | A4-1 | `e69960e8` |
| A5 | `L2R12PhaseAccepted.idr:44` / `phaseAllMember` | proof: proved at exact documented scope | A5-2 | `db9ac876` |
| A6 | `L2R12PhaseAccepted.idr:59` / `phaseAnchorSeedCheck` | executable: checked total executable definition | A6-1 | `60bac0be` |
| A7 | `L2R12PhaseAccepted.idr:81` / `phaseScanEntryAccepted` | proof: proved at exact documented scope | A7-1 | `a43578cd` |
| A8 | `L2R12PhaseAccepted.idr:102` / `phaseSeedAtAnchor` | proof: proved at exact documented scope | A8-1 | `e70f3893` |
| A9 | `L2R12PhaseNativeFixtures.idr:45` / `phaseFixtureCore` | executable: checked total executable definition | A9-1 | `22110746` |
| A10 | `L2R12PhaseNativeFixtures.idr:51` / `phaseFixtureLife` | proof: proved at exact documented scope | A10-1 | `8e8d25d9` |
| A11 | `L2R12PhaseNativeFixtures.idr:59` / `singleForcedPhaseDecoded` | proof: proved at exact documented scope | A11-1 | `2dfff961` |
| A12 | `L2R12PhaseNativeFixtures.idr:75` / `barrierRootPhaseDecoded` | proof: proved at exact documented scope | A12-1 | `371b20d4` |
| A13 | `L2R12PhaseNativeFixtures.idr:91` / `barrierSuccessorPhaseDecoded` | proof: proved at exact documented scope | A13-1 | `cd486e35` |
| A14 | `L2R12PhaseNativeFixtures.idr:106` / `phaseFixtureBirths` | proof: proved at exact documented scope | A14-1 | `90f8dca9` |
| B1 | `L2R12AdvanceDispatch.idr:31` / `replayAdvanceAtFound` | proof: proved at exact documented scope | B1-1 | `2388d30a` |
| B2 | `L2R12AdvanceDispatch.idr:63` / `advanceMissingImpossible` | proof: proved at exact documented scope | B2-1 | `383daad3` |
| B3 | `L2R12AdvanceDispatch.idr:76` / `replayAdvanceAtLookup` | proof: proved at exact documented scope | V1 | `c5aa935e` |
| B4 | `L2R12KindDispatch.idr:35` / `replayAdmittedRetirementKind` | proof: proved at exact documented scope | B4-2 | `bcf98094` |
| B5 | `L2R12InventoryDomain.idr:29` / `inventoryAdmittedKind` | proof: proved at exact documented scope | B5-3 | `e854025d` |
| B6 | `L2R12ClosedFold.idr:29` / `replayRestrictedRetirement` | proof: proved at exact documented scope | B6-1 | `c348b1cb` |
| B7 | `L2R12SnapshotSuffix.idr:23` / `replaySnapshotSuffixCPS` | proof: proved at exact documented scope | B7-1 | `79c23fb4` |
| B8 | `L2R12ValidWordFold.idr:25` / `replayActualWordValidCPS` | proof: proved at exact documented scope | B8-1 | `8156cb67` |
| B9 | `L2R12R191Segments.idr:33` / `R191RetirementSegments` | type: checked TYPE declaration; NOT inhabited | B9-1 | `f80bd0f8` |
| B10 | `L2R12R191Segments.idr:61` / `r191RetirementSegments` | executable: checked total executable definition | B10-3 | `17f08f7d` |
| B11 | `L2R12R191Whole.idr:37` / `R191FoldReplay` | type: checked TYPE declaration; NOT inhabited | B11-1 | `cb52e8d5` |
| B12 | `L2R12R191Whole.idr:49` / `spliceR191FoldedSpan` | proof: proved at exact documented scope | B12-1 | `3a947bdf` |
| B13 | `L2R12R191Whole.idr:76` / `r191WholeFromFold` | proof: proved at exact documented scope | B13-2 | `c41745f1` |
| B14 | `L2R12R191Whole.idr:96` / `r191WholeReplayFromFold` | proof: proved at exact documented scope | B14-1 | `d8cbc49b` |
| C1 | `L2R12SelectedAdjacency.idr:30` / `zeroDistanceAtGuard` | proof: proved at exact documented scope | C1-2 | `608ec726` |
| C2 | `L2R12SelectedAdjacency.idr:37` / `rootDistanceAtZero` | proof: proved at exact documented scope | C2-2 | `a721c311` |
| C3 | `L2R12SelectedAdjacency.idr:50` / `selectedBirthNotZero` | proof: proved at exact documented scope | C3-1 | `b08be844` |
| C4 | `L2R12SelectedAdjacency.idr:65` / `successorPredPositive` | proof: proved at exact documented scope | C4-1 | `24b9cfea` |
| C5 | `L2R12SelectedAdjacency.idr:74` / `selectedLocatedAdjacentOrdinals` | proof: proved at exact documented scope | C5-1 | `e5c3b2b4` |
| C6 | `L2R12AlignedCut.idr:27` / `AlignedSourceAction` | type: checked TYPE declaration; NOT inhabited | C6-1 | `5c9466db` |
| C7 | `L2R12AlignedCut.idr:46` / `alignedSourceThroughHead` | proof: proved at exact documented scope | C7-1 | `83adb9d2` |
| C8 | `L2R12AlignedCut.idr:66` / `alignedSourceAtOrdinal` | proof: proved at exact documented scope | C8-1 | `ea9352c6` |
| C9 | `L2R12AlignedCut.idr:101` / `alignedSourceAtStep` | proof: proved at exact documented scope | C9-1 | `6540df8b` |
| C10 | `L2R12AlignedCut.idr:126` / `locateAlignedSourceAction` | proof: proved at exact documented scope | C10-1 | `9af5c736` |
| C11 | `L2R12AlignedCut.idr:148` / `selectedCutAlignedEdge` | proof: proved at exact documented scope | C11-1 | `013a1368` |
| C12 | `L2R12ClassifierNative.idr:28` / `retireTagNormalize` | proof: proved at exact documented scope | C12-1 | `97f79e11` |
| C13 | `L2R12ClassifierNative.idr:46` / `selectedRetireFromAligned` | proof: proved at exact documented scope | C13-1 | `e7cd65c5` |
| C14 | `L2R12DistanceFrame.idr:26` / `totalDistanceOneLeftFromFrame` | proof: proved at exact documented scope | C14-1 | `315f885b` |
| D1 | `L2R12PacketContiguity.idr:35` / `packetCoreWords` | proof: proved at exact documented scope | D1-1 | `2cbcfe59` |
| D2 | `L2R12PacketContiguity.idr:53` / `PacketPassage` | type: checked TYPE declaration; NOT inhabited | D2-1 | `8e0e7e3a` |
| D3 | `L2R12PacketContiguity.idr:81` / `PacketContiguityResult` | type: checked TYPE declaration; NOT inhabited | D3-1 | `1f10e006` |
| D4 | `L2R12PacketContiguity.idr:107` / `locatePacketCore` | proof: proved at exact documented scope | D4-1 | `62b0d858` |
| D5 | `L2R12PacketContiguity.idr:124` / `packetPrefixShift` | proof: proved at exact documented scope | D5-1 | `ea383be8` |
| D6 | `L2R12PacketContiguity.idr:137` / `coreContiguityFromPackets` | proof: proved at exact documented scope | D6-1 | `7557734d` |
| D7 | `L2R12PacketFixture.idr:42` / `fixturePacketPassage` | executable: checked total executable definition | D7-1 | `1bf48dfd` |
| D8 | `L2R12PacketFixture.idr:60` / `coreRestorationViaGeneralPackets` | proof: proved at exact documented scope | D8-1 | `1251199e` |

## Origins and exact boundary

- A: observed-agreement phase TYPE; both seed/cut4 fixture agreements; authentic native phase acceptance and seed extraction at a Just anchor; three ForcedRootPhase inhabitants (C12 root3, barrier root3/root4) and catalog-decoded births. General produceForcedRootPhases still OPEN.
- B: fully discharged actual-kind callback, all-tag Advance + native Begin tag; closed replayOverActualWord consumer. Validity-strengthened restricted fold and native suffix splicing produce the ACTUAL full R191 replay with snapshot-equal original endpoint. Whole replay is not a projection of the earlier relocated fixture.
- C: exact selected physical ordinal adjacency; native source/target/tag/checked equation at explicit aligned dictionaries; selected Retire classifier receives its predecessor edge from the decoder. Following-root state transport, global distance frames, AdmittedDistanceMove production, D8 from producer and normalizer remain OPEN.
- D: arbitrary-state-family packet core word/count/location and +1 placement. Conditional general consumer explicitly requires RegistryExtensional whole endpoints under supervisor ruling(A). Fixed instance discharges that premise from contiguityEndpoints; arbitrary-family endpoint transport remains OPEN. No split edge.
- B3 source publication used V1 ONLY after an exact rstrip-only fresh validation of B3-1 (EOF whitespace guard rejected before staging); both snapshots and explicit authority are archived. All other declarations use their own bounded source-attempt PASS.

All retained sources are total and free of new holes/postulates/unsafe escapes. Exact source snapshots, bounded attempts, guard receipts and plan-first final validations are archived. Mechanical verification is NOT the parent-owned independent mathematical review. Complete cure is NOT SIGNABLE.
