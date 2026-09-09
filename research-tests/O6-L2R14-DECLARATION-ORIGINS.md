# L2R14 declaration origins and exact scope

Source boundary **a33379be**; **40 checked declarations in 13 modules**.
{'proof': 37, 'executable': 0, 'type': 3}
This is bounded PARTIAL connector research, not Theorem73 or a normalizer.
See GRIND-SHIFT-AUDIT and CP3-DIFF-DRAFT-OVERLAY for exact premises/residues.
Each row adds ONE declaration; no predecessor bodies/comments were changed.

| Unit | File:line / name | Kind/status | Fresh invocation | Guarded commit |
|---|---|---|---|---|
| A1 | `L2R14PhaseSeed.idr:35` / `phaseActorAtOwner` | proof: proved at exact documented scope | A1-1 | `90342146` |
| A2 | `L2R14PhaseSeed.idr:47` / `phaseActorAtEvent` | proof: proved at exact documented scope | A2-2 | `2364822e` |
| A3 | `L2R14PhaseSeed.idr:66` / `phaseSeedAcceptedParts` | proof: proved at exact documented scope | A3-2 | `2e96251f` |
| A4 | `L2R14PhaseSeed.idr:88` / `phaseSeedActor` | proof: proved at exact documented scope | A4-1 | `82e1487f` |
| A5 | `L2R14PhaseRelease.idr:32` / `phaseMemberAtDecision` | proof: proved at exact documented scope | A5-1 | `878f7a56` |
| A6 | `L2R14PhaseRelease.idr:44` / `phaseConsInclusion` | proof: proved at exact documented scope | A6-2 | `820cfd12` |
| A7 | `L2R14PhaseRelease.idr:53` / `phaseFilterAtBool` | proof: proved at exact documented scope | A7-2 | `53625681` |
| A8 | `L2R14PhaseRelease.idr:66` / `phaseFilterMember` | proof: proved at exact documented scope | A8-2 | `ac963c49` |
| A9 | `L2R14PhaseRelease.idr:77` / `phaseMapMember` | proof: proved at exact documented scope | A9-1 | `d5d77fe4` |
| A10 | `L2R14PhaseRelease.idr:91` / `phaseReleaseAtOrdinal` | proof: proved at exact documented scope | A10-1 | `24012a65` |
| A11 | `L2R14PhaseRelease.idr:112` / `phaseSeedRelease` | proof: proved at exact documented scope | A11-1 | `529e3953` |
| A12 | `L2R14PhaseOrigins.idr:43` / `produceForcedPhaseOrigins` | proof: proved at exact documented scope | A12-1 | `7aa1f64c` |
| A13 | `L2R14PhaseOrigins.idr:74` / `phaseReleaseNativeOwner` | proof: proved at exact documented scope | A13-1 | `1dfb8341` |
| A14 | `L2R14PhaseOrigins.idr:89` / `phaseProducedReleaseCount` | proof: proved at exact documented scope | A14-1 | `64ef9f6e` |
| B1 | `L2R14CatalogQuery.idr:25` / `catalogQueryThroughHead` | proof: proved at exact documented scope | B1-1 | `0afef16d` |
| B2 | `L2R14CatalogQuery.idr:38` / `catalogQueryInsert` | proof: proved at exact documented scope | B2-1 | `fa7f0e9b` |
| B3 | `L2R14CatalogQuery.idr:58` / `catalogQueryAtAction` | proof: proved at exact documented scope | B3-1 | `cc8632d2` |
| B4 | `L2R14CatalogQuery.idr:92` / `scanCatalogActionQuery` | proof: proved at exact documented scope | B4-1 | `7c62f2d4` |
| B5 | `L2R14AdjacentNative.idr:31` / `AlignedAdjacentNative` | type: checked TYPE declaration; inhabitance reported separately | B5-1 | `664c6b13` |
| B6 | `L2R14AdjacentNative.idr:47` / `adjacentNativeThroughHead` | proof: proved at exact documented scope | B6-1 | `372c63de` |
| B7 | `L2R14AdjacentNative.idr:70` / `alignedNativeHead` | proof: proved at exact documented scope | B7-1 | `268288f8` |
| B8 | `L2R14AdjacentNative.idr:89` / `adjacentNativeAtHead` | proof: proved at exact documented scope | B8-1 | `97862e28` |
| B9 | `L2R14AdjacentNative.idr:121` / `adjacentNativeAtOrdinal` | proof: proved at exact documented scope | B9-1 | `eb384386` |
| B10 | `L2R14AdjacentNative.idr:153` / `adjacentNativeAtStep` | proof: proved at exact documented scope | B10-1 | `cf201465` |
| B11 | `L2R14AdjacentNative.idr:182` / `locateAlignedAdjacent` | proof: proved at exact documented scope | B11-1 | `6839d3c8` |
| B12 | `L2R14AdjacentNative.idr:207` / `selectedAlignedAdjacent` | proof: proved at exact documented scope | B12-1 | `22662e21` |
| B13 | `L2R14IterationFromMoves.idr:22` / `admittedMoveMeasuresUnique` | proof: proved at exact documented scope | B13-1 | `2bdebc08` |
| B14 | `L2R14IterationFixtures.idr:68` / `fixtureIterationsFromProducers` | proof: proved at exact documented scope | B14-1 | `6310c426` |
| B15 | `L2R14IterationFixtures.idr:85` / `fixtureProducedMeasuresAgree` | proof: proved at exact documented scope | B15-1 | `98ce2c65` |
| B16 | `L2R14IterationFixtures.idr:101` / `fixtureDistancePathFromProducers` | proof: proved at exact documented scope | B16-1 | `65060ef9` |
| C1 | `L2R14LocalOperations.idr:22` / `localReplaceFreshHead` | proof: proved at exact documented scope | C1-1 | `e5245e31` |
| C2 | `L2R14LocalOperations.idr:35` / `localDeleteFreshHead` | proof: proved at exact documented scope | C2-1 | `e8d80183` |
| C3 | `L2R14LocalOperations.idr:49` / `localChildInsertRetireDelete` | proof: proved at exact documented scope | C3-1 | `65fb93bb` |
| C4 | `L2R14ActionShapes.idr:30` / `NativeActionShape` | type: checked TYPE declaration; inhabitance reported separately | C4-1 | `81638079` |
| C5 | `L2R14ActionShapes.idr:44` / `nativeActionShapeSnapshot` | proof: proved at exact documented scope | C5-1 | `1aee3934` |
| C6 | `L2R14ActionShapes.idr:63` / `LocalSquareActionShapes` | type: checked TYPE declaration; inhabitance reported separately | C6-1 | `8707cebc` |
| C7 | `L2R14CoreShapeFold.idr:33` / `coreNativeSnapshotFromShapes` | proof: proved at exact documented scope | C7-1 | `951907be` |
| C8 | `L2R14LocalSquareProduction.idr:41` / `packetWholeTransportFromActionShapes` | proof: proved at exact documented scope | C8-1 | `6acc5ef4` |
| C9 | `L2R14LocalShapeFixture.idr:38` / `fixtureLocalActionShapes` | proof: proved at exact documented scope | C9-1 | `651aa8e8` |
| C10 | `L2R14LocalSquareFixture.idr:46` / `fixtureLocalSquareFromActionShapes` | proof: proved at exact documented scope | C10-1 | `a33379be` |

## Origins and exact boundary

- A: produceForcedPhaseOrigins derives actual phase-event actor/check and GLOBAL native release from produceForcedPhaseEntry; native release source classifier and actual release maximum count/birth bound proved. phaseReleaseCheckToNativeOwnedInterval, actor identity at the event, lifecycle/core localization and produceForcedRootPhases remain OPEN.
- B: scanCatalogActionQuery and selectedAlignedAdjacent produce ORIGINAL source-aligned native predecessor/root edges for arbitrary selected cuts at explicit AlignedTransitions. Actual fixed1→0/2→1→0 iterations and endpoints/zero come FROM the general LOCAL move producers; all3 measures agree with D8. Global scalar-frame/invariant/suffix/Begin/Advance/existence/normalizePhaseDistance remain OPEN.
- C: authorized raw per-action registry-operation route, no native split Remove. See audit for exact final producer and fixture scope. Raw per-action state-shape premises are general hypotheses, discharged only on the fixture. Complete cure remains NOT SIGNABLE.
- No predecessor source/doc repair, unsafe escape or src/ change. C8 has one exactly authorized visibility-only correction; hashes/receipt in archive.

All retained sources are total and free of holes/postulates/unsafe escapes. Exact raw source snapshots, bounded attempts, guarded receipts and plan-first final validations are archived. Mechanical verification is NOT parent-owned independent mathematical review. Complete cure is NOT SIGNABLE.
