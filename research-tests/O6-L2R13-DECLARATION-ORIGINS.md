# L2R13 declaration origins and exact scope

Source boundary **6b44f2a7**; **38 checked declarations in 12 modules**.
{'proof': 33, 'executable': 3, 'type': 2}
This is bounded PARTIAL connector research, not Theorem73 or a normalizer.
See GRIND-SHIFT-AUDIT and CP3-DIFF-DRAFT-OVERLAY for exact premises/residues.
Each row adds ONE declaration; no predecessor bodies/comments were changed.

| Unit | File:line / name | Kind/status | Fresh invocation | Guarded commit |
|---|---|---|---|---|
| A1 | `L2R13ForcedAnchor.idr:31` / `phaseNatZero` | proof: proved at exact documented scope | A1-1 | `24fe5497` |
| A2 | `L2R13ForcedAnchor.idr:37` / `phaseNatSuccessor` | proof: proved at exact documented scope | A2-1 | `4daa7905` |
| A3 | `L2R13ForcedAnchor.idr:45` / `phaseNatEqual` | proof: proved at exact documented scope | A3-2 | `d592d931` |
| A4 | `L2R13ForcedAnchor.idr:51` / `phaseAppendNonempty` | proof: proved at exact documented scope | A4-1 | `f566eeff` |
| A5 | `L2R13ForcedAnchor.idr:59` / `phaseFlattenNonempty` | proof: proved at exact documented scope | A5-2 | `813c9113` |
| A6 | `L2R13ForcedAnchor.idr:71` / `phaseConcatNonempty` | proof: proved at exact documented scope | A6-1 | `caeb4756` |
| A7 | `L2R13ForcedAnchor.idr:83` / `phaseKeyHitNonempty` | proof: proved at exact documented scope | A7-1 | `cbb33c69` |
| A8 | `L2R13ForcedAnchor.idr:112` / `phaseForcedHitNonempty` | proof: proved at exact documented scope | A8-1 | `b0ee9037` |
| A9 | `L2R13ForcedAnchor.idr:135` / `phaseNonemptyAnchor` | executable: checked total executable definition | A9-1 | `ce60e607` |
| A10 | `L2R13ForcedAnchor.idr:144` / `forcedAnchorJust` | proof: proved at exact documented scope | A10-1 | `6a750808` |
| A11 | `L2R13PhaseEntry.idr:37` / `produceForcedPhaseEntry` | proof: proved at exact documented scope | A11-1 | `7f6c47db` |
| A12 | `L2R13PhaseFixtures.idr:49` / `forcedAnchorsReproducePhases` | proof: proved at exact documented scope | A12-1 | `60ed426b` |
| A13 | `L2R13PhaseEntry.idr:62` / `phaseMaximumIndex` | proof: proved at exact documented scope | A13-1 | `833afacf` |
| A14 | `L2R13PhaseEntry.idr:75` / `phaseAnchorCountBound` | proof: proved at exact documented scope | A14-1 | `0e6434f8` |
| B1 | `L2R13InsertExtensional.idr:28` / `insertLookupExtensionalObserved` | proof: proved at exact documented scope | B1-1 | `cf205c75` |
| B2 | `L2R13InsertExtensional.idr:61` / `freshInsertExtensional` | proof: proved at exact documented scope | B2-1 | `f867a408` |
| B3 | `L2R13InsertExtensional.idr:77` / `freshInsertSnapshot` | proof: proved at exact documented scope | B3-1 | `4d7c4b39` |
| B4 | `L2R13InsertExtensional.idr:90` / `rootInsertPacketExtensional` | proof: proved at exact documented scope | B4-1 | `d007cb36` |
| B5 | `L2R13InsertExtensional.idr:114` / `insertionStateEta` | proof: proved at exact documented scope | B5-1 | `3ad8c644` |
| B6 | `L2R13InsertExtensional.idr:123` / `rootInsertExtensionalFromView` | proof: proved at exact documented scope | B6-1 | `502d120b` |
| B7 | `L2R13InsertExtensional.idr:152` / `checkedRootAcrossExtensional` | proof: proved at exact documented scope | B7-1 | `b1456c13` |
| B8 | `L2R13SquareSuccessor.idr:32` / `squareFollowingRoot` | proof: proved at exact documented scope | B8-1 | `42b8c3ab` |
| B9 | `L2R13TerminalMove.idr:39` / `nativePairTrail` | executable: checked total executable definition | B9-1 | `888b3f00` |
| B10 | `L2R13TerminalMove.idr:62` / `terminalSquareAdmittedMove` | proof: proved at exact documented scope | B10-2 | `6f813b53` |
| B11 | `L2R13DistanceFixtures.idr:62` / `distanceFixtureSquares` | proof: proved at exact documented scope | B11-1 | `17626d5d` |
| B12 | `L2R13DistanceFixtures.idr:83` / `terminalFixtureMoves` | proof: proved at exact documented scope | B12-2 | `4bf66cb8` |
| B13 | `L2R13ExtendMove.idr:45` / `extendAdmittedMoveByRoot` | proof: proved at exact documented scope | B13-2 | `5925ac4f` |
| B14 | `L2R13DistanceFixtures.idr:103` / `firstBundleFromProducer` | proof: proved at exact documented scope | B14-2 | `b7c91f6a` |
| C1 | `L2R13NativeSuffixFrames.idr:25` / `NativeSuffixFrames` | type: checked TYPE declaration; inhabitance reported separately | C1-1 | `1a8e70cf` |
| C2 | `L2R13NativeSuffixFrames.idr:67` / `nativeRootFrameEndpoint` | proof: proved at exact documented scope | C2-1 | `ca1ae6d8` |
| C3 | `L2R13NativeSuffixFrames.idr:95` / `nativeRetireFrameEndpoint` | proof: proved at exact documented scope | C3-1 | `9825bdd8` |
| C4 | `L2R13NativeSuffixFrames.idr:115` / `nativeSuffixEndpoints` | proof: proved at exact documented scope | C4-1 | `ffd2e55a` |
| C5 | `L2R13PacketEndpointTransport.idr:33` / `PacketWholeEndpointTransport` | type: checked TYPE declaration; inhabitance reported separately | C5-1 | `a16feec2` |
| C6 | `L2R13PacketEndpointTransport.idr:56` / `packetWholeEndpointsFromLocalSquare` | proof: proved at exact documented scope | C6-1 | `ea89f008` |
| C7 | `L2R13PacketEndpointFixture.idr:43` / `fixtureLocalCoreRootSquare` | proof: proved at exact documented scope | C7-1 | `f50b73f8` |
| C8 | `L2R13PacketEndpointFixture.idr:52` / `fixturePacketEndpointHypotheses` | executable: checked total executable definition | C8-1 | `3b02bb58` |
| C9 | `L2R13PacketEndpointTransport.idr:70` / `coreContiguityFromLocalSquareFrames` | proof: proved at exact documented scope | C9-1 | `81f0aa10` |
| C10 | `L2R13CoreRestoration.idr:46` / `coreRestorationViaNativeEndpointFrames` | proof: proved at exact documented scope | C10-2 | `6b44f2a7` |

## Origins and exact boundary

- A: forcedAnchorJust and produceForcedPhaseEntry derive anchor, accepted authentic seed and birth from scanCatalogBirth; all three L2R12 fixture anchors reproduced. Max scan membership/successor count and anchor-before-birth proved. Physical interval/lifecycle/release localization and general produceForcedRootPhases remain OPEN.
- B: native root successor from RegistryExtensional and explicit scalar declaration frame; squareFollowingRoot adapter. Genuine terminalSquareAdmittedMove derives words/locations/current cuts/endpoint/decrement. All three D8 moves FROM new producers, including first bundle via native root suffix extension. Global phase/front/NeverRetired/uniqueness and scan-frame transport/existence, generic Begin/Advance integration and normalizePhaseDistance remain OPEN.
- C: arbitrary-family PacketWholeEndpointTransport hypotheses and whole endpoints via native Root/Retire suffix induction. The five-edge core/root LOCAL square is an explicit justified hypothesis, not derived from per-action swaps. Fixed instance proves local6~16, then derives7~17 through actual S edges; no contiguityEndpoints whole equality and no native split Remove. General core-word/location/placement route composes with this into full fixed CoreRestorationFixture.
- B10 has exactly one authorized visibility-only + single-sentence correction54f188ce, fresh V0 before B14-2. The original declaration commit and final-source hashes differ by ONLY that authenticated correction; types/body/quantities unchanged.
- P2 documentary repairs affect only L2R12 origins, micro-ledger and publisher. A1 TYPE alias is NOT inhabited; record declarations report inhabitance separately. Both exact repair phases are authenticated in raw rulings/receipts; no predecessor source changed.

All retained sources are total and free of holes/postulates/unsafe escapes. Exact raw source snapshots, bounded attempts, guarded receipts and plan-first final validations are archived. Mechanical verification is NOT parent-owned independent mathematical review. Complete cure is NOT SIGNABLE.
