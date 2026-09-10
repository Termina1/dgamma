# L2R16 declaration and repair origins

Boundary **9a864c05**; **17 checked Tier2 declarations in 12 modules**.
T12 was completely reverted. T18 is conditional on uniqueness; no unconditional normalization or full global-frame retirement is claimed.
RSS terminology is fixed in the compiler ledger. TYPE definitions and their inhabitants are separate.

| Unit | Source:name | Kind and exact status | Invocation | Guarded commit |
|---|---|---|---|---|
| T1 | `L2R16AnchorStates.idr:24:anchorComponent` | executable: total independent-key component constructor | T1-1 | `24aa1e5d` |
| T2 | `L2R16AnchorStates.idr:34:anchorState` | executable: total literal native snapshot accessor; no extra-edge claim for fallback indices | T2-1 | `dff38517` |
| T3 | `L2R16AnchorNative.idr:28:AnchorNativeExecution` | type: native obligation record TYPE, inhabited separately by T4 | T3-1 | `b59035d3` |
| T4 | `L2R16AnchorNative.idr:59:anchorNative` | proof: initial well-formedness and twelve actual checked native edges | T4-1 | `1c60845a` |
| T5 | `L2R16AnchorTrace.idr:28:anchorTrace` | executable: two authentic native words | T5-1 | `54cf9f50` |
| T6 | `L2R16AnchorTrail.idr:29:anchorTrail` | executable: actual production AvailabilityTrace data for both words | T6-1 | `69163c06` |
| T7 | `L2R16ProductionBridge.idr:24:researchAvailability` | executable: generic production-to-research constructor bridge preserving native data/index | T7-1 | `b828484d` |
| T8 | `L2R16AnchorDistance.idr:40:anchorDistanceData` | executable: executable two-distance/total/target observation | T8-1 | `626a8cb4` |
| T9 | `L2R16AnchorDistance.idr:56:anchorDistanceAgreement` | proof: actual (3,0,3,8)->(2,1,3,7) data agreement | T9-1 | `8a5dfcf4` |
| T10 | `L2R16AnchorPhases.idr:45:anchorPhase` | proof: four concrete ForcedRootPhase inhabitants, not a general producer | T10-1 | `1792b15b` |
| T11 | `L2R16AnchorUnique.idr:41:anchorInsertionAt` | proof: authentic raw insertion ordinal theorem, not assembled uniqueness | T11-3 | `2259e1d3` |
| T13 | `L2R16AnchorDomain.idr:42:anchorFrontNever` | proof: FrontNormal and NeverRetired for both words | T13-1 | `1b0d10b4` |
| T14 | `L2R16AnchorSquare.idr:44:anchorSquare` | proof: actual classified native square, not AdmittedDistanceMove | T14-1 | `390bbb5e` |
| T15 | `L2R16AnchorSegments.idr:46:anchorSegment` | executable: exact native prefix and two suffix reifications | T15-1 | `5f2f1af3` |
| T16 | `L2R16AnchorSegments.idr:64:anchorSuffixFrames` | proof: genuine native remaining-root suffix frames | T16-1 | `f83d0426` |
| T17 | `L2R16AnchorDomain.idr:56:anchorCatalogCoverage` | proof: complete old catalog phases and earlier-root exclusion via All data | T17-3 | `f0e4f882` |
| T18 | `L2R16AnchorFrameRejection.idr:57:anchorGlobalFrameRejectedGivenUnique` | proof: global-frame instance rejected CONDITIONALLY on UniqueRawNameInsertions only | T18-3 | `071f4dd0` |

## Repair origins

90 separately guarded lexical/semantic repair commits. Full before/after hashes and signature deltas are in MICRO-UNIT-LEDGER; namespace names/occurrence counts are in QUALIFICATION-TABLE.

## Exhausted and unattempted

- L2R16 T12: UniqueRawNameInsertions on the anchor fixture via if-reduction — interface-vs-primitive wall; 3/3 failed, fully reverted.
- The different explicit-dictionary uniqueness data-agreement route was not attempted; it is the first proposed L2R17 micro-unit.

Mechanical verification is not parent-owned mathematical review. No lane-owned production or protected-source change occurred.
