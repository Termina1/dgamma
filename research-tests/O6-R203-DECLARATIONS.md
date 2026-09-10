# R203 declaration correspondence and attempts

32 retained top-level declarations; each has one fresh PASS and one exact-source guarded commit. Includes two executable functions, two specification/type declarations, and erased constructive proofs; this is not32 closed paper theorems. All new Idris sources are total.

| Unit | Source:declaration | Retained attempt | Commit |
|---|---|---|---|
| B1 | `research/DGamma/CP5O20WholeClosingJoinSpike.idr:o20SubsequenceOrdinalBounds` | `B1-1` | `df63fb6c` |
| B2 | `research/DGamma/CP5O20WholeClosingJoinSpike.idr:o20OffsetStrictOrder` | `B2-1` | `88f4f0b0` |
| B3 | `research/DGamma/CP5O20WholeClosingJoinSpike.idr:o20WholeEmbeddingReflectsSourceOrder` | `B3-1` | `d5c8a3e2` |
| B4 | `research/DGamma/CP5O20WholeClosingJoinSpike.idr:o20ClosingActionAtAppendLeft` | `B4-2` | `830a8889` |
| B5 | `research/DGamma/CP5O20WholeClosingJoinSpike.idr:o20SplitClosingActionAtAppend` | `B5-1` | `28dc4446` |
| B6 | `research/DGamma/CP5O20WholeClosingJoinSpike.idr:o20DeletionUnloadFreeSegments` | `B6-1` | `ee639059` |
| B7 | `research/DGamma/CP5O20WholeClosingJoinSpike.idr:o20WholeClosingIndexRetainedOrSelectedCenter` | `B7-1` | `c518bde1` |
| B8 | `research/DGamma/CP5O20WholeClosingJoinSpike.idr:o20DeletionRetainedBirthEmbedding` | `B8-1` | `763e9d0b` |
| B9 | `research/DGamma/CP5O20WholeClosingJoinSpike.idr:o20DeletionRetainedClosingBirthOrSelectedParent` | `B9-2` | `bc17af9e` |
| B10 | `research/DGamma/CP5O20WholeClosingJoinSpike.idr:o20LocatedOrdinalTransport` | `B10-2` | `f88b8732` |
| B11 | `research/DGamma/CP5O20WholeClosingJoinSpike.idr:o20ClosingIndexInsideTrace` | `B11-1` | `4e70974a` |
| B12 | `research/DGamma/CP5O20WholeClosingJoinSpike.idr:o20SelectedCenterCloseBirthBefore` | `B12-1` | `66d1f47f` |
| B13 | `research/DGamma/CP5O20WholeClosingJoinSpike.idr:o20ParentInstalledAtRegistrationCut` | `B13-2` | `13be8b57` |
| B14 | `research/DGamma/CP5O20WholeClosingJoinSpike.idr:o20BeforeBirthHasEarlierParentClose` | `B14-1` | `87451394` |
| B15 | `research/DGamma/CP5O20WholeClosingJoinSpike.idr:o20DeletionRetainedClosingBirth` | `B15-1` | `36f0786a` |
| B16 | `research/DGamma/CP5O20WholeClosingJoinSpike.idr:o20EveryDeletedGenerationSelected` | `B16-2` | `eb6e75a4` |
| A1 | `research/DGamma/CP5O20NativeDisappearanceSkipSpike.idr:o20SubsequenceTargetOrdinal` | `A1-2` | `8b633883` |
| A2 | `research/DGamma/CP5O20NativeDisappearanceSkipSpike.idr:o20SubsequenceOrdinalsInverse` | `A2-1` | `bc960f0a` |
| A3 | `research/DGamma/CP5O20NativeDisappearanceSkipSpike.idr:o20SelectedLifecycleTargetAbsent` | `A3-1` | `8153cf6c` |
| A4 | `research/DGamma/CP5O20NativeDisappearanceSkipSpike.idr:o20WholeSelectedLifecycleDisappears` | `A4-1` | `f376483a` |
| A5 | `research-tests/DGamma/R203NativeDisappearancePositive.idr:r203ActualUnloadIsNotEpsilon` | `A5-2` | `d86b7acf` |
| A6 | `research/DGamma/CP5O20GlobalActivationHistorySpike.idr:o20OrdinaryIndexKeepsActivationCounts` | `A6-1` | `a83071a5` |
| A7 | `research/DGamma/CP5O20GlobalActivationHistorySpike.idr:O20NativeActivationScan` | `A7-1` | `3828836b` |
| A8 | `research/DGamma/CP5O20GlobalActivationHistorySpike.idr:o20LeftNativeActivationHistory` | `A8-2` | `a0a30a85` |
| A9 | `research/DGamma/CP5O20GlobalActivationHistorySpike.idr:o20ReplayRetainedEventCounts` | `A9-1` | `693fb232` |
| A10 | `research/DGamma/CP5O20GlobalActivationHistorySpike.idr:o20NativeActivationCounts` | `A10-2` | `b5e7f006` |
| A11 | `research/DGamma/CP5O20GlobalActivationHistorySpike.idr:o20ChronologicalPositions` | `A11-1` | `5a2dab19` |
| A12 | `research/DGamma/CP5O20GlobalActivationHistorySpike.idr:o20NativeChronologicalPositions` | `A12-1` | `8f97c6c4` |
| A13 | `research/DGamma/CP5O20GlobalActivationHistorySpike.idr:o20AcceptedActivationHistories` | `A13-2` | `6c0a23e1` |
| A14 | `research/DGamma/CP5O20GlobalActivationHistorySpike.idr:o20ChronologicalPositionAtPrefix` | `A14-2` | `fcf33bb9` |
| A15 | `research-tests/DGamma/R203GlobalActivationHistoryPositive.idr:r203ClosedBirthConsumesNoRetainedPosition` | `A15-1` | `8d78eee8` |
| A16 | `research-tests/DGamma/R203GlobalActivationHistoryPositive.idr:r203RemovedBirthKeepsHistoricalPosition` | `A16-1` | `f0c80a37` |

## Failed and superseded attempts

- B4-1: expose the actual `Fired` head so native action lookup reduces.
- B9-1: parenthesize the nested dependent-pair pattern.
- B10-1: replace equality-pattern-unified names with `_`.
- B13-1: bind the actual `{before}` state in the installation motive.
- B16-1: **PASS**, not a failure. B16-2 only replaces two redundant explicit source/target index patterns by `_`; exact snapshot transformation is independently authenticated. B16-2 is the committed version.
- A1-1: executable inverse needs erased implicit type/state indices; actual filter and queried Nat remain runtime data.
- A5-1: local filter/proof bindings explicitly quantity0, permitting calls of erased proof functions.
- A8-1: `prefix` is a reserved identifier; rename the event-list variables.
- A10-1: the `index@` alias was opaque in the dependent native scan; use its explicit constructor value.
- A13-1: frozen symmetry helper is private. Do NOT export/change it; use a local erased structural right-side scan producer in the same declaration.
- A14-1: split the queried event activation as well as the preceding event so the nested case-result equation normalizes.

All failures pass on attempt2. No third attempts, exhausted/reverted units, C attempts, or cap extensions. B16-1 stays a genuine uncommitted PASS; it is never laundered as a failure or counted as a guarded source commit.
