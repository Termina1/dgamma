# L2R2 declaration / copy-origin inventory

All new Idris code is under `research-tests/O6-L2R2-Sources/DGamma/`. The table
lists **42 top-level declarations**, not 42 independent metatheorems. Records
are statement/data packages; their producer scope is explained in the shift
audit. Every source commit adds exactly one top-level declaration and has a
fresh-PASS receipt. C4 additionally contains its approved data-body bundle and
approved snapshot-endpoint adjustment to the existing execution package.

## New declarations and authenticated source commits

| Unit | Final source coordinate / name | Retained fresh PASS | Commit |
|---|---|---|---|
| B1 | `L2R2RetireInsert.idr:24 rootInsertAtAbsence` | `B1-3` | `ccbd70ad` |
| B2 | `L2R2CheckedSnapshot.idr:18 CheckedSnapshotStep` | `B2-1` | `816d90fd` |
| B3 | `L2R2CheckedSnapshot.idr:35 checkedSnapshotObserved` | `B3-1` | `c22d28ff` |
| B4 | `L2R2RetireInsert.idr:43 checkedRootInsert` | `B4-2` | `ccf2d1ab` |
| B5 | `L2R2RetireInsert.idr:64 replaceOtherHeadObserved` | `B5-1` | `4691970d` |
| B6 | `L2R2RetireSquare.idr:18 ChildRetireSnapshotExchange` | `B6-1` | `22dbdff8` |
| B7 | `L2R2RetireInsert.idr:82 retireInsertedSnapshot` | `B7-2` | `b0f901c2` |
| B8 | `L2R2RetireInsert.idr:105 rootRetireSquareAtInsert` | `B8-2` | `4b46548c` |
| B9 | `L2R2RetireInsert.idr:158 rootRetireSquareFromPlan` | `B9-2` | `a7b7543a` |
| B10 | `L2R2RetireInsert.idr:194 commuteRootInsertChildRetire` | `B10-1` | `3fabc497` |
| B11 | `L2R2RemoveSquare.idr:27 ChildRemoveSnapshotExchange` | `B11-1` | `9d91d4e6` |
| B12 | `L2R2RemoveSquare.idr:51 deletedBindingAbsent` | `B12-2` | `292d684a` |
| B13 | `L2R2RemoveSquare.idr:67 removeSquareFromObservations` | `B13-2` | `7c1abf3d` |
| B14 | `L2R2RemoveSquare.idr:115 removeSquareFromLifecycleReplay` | `B14-1` | `3e6318d6` |
| B15 | `L2R2RemoveSquare.idr:164 commuteBeginChildRemove` | `B15-1` | `6d8b7623` |
| B16 | `L2R2RemoveSquare.idr:195 commuteAdvanceChildRemove` | `B16-1` | `1ede1b79` |
| B17 | `L2R2CheckedSnapshot.idr:62 checkedAcrossSnapshot` | `B17-1` | `c247b311` |
| B18 | `L2R2ForeignReplay.idr:21 RetirementReplay` | `B18-1` | `517df1d9` |
| B19 | `L2R2ForeignReplay.idr:42 foreignRetireReplayCPS` | `B19-2` | `d191c330` |
| B20 | `L2R2ForeignReplay.idr:100 replayRetirementBeforeForeignRun` | `B20-1` | `6acd8069` |
| B21 | `L2R2ConditionalGap.idr:19 RemainingGapHeadIsRoot` | `B21-1` | `53a302cc` |
| B22 | `L2R2ConditionalGap.idr:35 extendedZeroGapWithoutRoot` | `B22-2` | `33ccc4e3` |
| C1 | `L2R2SmallStates.idr:17 smallComponent` | `C1-1` | `24da11d8` |
| C2 | `L2R2SmallStates.idr:29 smallState` | `C2-1` | `df3d2e19` |
| C3 | `L2R2SmallExecution.idr:24 SmallNativeExecution` | `C3-1` | `8f6764f5` |
| C4 | `L2R2SmallExecution.idr:44 smallNativeExecution` | `C4-3` | `4e6311ed` |
| C5 | `L2R2SmallExecution.idr:52 smallTrace` | `C5-1` | `e1b69f8e` |
| C6 | `L2R2SmallPlacement.idr:21 smallRootBirth` | `C6-1` | `584733b3` |
| C7 | `L2R2SmallPlacement.idr:35 smallAvailabilityTrail` | `C7-1` | `60a36768` |
| C8 | `L2R2SmallPlacement.idr:53 smallEarlierUnavailable` | `C8-1` | `81133b90` |
| C9 | `L2R2SmallPlacement.idr:68 smallRootEarliest` | `C9-1` | `aec6d46a` |
| C10 | `L2R2SmallPlacement.idr:77 smallStrictPlacementRejected` | `C10-1` | `f56f7a69` |
| C11 | `L2R2SmallBlocks.idr:23 SmallExtendedBlocks` | `C11-1` | `beabc537` |
| C12 | `L2R2SmallBlocks.idr:40 smallExtendedBlocks` | `C12-1` | `f18f1f00` |
| C13 | `L2R2RootSnapshot.idr:26 AvailabilityRootSnapshotExchange` | `C13-1` | `98019d10` |
| C14 | `L2R2RootSnapshot.idr:49 smallRootSnapshotSquare` | `C14-1` | `fc95fdb3` |
| C15 | `L2R2RootPhase.idr:25 supportSetAcrossSnapshot` | `C15-1` | `31a4f060` |
| C16 | `L2R2RootPhase.idr:42 beginSnapshotRootDecreases` | `C16-1` | `ae92c7b3` |
| C17 | `L2R2RootPhase.idr:69 SnapshotRootPhaseStep` | `C17-1` | `f0542848` |
| C18 | `L2R2RootPhase.idr:101 rootPhaseFromSnapshot` | `C18-1` | `e95b397c` |
| C19 | `L2R2RootPhase.idr:126 SmallRootPhaseEvidence` | `C19-2` | `22f1ad1c` |
| C20 | `L2R2RootPhase.idr:149 smallRootPhaseEvidence` | `C20-1` | `141a1d80` |

## New analogues: precise origins and deviations

| New declaration(s) | Origin or reused capital | Change / non-claim |
|---|---|---|
| `ChildRetireSnapshotExchange` | `research/DGamma/CP5L2R1RetireExchange.idr:18 ExactChildRetireExchange` | Auxiliary snapshot analogue: actual source-found own-child evidence; separate replay endpoint; exact world/ordered-bindings equality. Not a CP3 production statement copy. |
| `AvailabilityRootSnapshotExchange` | `research/DGamma/CP5L2R1RootExchange.idr:19 AvailabilityRootExchange` | Authorized separate late endpoint + runtimeSnapshot equality; real native checked edges and cut compatibility retained. Exact old fixture remains parked. |
| `beginSnapshotRootDecreases` | `research/DGamma/CP5L2R1RootExchange.idr:76–77 beginRootExchangeDecreases` | Snapshot/no-suffix counterpart; arbitrary prior count and exact-one local decrease retained; authentic arbitrary suffix is NOT retained. |
| `SnapshotRootPhaseStep`, `rootPhaseFromSnapshot` | Narrow analogy to `research/DGamma/CP5ConfluenceCanonicalSortSpike.idr:1583 CanonicalRootInsertionHoist`; prefix-splicing idea from `CP5L2R1RootExchange.idr:40 rootExchangeInContext` | NOT copies of full O17 statements. Explicit supplied square, arbitrary earlier context, no suffix, native swapped trace, snapshot/support-set equality and local decrease. No ReplayInvariantBundle/global normalizer/placement producer. |
| `CheckedSnapshotStep`, observation bridges | `src/DGamma/CP4RuntimeBindings.idr:12 RuntimeSnapshot`, `:411 applyActionObservationCoherent`, `:446 transportApplyActionAcrossRuntimeSnapshot`; `CP4ProgressNoDeadlock.idr:20 checkedFromRaw` | New small checked-successor package and proved bridges. Does not assert equality of erased registry certificates. |
| `ChildRemoveSnapshotExchange`, Remove producers | `src/DGamma/CP4DeletionBoundaryLifecycleCore.idr:29 LifecycleDeleteRuntimeCommute`; `CP4DeletionBoundaryLifecycleBegin.idr:18 beginOneDeleteRuntimeCommute`; `CP4DeletionBoundaryLifecycleAdvance.idr:56 advanceOneDeleteRuntimeCommute` | New package includes actual source child evidence, Boolean absence observation, real alternate edges and exact snapshot. Public Begin/Advance producers execute the CP4 commuters; they do not accept a commuter oracle. |
| `RetirementReplay`, CPS fold/wrapper | `research/DGamma/CP5L2R1ChildRelocation.idr:136 childRetireBeforeForeignRun` and its foreign lookup frame | New actual whole-run replay fold, still conditional on an explicit LOCAL per-edge checked dispatcher. Not an unconditional upgrade of applicability to replay. |
| `RemainingGapHeadIsRoot`, `extendedZeroGapWithoutRoot` | Existing `CP5L2R1ExtendedZeroGap.BlockBeforeExtended`; `CP3.NoRootOrchestration` | New conditional coverage family/lemma, not a new grammar and not a universal zero-gap producer. |
| `supportSetAcrossSnapshot` | Executable `src/DGamma/CP3.idr:577 supportSet` / underlying `supportFuel` | Congruence proof on ordered runtime bindings. NOT the full `CanonicalSupportTransport` or dependent support-linearization theorem. |
| Small native states, traces, placement, block and phase certificates | Native Calculus/Coeffects insert/replace/delete and actual checked equations | New small-state fixtures; not transparent copies of R174's nested evaluated trace. Literal endpoints where stated; only snapshot equality for alternate root route. |

No new direct copy of the full CP3 canonical schedule or CanonicalSort sorting
result is introduced this shift. The following **inherited** copies remain
explicitly part of the research dependency inventory; they were NOT silently
replaced or made into producers.

## Inherited copied-statement inventory (unchanged in L2R2)

| Research declaration | Exact frozen origin | Status / change |
|---|---|---|
| `CP5ActorLifecycleOnlyExtended.ActorLifecycleOnlyExtended` | `src/DGamma/CP3.idr:1786 ActorLifecycleOnly` | Adds actual own-child Retire/Remove to inherited extended body grammar. No unrelated-root attachment exists. |
| `CP5ActorLifecycleOnlyExtended.LocatedOpenEpisodeBlockExtended` | `src/DGamma/CP3.idr:1824 LocatedOpenEpisodeBlock` | Extended body family; physical occurrence/install/maximality fields retained. |
| `CP5L2R1ExtendedZeroGap.BlockBeforeExtended` | `src/DGamma/CP3.idr:1873 BlockBefore` | Physical order counterpart; no zero-gap field. Two production prefix helpers are expanded, not newly copied as declarations. |
| `CP5AvailabilityAwarePlacement.AvailabilityAwareCanonicalInputPlacement` | `src/DGamma/CP3.idr:3156 CanonicalInputPlacement`, strict root clauses `3164/3173` | Availability-aware replacement, no coercion back to old strict placement. C9 supplies only the actual root's earliest clause. |
| `CP5L2R1PlacementCopies.AvailabilityCanonicalSchedule` | `src/DGamma/CP3.idr:3240 CanonicalSchedule`; `canonicalBlock` at `3256–57`, `inputPlacement` at `3265` | Statement copy substituting extended blocks/order and availability placement; full producer still absent here. |
| `CP5L2R1PlacementCopies.AvailabilityCanonicalSupportTransport` | `research/DGamma/CP5ConfluenceCanonicalSortSpike.idr:93 CanonicalSupportTransport` | Original-order witness retained; only placement field transported to R178 variant. Not a universal reduced-order transport. |
| `CP5L2R1CanonicalSortCopies.AvailabilitySortedClosingFreeTrace` | `research/DGamma/CP5ConfluenceCanonicalSortSpike.idr:118 SortedClosingFreeTrace` | Replay, invariant, endpoint, registration/no-withdrawal fields retained; extended block/range/order and availability-placement substitutions only. No full producer claimed. |

## Forbidden seams and unchanged interfaces

- No new `childRemoveAtFound`, nested R174 exact occurrence/old-strict rejection,
  R192 eleven-edge relocation producer, or exact old C13 root fixture was tried.
- C4's small native route adjustment and C13's **approved snapshot** interface
  are documented deviations, not proof irrelevance.
- No new attachment grammar or frozen O19 conversion is defined.
- Only two predecessor **comments** were repaired by exact byte authentication:
  `research-tests/run-l2r1-check.py` docstring and
  `research-tests/DGamma/L2R1RootHoist.idr` candidate-state comment.
