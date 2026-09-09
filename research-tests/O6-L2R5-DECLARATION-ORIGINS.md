# L2R5 declaration origins and copied-definition inventory

33 retained top-level declarations in10 new modules. Every row has one immediate fresh own-target PASS and a GUARDED COMMIT receipt. A11 and B5 stopped3/3 and were fully reverted; they are NOT among the rows. A12 used the supervisor's explicit one-new-observed-statement gate. No predecessor or production definition was edited.

| Unit | Declaration / current line | Fresh PASS | Commit | Exact status |
|---|---|---|---|---|
| A1 | `L2R5AnchorTransport:anchorBirths` L14 | A1-1 | `3baa3fba` | total executable definition |
| A2 | `L2R5AnchorTransport:anchorBirthsSwap` L25 | A2-1 | `e9abbd95` | proved at stated scope |
| A3 | `L2R5CurrentCut:rootCurrentFromView` L19 | A3-1 | `d2116a31` | proved at stated scope |
| A4 | `L2R5CurrentCut:checkedRootCurrentAvailable` L35 | A4-1 | `5822f06e` | proved at stated scope |
| A5 | `L2R5CurrentCut:admittedSwapCurrentCuts` L53 | A5-1 | `cb60b7d7` | proved at stated scope |
| A6 | `L2R5Extensional:RegistryExtensional` L18 | A6-1 | `0fbc3d33` | defined type |
| A7 | `L2R5Extensional:snapshotIntoExtensional` L31 | A7-1 | `21453f7c` | proved at stated scope |
| A8 | `L2R5Extensional:extensionalMemberKey` L45 | A8-1 | `f8e12a2c` | proved at stated scope |
| A9 | `L2R5Extensional:DeclaredOccupancy` L58 | A9-1 | `49ef79d1` | defined type |
| A10 | `L2R5Extensional:extensionalDeclaredOccupancy` L74 | A10-1 | `c74c1260` | proved at stated scope |
| A12 | `L2R5InsertObserved:insertedLookupTwoObserved` L17 | A12-2 | `0efb83c1` | proved at stated scope |
| A13 | `L2R5InsertObserved:freshInsertEndpointsExtensional` L49 | A13-1 | `71f6de67` | proved at stated scope |
| A14 | `L2R5ExtensionalRetire:replaceLookupExtensionalObserved` L19 | A14-1 | `ca6b2920` | proved at stated scope |
| A15 | `L2R5ExtensionalRetire:replaceExtensional` L44 | A15-1 | `d2d5a35d` | proved at stated scope |
| A16 | `L2R5ExtensionalRetire:CheckedExtensionalStep` L63 | A16-1 | `a625b77b` | defined type |
| A17 | `L2R5ExtensionalRetire:retireExtensionalFromView` L79 | A17-1 | `ca793ff9` | proved at stated scope |
| A18 | `L2R5ExtensionalRetire:checkedRetireAcrossExtensional` L101 | A18-1 | `c60f315a` | proved at stated scope |
| A19 | `L2R5ExtensionalRetire:extensionalTransitive` L117 | A19-1 | `fc9ac87f` | proved at stated scope |
| A20 | `L2R5ExtensionalFixtures:extensionalFixtureEndpoints` L26 | A20-2 | `4ab704a9` | proved at stated scope |
| B1 | `L2R5RetirementFrame:sameOptionalView` L16 | B1-1 | `cc606679` | total executable definition |
| B2 | `L2R5RetirementFrame:RetirementProviderFrame` L28 | B2-1 | `239d9676` | defined type |
| B3 | `L2R5RetirementFrame:retirementProviderFrame` L61 | B3-1 | `85cd102d` | total executable definition |
| B4 | `L2R5ProviderObservation:ProviderHeadObservation` L17 | B4-1 | `76a0b126` | defined package ONLY; producer B5 absent |
| C1 | `L2R5RootCatalog:RootCatalogEntry` L19 | C1-1 | `b3a524f5` | defined type |
| C2 | `L2R5RootCatalog:rootCatalogStep` L29 | C2-1 | `18724c90` | total executable definition |
| C3 | `L2R5RootCatalog:scanRootCatalog` L45 | C3-1 | `e9ab71a5` | total executable definition |
| C4 | `L2R5RootCatalog:RootCatalogContains` L57 | C4-1 | `525730d2` | defined type |
| C5 | `L2R5RootCatalog:rootCatalogHeadComplete` L70 | C5-2 | `77681c9a` | proved at stated scope |
| C6 | `L2R5RootCatalog:rootCatalogTailComplete` L93 | C6-1 | `f82f7f8a` | proved at stated scope |
| C7 | `L2R5RootCatalog:rootCatalogConsComplete` L114 | C7-1 | `601c1400` | proved at stated scope |
| C8 | `L2R5RootCatalog:scanRootLookupComplete` L143 | C8-1 | `ef9b9f9b` | proved at stated scope |
| C9 | `L2R5CatalogFixtures:RuntimeCatalogFixtures` L26 | C9-1 | `935f0aae` | defined type |
| C10 | `L2R5CatalogFixtures:runtimeCatalogFixtures` L45 | C10-1 | `8c603e3b` | proved at stated scope |

## Copy/recipe delta inventory

| New declarations | Origin consulted/reused | Delta / obligations retained |
|---|---|---|
| anchorBirths / anchorBirthsSwap | L2R4AnchorMeasure AnchorEvent, ordinary structural List induction | New runtime projection and ordered-annotation equation with arbitrary prefix/suffix; fixed event annotations only, no native stable-ID assignment theorem |
| rootCurrentFromView / checkedRootCurrentAvailable / admittedSwapCurrentCuts | CP4DeletionSelectedForeignOrchestration.ForeignInsertPlanView; L2R2RootSnapshot.AvailabilityRootSnapshotExchange | New current declaration-freedom extraction and admitted-swap current-cut transport. Original checked edge only for freedom; actual swap certificate remains an explicit premise for transport. Earliest is not an invariant |
| RegistryExtensional / snapshotIntoExtensional | Owner revised endpoint ruling; CP4RuntimeBindings snapshotWorld/snapshotBindings | New normalizer-only world + pointwise lookup relation. No ordered-registry equality or extensional evaluator congruence is presumed |
| extensionalMemberKey / DeclaredOccupancy / extensionalDeclaredOccupancy | Coeffects.memberKey, actual lookupFiber + component declared keys | New derived name membership and bidirectional existential declaration-occupancy transport. Finite provisionsDisjointFrom Bool equivalence remains open |
| insertedLookupTwoObserved / freshInsertEndpointsExtensional | Coeffects.lookupInsertOther and actual insertBinding; supervisor A12 explicit observed-value gate | NEW actual registry statement with BOTH observed Dec arguments/equations; both second-insert freshness proofs produced. General lookup algebra, not native alternate OInsert applicability. Exhausted A11 list-head statement remains absent |
| replaceLookupExtensionalObserved / replaceExtensional | Coeffects.lookupReplaceEntries / lookupReplaceOther | New same-fiber replacement congruence at extensional states, one observed name decision; no ordered-list equality needed |
| CheckedExtensionalStep / retireExtensionalFromView / checkedRetireAcrossExtensional / extensionalTransitive | CP4DeletionBoundaryDeleted.RetireSuccessView; L2R1 childRetireAtFound; L2R2 CheckedSnapshotStep packaging recipe | New ORIGINAL-edge-only ORetire transport with actual alternate successor, same tag, current validity and extensional result. Does not substitute for lifecycle-after-retirement replay |
| extensionalFixtureEndpoints | Original smallNativeExecution.smallAlternateSnapshot and bundlePhaseEvidence.originalToMovedRuntime | New pointwise embeddings of actual existing one-/two-move prefix endpoints. No copied original-state identity; not a new normalizer instance |
| sameOptionalView / RetirementProviderFrame / retirementProviderFrame | Native resolveView, provisionOverlap, retired/isActive; owner B observed-value ruling | New executable actual source/replacement observations with all Bool equations. No unchanged-resolver or successful replay assumed. Key overlap ≠ resolver change |
| ProviderHeadObservation | New observed guard package proposed after L2R4 B7 | Explicit guard Bool + guard equation + both native head equations. TYPE ONLY: B5 producer exhausted3/3 and absent. Not claimed as a proof of invariance |
| RootCatalogEntry / rootCatalogStep / scanRootCatalog | Actual AvailabilityTrace; exhaustive native Action classifier recipe | New executable raw birth catalog scanned FROM trace, original positions retained, not supplied. Root Retire/Remove deliberately not insertion entries |
| RootCatalogContains / rootCatalogHeadComplete / rootCatalogTailComplete / rootCatalogConsComplete / scanRootLookupComplete | L2R4 nativeActionAt; Nat offset transport recipe from L2R4CatalogCoverage | New exact action/ordinal member package and GENERAL completeness for computed catalog. No caller-supplied catalog/completeness callback. Raw root-insert membership, not AttachedBundleOccurrence/AttachedNormalForm |
| RuntimeCatalogFixtures / runtimeCatalogFixtures | SAME L2R2SmallExecution and L2R3BarrierExecution native edges, one-origin states | New full7/8-edge actual annotations, computed catalogs [(4,R3)]/[(4,R3),(5,S4)] and generic C8 theorem instances. No fixture-instantiated AttachedNormalForm |

No body-only companion bundle was requested or used. All L2R1–L2R4 source bytes are unchanged. V0 only touched the exact unchanged L2R4AnchorMeasure target for freshness; its actual old/new mtimes are logged (no claim they were2025 after predecessor checks). New runner scripts were COPIED from L2R4, then updated for exact paths/caps/IDs/stop cases. The draft generator is new docs-only tooling; no Idris compiler/source/cache operation occurs in it.

## Draft-only copies (not new compiled declarations)

D1's CP3-DIFF-DRAFT and REHOME-MANIFEST disclose every Tier-1 rehome rename/quantity delta and source SHA. Original CP3 transitionCount/LocatedActionOccurrence/locatedActionOrdinal bytes are proposed to MOVE, not change. Tier2 connector names/record fragments have NO compiled definitions. The118-entry STATEMENT-FIDELITY inventory records direct frozen signature dependencies; it is not a transitive typechecker, a migration, or proof of future compatibility. No root docs, src/, research/, LocalDiamond, O19/O20, canonical/cross-trace/renaming files were edited.
