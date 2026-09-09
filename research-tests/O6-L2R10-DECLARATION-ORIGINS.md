# L2R10 declaration origins and exact scope

Source boundary **637c0ca1**; **42 checked declarations in11 modules**.
This is Thm73/O20 connector research, not Theorem73 or a normalizer proof.
12 executable definitions,26 erased proofs,4 type/record definitions; the
unique move-existence TYPE is uninhabited. Each row adds ONE declaration.

| Unit | File:line / name | Kind and status | Fresh invocation | Guarded commit |
|---|---|---|---|---|
| A1 | `L2R10OrdinalData.idr:32` / `fixtureDictionaries` | executable: checked total executable definition | A1-1 | `265d4728` |
| A2 | `L2R10OrdinalData.idr:40` / `ordinalDataAgreement` | proof: proved at exact documented scope | A2-1 | `1f61af78` |
| A3 | `L2R10ReleaseAgreement.idr:20` / `releaseAbsentAtDecision` | proof: proved at exact documented scope | A3-1 | `c8f8a79b` |
| A4 | `L2R10ReleaseAgreement.idr:35` / `releaseAbsentFalse` | proof: proved at exact documented scope | A4-1 | `633a6372` |
| A5 | `L2R10ReleaseAgreement.idr:46` / `releasePresentAtBool` | proof: proved at exact documented scope | A5-1 | `642c50f6` |
| A6 | `L2R10ReleaseAgreement.idr:57` / `releaseAgreementAtDec` | proof: proved at exact documented scope | A6-1 | `6c842c05` |
| A7 | `L2R10ReleaseAgreement.idr:72` / `releaseScanAgrees` | proof: proved at exact documented scope | A7-1 | `b24bd0f7` |
| A8 | `L2R10PhaseScan.idr:27` / `phaseParentOwner` | executable: checked total executable definition | A8-1 | `dead1776` |
| A9 | `L2R10PhaseScan.idr:33` / `phaseControlOwner` | executable: checked total executable definition | A9-1 | `5fcec743` |
| A10 | `L2R10PhaseScan.idr:46` / `phaseActionOwner` | executable: checked total executable definition | A10-1 | `0fcb158b` |
| A11 | `L2R10PhaseScan.idr:65` / `phaseEvents` | executable: checked total executable definition | A11-1 | `8680e45d` |
| A12 | `L2R10PhaseScan.idr:78` / `phaseReleaseCheck` | executable: checked total executable definition | A12-1 | `66107d21` |
| A13 | `L2R10PhaseScan.idr:96` / `phaseScanOk` | executable: checked total executable definition | A13-3 | `8e5e630d` |
| A14 | `L2R10PhaseFixtures.idr:36` / `phaseScanFixtureObservations` | proof: proved at exact documented scope | A14-1 | `504f9885` |
| B1 | `L2R10BeginAdapter.idr:29` / `retirementBeginPlanAdapter` | proof: proved at exact documented scope | B1-1 | `c6ee9eb9` |
| B2 | `L2R10BeginAdapter.idr:68` / `replayRetirementBegin` | proof: proved at exact documented scope | B2-1 | `982aec58` |
| B3 | `L2R10AdvanceReplay.idr:28` / `retirementTargetAtFlag` | proof: proved at exact documented scope | B3-1 | `c40c42a7` |
| B4 | `L2R10AdvanceReplay.idr:45` / `retirementTargetSame` | proof: proved at exact documented scope | B4-1 | `e5c371f1` |
| B5 | `L2R10AdvanceReplay.idr:62` / `RetirementAdvanceEquation` | type: checked type, inhabited by retirementAdvanceNative | B5-1 | `5241bd5d` |
| B6 | `L2R10AdvanceReplay.idr:81` / `advanceYieldAtRest` | proof: proved at exact documented scope | B6-1 | `9c804671` |
| B7 | `L2R10AdvanceReplay.idr:133` / `advanceYieldAtMatch` | proof: proved at exact documented scope | B7-1 | `ca6a7dd0` |
| B8 | `L2R10AdvanceReplay.idr:173` / `advanceEmptyAtMatch` | proof: proved at exact documented scope | B8-1 | `42b0cb07` |
| B9 | `L2R10AdvanceReplay.idr:212` / `advanceAtYield` | proof: proved at exact documented scope | B9-1 | `f4a11274` |
| B10 | `L2R10AdvanceReplay.idr:237` / `advanceAtOutcome` | proof: proved at exact documented scope | B10-1 | `ff483623` |
| B11 | `L2R10AdvanceReplay.idr:275` / `advanceAtCapability` | proof: proved at exact documented scope | B11-1 | `1aafc9c8` |
| B12 | `L2R10AdvanceReplay.idr:309` / `advanceAtRemaining` | proof: proved at exact documented scope | B12-1 | `bcd9e0ef` |
| B13 | `L2R10AdvanceReplay.idr:332` / `advanceAtLifecycle` | proof: proved at exact documented scope | B13-1 | `b425983d` |
| B14 | `L2R10AdvanceReplay.idr:371` / `retirementAdvanceNative` | proof: proved at exact documented scope | B14-1 | `862cab09` |
| B15 | `L2R10AdvanceReplay.idr:386` / `replayRetirementAdvance` | proof: proved at exact documented scope | B15-1 | `7d53bc29` |
| B16 | `L2R10LifecycleRoles.idr:30` / `replayRetirementLifecycle` | proof: proved at exact documented scope | B16-1 | `d1f6370a` |
| C1 | `L2R10SplitEdges.idr:30` / `SplitNativeEdge` | type: checked type, only actual root edge instantiated | C1-1 | `3b57a7bc` |
| C2 | `L2R10SplitEdges.idr:39` / `splitRootEdge` | proof: proved at exact documented scope | C2-1 | `72d9d446` |
| D1 | `L2R10UniqueMoveDomain.idr:22` / `GeneralAdmittedMoveExistenceUnique` | type: TYPE ONLY; no inhabitant | D1-1 | `e3b15e9b` |
| D2 | `L2R10UniqueMoveDomain.idr:38` / `uniqueChildBirthBeforeRootExcluded` | proof: proved at exact documented scope | D2-1 | `c953937d` |
| D3 | `L2R10MoveCutObservation.idr:33` / `trailSourceActions` | executable: checked total executable definition | D3-1 | `74df1948` |
| D4 | `L2R10MoveCutObservation.idr:49` / `SelectedSquareCut` | type: checked observation type, produced by observeSelectedMoveCut; NOT a move | D4-1 | `308d8a4c` |
| D5 | `L2R10MoveCutObservation.idr:76` / `selectedCutAtPair` | executable: checked total executable definition | D5-1 | `5ca7c98c` |
| D6 | `L2R10MoveCutObservation.idr:102` / `selectedCutAtLookup` | executable: checked total executable definition | D6-1 | `de0e0419` |
| D7 | `L2R10MoveCutObservation.idr:125` / `selectedCutAtSearch` | executable: checked total executable definition | D7-2 | `f983d44c` |
| D8 | `L2R10MoveCutObservation.idr:153` / `observeSelectedMoveCut` | executable: checked total executable definition | D8-1 | `21dcd522` |
| D9 | `L2R10MoveCutFixtures.idr:55` / `singleSelectedCutObservation` | proof: proved at exact documented scope | D9-1 | `b79f126c` |
| D10 | `L2R10MoveCutFixtures.idr:66` / `bundleSelectedCutObservations` | proof: proved at exact documented scope | D10-1 | `637c0ca1` |

## Source and formulation origins

- A1/A2: NEW monomorphic ω dictionary/data equations over inherited public
  native trails; not frozen L2R9 OrdinalFixtures. A3–A7: NEW single-key native
  Dec/Bool observations, not the exhausted whole-list statement.
- A8–A14: NEW actual actor-core event word and conservative phase checker;
  inherited catalog/anchor data are observed, not replaced by supplied phases.
- B1/B2: original ForeignBeginPlanView ownerShape adapter plus retirement
  snapshot. B3–B15: explicit native Advance decisions/outcomes, with native
  resolveCommittedValuesRetireRegistry transport. B16 inhabits the original
  retained three-role contract, not narrowed ForeignReplay.single.
- C1/C2: NEW single-equation abstract-state type and actual root4→8. C3
  checkedFromRaw + C2 target validity hit18GiB twice and48GiB on exact third
  bytes. C3 fully reverted; C4–C10 unattempted. No frozen old statement retry.
- D1/D2: owner R173 uniqueness restored; actual located-birth count proof.
  D3–D8: NEW source-aware selected-cut observation, not admitted moves.
  D7 generic observed indices use actual distance/catalog equations.
  D9/D10: observations FROM the new producer on old genuine prefix fixtures,
  never projected old admitted-move fields.
- Recipe scripts follow the predecessor one-declaration-generation pattern
  but are lane-owned, compiler-free and reproduce only their stated helpers.

## Failed attempts (none retained as unchecked proof)

- A13-1/A13-2: index' API/type mismatch (Nat/List, then Nat/Fin); corrected
  to head'(drop ordinal events), PASS3/3. A failed commit request was rejected
  before staging; guard behavior and fresh-pass requirement are test-covered.
- C3-1/C3-2:18GiB stops. C3-3: authorized exact48GiB cost stop, STOP3/3.
  Earlier lock polling was stopped before compiler launch and consumed no
  attempt; actual C3-3 had no lock/window operation.
- D7-1: coverage failed on calculated search indices; direct imports checked,
  then explicit observed generic distance/items with own equations PASS2/3.

## Review limits and evidence

Read CP3-DIFF-DRAFT-OVERLAY for exact Tier-2 residues. The independently
authorized predecessor D4 COMMENT repair is not a proof/body/quantity change.
All other predecessor sources/draft and all src/root documents are unchanged.
The archive contains raw source snapshots, diagnostics, command/RSS records,
guard receipts, lock-policy chronology and final validations. The compiler-free
independent verifier reconstructs these facts without importing runner logic;
its focused tests are not human mathematical review. Parent owns that gate.
