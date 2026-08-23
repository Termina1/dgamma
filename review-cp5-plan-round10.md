# Theorem 73 Scoping Plan — Adversarial Review, Round 10

- Reviewed branch: `cp5-thm73-scoping`
- Reviewed commit: `56b5a86d4cc19eab2413b8d002ec3a3b966b730f`
- Immutable production target: `src/DGamma/CP3.idr` blob `2c697e532e83989de8591fa6a4378747c6a501c0`
- Method: repository read-only except this report; all generated probes under `/tmp/thm73-review10-probes`; Idris processes serialized.

## Probe log (appended immediately after each probe)

### Probe 01 — review coordinate and initial worktree state

**Command:** `git rev-parse HEAD; git branch --show-current; git status --short; git status --porcelain=v2 --branch`

**Result:** HEAD and branch match the assigned coordinate. The initial worktree was not fully clean: untracked `paper/` existed before this report was created. No staged entries were reported.

**Classification:** note — coordinate verified; pre-existing untracked paper directory means any blanket “clean worktree” claim must be qualified.

### Probe 02 — immutable production tree and package reachability

**Command:** `git ls-tree 56b5a86 -- src/DGamma/CP3.idr; git diff --exit-code 34b21c9..56b5a86 -- src dgamma.ipkg; sed -n '1,220p' dgamma.ipkg`

**Result:** `CP3.idr` is exactly blob `2c697e532e83989de8591fa6a4378747c6a501c0`; the entire `src/` plus `dgamma.ipkg` diff from the stated production baseline is empty (`DIFF_EXIT=0`). The package module list contains only `src/DGamma/*`; no `research` or `research-tests` module is reachable through `dgamma.ipkg`.

**Classification:** note — production immutability and research exclusion are confirmed.

### Probe 03 — tracking and inventory of every round-10 artifact

**Command:** `git ls-tree -r --name-only 56b5a86` filtered for plan, prior reports, research spikes, R10 tests and suite; count `.idr` files; query cited paths.

**Result:** All nine prior reports and `THM73-PLAN.md` are tracked. Exactly five research spike modules and 43 research-test Idris modules are tracked. All eight cited R10 modules are tracked under `research-tests/DGamma/` (the task's module-style citations omit that directory component), and `research-tests/run-r10-suite.sh` is tracked/executable (`100755`, blob `e4ce5e...`).

**Classification:** note — tracking claim confirmed (with benign path-prefix clarification).

### Probe 04 — prior front and revision-10 claim audit

**Command:** read `review-cp5-plan-round9.md` in full and `THM73-PLAN.md` revision 10 in full.

**Result:** Round 9's blocker was free occurrence maps in `AdjacentSwapResult`, `ClosingFreeReduction`, and `SortedClosingFreeTrace`; its majors were absent concrete O16/origin fixtures, absent reproducible suite, and undercharging. Revision 10 claims to close the free-map interfaces, honestly withdraw concrete O16, add raw constructor materializers/range producers, commit a 43-module suite, and revise to 32 holes / 129–226.

**Classification:** note — attack front is taken from the actual previous report, not the revision's closure table.

### Probe 05 — exact external release copy and toolchain

**Command:** recreate `/tmp/thm73-review10-probes/release` via `git archive 56b5a86 -- src research research-tests dgamma.ipkg THM73-PLAN.md`; hash CP3; inventory modules; `idris2 --version`.

**Result:** Idris 2 is 0.8.0. Archived CP3 SHA-256 is `23a9a0d3c8e4475f40ee4c85227683ecea51cc8f94bffc9f001e058f9b54e2ec`, matching the immutable blob's prior release hash. Archive contains 258 files, exactly five research Idris modules, and exactly 43 research-test Idris modules.

**Classification:** note — every following generated probe is based on the exact tracked release tree outside the repository.

### Probe 06 — exact type-declaration anchors

**Command:** `rg -n` over exact release research/tests for producer records and map/fold projections; save output to `/tmp/thm73-review10-probes/declaration-anchors.txt`.

**Result:** Source anchors are LocalDiamond 436–559 and 596–703, DeletionChain 228–485, CanonicalSort 106–166, CrossTrace 45 onward, and the raw fixture beginning at test line 59. The claimed types/functions exist in tracked source and will be read at those exact declarations.

**Classification:** note — declaration existence confirmed; no semantic claim accepted yet.

### Probe 07 — first-source adjacent-swap type audit

**Command:** line-numbered inspection of `CP5ConfluenceLocalDiamondSpike.idr:350–735`, saved as `/tmp/thm73-review10-probes/local-seal-source.txt`.

**Result:** `AdjacentSwapResult` has no occurrence-map field. Its `originalDecomposition` is equality from the exact constructor-indexed `tracePrefix/left/right/suffix` append to the exact `original`; `swappedDecomposition` is equality from its actual `swappedTrace` to the exact prefix/moved pair/actual replayed suffix. `swappedOccurrenceFold` invokes the single global O6 function with those exact indexed values and both equality proofs; the public map is only its projection. The fold record's laws pin moved-right to `S (transitionCount prefix)`, moved-left to `transitionCount prefix`, and suffix outputs to the same absolute ordinal. Finite sorting composes only these projections.

**Classification:** note — source shape supports the claim. Equality/decomposition substitution and hole-opacity attacks are still to be type-checked, not inferred from prose.

### Probe 08 — deletion step/derivation seal source audit

**Command:** line-numbered inspection of `CP5ConfluenceDeletionChainSpike.idr:150–525`, saved as `/tmp/thm73-review10-probes/deletion-seal-source.txt`.

**Result:** `DeletionChainStep` still stores a runtime correspondence, but its erased field requires literal propositional equality to the single exact-argument O9 fold (trace, premises, candidate, actual `deletionResult`). `ClosingFreeDeletionDerivation` threads actual such steps over each result's `survivingTrace`; the recursive fold composes each sealed field. Core/reduction records have no map fields and project the recursive fold from their exact carried derivations.

**Classification:** note — type shape confirms the intended seal. Because the O9 fold body is a deliberate research hole, separate probes must distinguish “fixed but unproved output” from “client-selectable output.”

### Probe 09 — sorting, accounting, capital, and O16-renaming source audit

**Command:** line-numbered inspection of `CP5ConfluenceCanonicalSortSpike.idr:1–700`, saved as `/tmp/thm73-review10-probes/canonical-source.txt`.

**Result:** `SortedClosingFreeTrace` stores an exact finite adjacent-swap derivation and no occurrence map; `sortingOccurrenceCorrespondence` is its fold projection. The deletion+sorting composition feeds accounting and O18. O18 retains a runtime schedule only under equality to `producerCanonicalSchedule` and projects the occurrence map from reduction+sorting. The old fixture is fully renamed to `AbstractTwoBirthOneWithdrawalAssembly`, assembler, and accounting projection; its source comments explicitly say it assumes all hard reduction/sorting/accounting premises and is not concrete.

**Classification:** note — claimed type repair and honest O16 source boundary are present; plan/comment search and attacks remain.

### Probe 10 — suite cardinality and harness source audit

**Command:** line-numbered inspection of `research-tests/run-r10-suite.sh`; enumerate all tracked test modules.

**Result:** Script serially builds production, checks exactly five named spikes, 24 positives, and 19 negatives. The arrays cover all 43 tracked test modules exactly once. Negatives require nonzero exit plus one of three broad diagnostics (`Mismatch between`, `Can't solve constraint`, `not a valid impossible`); this rejects accidental success but is not module-specific enough by itself to prove the *right* boundary. No parallelism occurs.

**Classification:** note — counts and serial structure pass; module-specific negative-source inspection and a fresh run are required.

### Probe 11 — fresh merged-source positive check (first attempt)

**Command:** merge exact archived `src/DGamma`, `research/DGamma`, and tracked tests under `/tmp/thm73-review10-probes/all/DGamma`; delete TTCs; run `idris2 --check --source-dir all R10ProvenanceProjectionPositive.idr`.

**Result:** The merged root contains 255 modules. The unseeded source check was host-killed with exit 137 before yielding a type result, matching the disclosed host-pressure failure mode.

**Classification:** note — resource failure only; mandatory serial retry will use an exact external production build/TTC seed before any conclusion.

### Probe 12 — exact external production build (first attempt)

**Command:** remove external `build/`; run `idris2 --build dgamma.ipkg` in the exact archived release.

**Result:** Host killed Idris (`Killed: 9`, exit 137) before a terminal build counter. No type-level conclusion.

**Classification:** note — disclosed resource failure reproduced; retry required after checking for stale Idris/Chez processes and using a fresh seeded archive if available.

### Probe 13 — host-pressure/stale-process diagnosis

**Command:** `ps` for Idris/Chez; locate repo TTC seed; inspect build size, disk, and `vm_stat`.

**Result:** No stale Idris/Chez process exists. The repo has a production TTC root at `build/ttc/2025081600` and a 966 MB build seed; disk has 160 GiB free and system free pages are ample. Exit 137 appears to be per-process/host policy rather than concurrent Idris pollution.

**Classification:** note — concurrency rule respected; use the exact unchanged production TTC seed, then force a serialized build closure check.

### Probe 14 — seeded exact external package closure

**Command:** copy the existing production `build/` seed into the exact archived release (permitted because Probe 02 proved `src/` and `dgamma.ipkg` byte-identical to baseline); run `idris2 --build dgamma.ipkg` serially.

**Result:** Exit 0. All seeded interfaces were accepted as up-to-date; Idris emitted no module counters. This confirms seeded package closure but does not independently reproduce a fresh 207/207 compile.

**Classification:** note — package closure passes; disclosed fresh-build host-kill remains a residual environment limitation.

### Probe 15 — source-seeded local-diamond spike check

**Command:** set `IDRIS2_PATH` to exact external production TTC root; remove `research/build`; serially `idris2 --source-dir research --check CP5ConfluenceLocalDiamondSpike.idr`.

**Result:** Exit 0 with no diagnostic. The first research spike elaborates against the exact production interfaces under the seeded strategy.

**Classification:** note — source interface passes.

### Probe 16 — remaining four research spikes

**Command:** with exact production TTC seed, serially check DeletionChain, CanonicalSort, RenamingComposition, and CrossTrace under `--source-dir research`.

**Result:** 4/4 exit 0. Together with Probe 15, all five tracked research spikes elaborate serially.

**Classification:** note — spike front passes.

### Probe 17 — source projection positive

**Command:** serially check tracked `R10ProvenanceProjectionPositive.idr` against exact seeded production/research TTCs.

**Result:** Exit 0. Adjacent result, deletion core/reduction, and sorting map equations are all definitionally `Refl` projections at their advertised fold boundaries.

**Classification:** note — positive projection claim passes.

### Probe 18 — tracked adjacent-map replacement negative

**Command:** delete any test TTC; check `R10AdjacentSwapMapCloneNegative.idr` expecting failure; inspect first error.

**Result:** Exit 1 at the intended `Refl`: Idris cannot solve `alternate` versus `(swappedOccurrenceFold result).operationalOccurrenceCorrespondence`.

**Classification:** note — retained Probe-70 analogue fails at the public projection. A direct constructor/decomposition clone is still needed because this test only asks for arbitrary equality.

### Probe 19 — tracked deletion-step replacement negative

**Command:** fresh check `R10DeletionStepMapCloneNegative.idr` expecting failure; inspect first error.

**Result:** Exit 1 at `Refl`, but the diagnostic is only `alternate` versus `step.deletionOccurrenceCorrespondence`; it does not exercise the constructor seal/equality field.

**Classification:** minor — the named tracked test is weaker than its “map clone” name/comment. The interface may still be sound, but a direct clone reusing all old fields is necessary before accepting the seal.

### Probe 20 — tracked reduction replacement negative

**Command:** fresh check `R10ReductionMapCloneNegative.idr` expecting failure; inspect first error.

**Result:** Exit 1 at the intended boundary: `alternate` cannot unify with `closingFreeDeletionOccurrenceFold (reductionDeletionDerivation reduction)`.

**Classification:** note — reduction output has no free map slot; direct arbitrary replacement fails before accounting.

### Probe 21 — tracked sorting replacement negative

**Command:** fresh check `R10SortedMapCloneNegative.idr` expecting failure; inspect first error.

**Result:** Exit 1: `alternate` cannot unify with `finiteDerivationOccurrenceCorrespondence (sortingAdjacentDerivation sorted)`.

**Classification:** note — sorting output has no free map slot; arbitrary replacement fails before accounting.

### Probe 22 — tracked coherent-both-halves capital negative

**Command:** fresh check `R10CoherentBothHalvesCapitalNegative.idr` expecting failure; inspect first error.

**Result:** Exit 1, but only at the tautologically impossible universal equality `alternate = canonicalOccurrenceCorrespondence capital`; it does not attempt assembly through producer records.

**Classification:** minor — the tracked capital negative is weaker than the round-9 Probe-36/68 laundering attack. Direct source-record cloning and assembly-path probes remain necessary.

### Probe 23 — direct deletion-step constructor clone (first attempt)

**Command:** compile generated `R10DirectDeletionStepCloneNegative.idr` from a separate `/tmp/.../probe-src` with absolute `IDRIS2_PATH` to exact seeded TTCs.

**Result:** Invalid harness run: Idris reports `CP5ConfluenceDeletionChainSpike not found` yet anomalously exits 0. The probe body was not elaborated.

**Classification:** note — import-path failure only; relocate generated probe into the external release's `research-tests` source root and retry. This run is not evidence for the seal.

### Probe 24 — direct deletion-step constructor clone (valid retry)

**Command:** relocate generated probe into external `release/research-tests/DGamma`; compile while replacing only the runtime occurrence map and reusing all eleven original constructor fields/proofs.

**Result:** Exit 1 exactly at reuse of `deletionOccurrenceCorrespondenceExact`: old `step.deletionOccurrenceCorrespondence` cannot unify with `alternate`.

**Classification:** note — the erased equality genuinely seals the constructor before O10/accounting; this stronger round-9 Probe-32 analogue passes.

### Probe 25 — O9 hole-opacity attack with arbitrary map and `Refl`

**Command:** generated direct constructor clone sets the runtime map to arbitrary `alternate` and supplies `Refl` for equality to `deletionStepOperationalOccurrenceFoldSpike`; compile expecting failure.

**Result:** Exit 1 exactly at the equality field. Idris displays the fold as opaque `?deletionStepOperationalOccurrenceFoldSpike_rhs ...` and cannot unify it with `alternate`.

**Classification:** note — a hole-bodied fold is fixed/opaque to clients, not an import-time metavariable they can instantiate. The named hole defers correctness of the fixed fold's output; it does not leave a caller-selectable map slot.

### Probe 26 — O9 seal with caller-supplied genuine equality

**Command:** generated positive reconstructs the step with `alternate` only when given erased `alternate = deletionStepOperationalOccurrenceFoldSpike ... exact-result`; check serially.

**Result:** Exit 0 (1/1). Ordinary equality elimination/transport is accepted exactly when the caller proves the map equals the fixed fold.

**Classification:** note — honest scope: before O9 is proved, the seal pins provenance to an opaque named output, not to a known executable implementation. Correctness is deferred to the catalogued O9 hole; caller choice is not.

### Probe 27 — level-up decomposition substitution attack

**Command:** generated positive (a) proves uniqueness of equality proofs, (b) reconstructs `MkAdjacentSwapResult` with caller-supplied proofs of the exact original/swapped decomposition equations while reusing every semantic field, and (c) proves the projected occurrence map is unchanged after such proof substitution.

**Result:** Exit 0 (1/1). Any accepted decomposition is necessarily proof of the exact constructor-indexed append equation. Equality-proof uniqueness rewrites both supplied proofs to the original record proofs, after which map equality is `Refl`.

**Classification:** note — decomposition proofs are syntactically choosable but cannot carry a laundered map or denote a different trace. The exact trace/prefix/moved-transition/replayed-suffix values—not free record claims—index their equality types. The round-10 level-up attack does not break the seal.

### Probe 28 — raw origin “fixture” and smuggled-field audit

**Command:** line-numbered read of all 421 lines of `R10OperationalOriginPlanFixturesPositive.idr`; grep constructor uses and every occurrence/map/result/derivation/label/plan/whole token; compare with `BlockCrossingOriginPlan`/`WholeBlockSwapDerivation` source.

**Result:** The materializer genuinely constructs `MkAdjacentSwapResult`, `FiniteAdjacentSwapStep`, `CrossingOriginPlanStep`, `NonEmptyAdjacentSwap`, and (through R9 Cartesian wrappers) `MkWholeBlockSwapDerivation`. However, `RawOperationalOriginPlan` **does carry an occurrence correspondence** twice in its declaration: as the `prefixOccurrences` index (lines 73–74) and as each `RawOriginStep` argument (113–114). Its origin equalities and recursive tail are essentially the hard fields of `BlockCrossingOriginPlan` before repackaging. Moreover, there is no term-level construction of `RawOriginStep` anywhere: all occurrences are declaration/pattern matches. The 1×1/2×1/2×2 exports are generic functions accepting a prebuilt raw recursive plan, safety, and count equalities; they are not closed fixtures.

At the whole-entry types, the initial `prefixOccurrences` index is fixed to identity and every recursive tail is fixed to composition with the sealed swap projection, so this map argument is not a demonstrated laundering hole. But the plan's explicit “does not store ... occurrence map” and “fixtures” descriptions overstate the artifact.

**Classification:** major — tracked generic constructor repackaging exists, but the claimed genuinely raw/no-map origin fixtures do not. This is a calibration/evidence defect; the sealed top-level index prevents elevating it to an interface blocker on present evidence.

### Probe 29 — tracked operational-origin module elaboration

**Command:** delete its TTC; serially check `R10OperationalOriginPlanFixturesPositive.idr`.

**Result:** Exit 0, terminal `4/4`. The generic materializer and 1×1/2×1/2×2 wrapper telescopes type-check. This does not negate Probe 28: no `RawOriginStep` value is constructed by the module.

**Classification:** note — type composition passes; fixture calibration remains major.

### Probe 30 — actor-block decomposition fixture source audit

**Command:** line-numbered read of all 276 lines of `R10ActorBlockDecompositionFixturesPositive.idr`; grep constructor/range assumptions.

**Result:** The three assemblers call `MkActorBlockDecomposition` directly. They assume blocks, ordering, coverage, distinct actors, and exact start/count equalities (as disclosed), but accept no range-disjointness function. Each defines the full four-orientation `ranges` function locally and derives contradictions by finite-bound elimination and exact Nat equalities for 1×1, 2×1, and 2×2.

**Classification:** note — range disjointness is genuinely proved internally from the admitted exact geometry; this claimed calibration passes.

### Probe 31 — actor-block decomposition module elaboration

**Command:** delete its TTC; serially check `R10ActorBlockDecompositionFixturesPositive.idr`.

**Result:** Exit 0 (1/1).

**Classification:** note — internal range-law constructions elaborate.

### Probe 32 — honest O16 withdrawal and rename completeness

**Command:** repo-archive search for old fixture/assembler/accounting names, `rawTwoBirthOneWithdrawalProducer`, and all concrete/nontrivial O16/two-birth claims in plan/research/tests.

**Result:** Old public names and `rawTwoBirthOneWithdrawalProducer` are absent. Every concrete O16 occurrence in the plan says unresolved, withdrawn, absent, XL gate, or future phase-F work. Source uses only the `Abstract...` names and comments that all hard laws are assumed. No lingering concrete-calibration claim found.

**Classification:** note — honest withdrawal is complete.

### Probe 33 — exact research-hole inventory

**Command:** Python regex scan of every tracked `research/DGamma/*.idr` for all `?identifier` occurrences and unique `?*_rhs` names; print each name.

**Result:** Exact split: canonical 6, cross 4, deletion 11, local 9, renaming 2; total **32**. Every question-mark identifier is one of these unique named RHS holes; no hidden extra question mark.

**Classification:** note — exact hole count passes.

### Probe 34 — forward/reverse O1–O23 hole reconciliation

**Command:** inspect every hole's complete declaration/comment from `/tmp/thm73-review10-probes/hole-contexts.txt`; map each name both directions to plan obligations.

**Result:** Exact bijection holds:

- O1: same-external refl/trans, endpoint refl/trans, composed modulo endpoint (5); O2: relational/deletion independence transports (2).
- O3: A/A (1); O4: A/O + O/A (2); O5: O/O (1); O6: adjacent operational fold + suffix + whole operational block swap (3).
- O7 scan (1); O8 selection (1); O9 deletion operational fold + enriched step (2); O10 recursive core (1); O11 cumulative accounting (1).
- O12 shape (1); O13 complete (0); O14 ordering (1); O15 support transport (1); O16 accounting (1); O17 sort (1); O18 capital (1).
- O19 support matching + selector (2); O20 convergence (1); O21 two scanner inductions + replayed endpoint composition (3); O22/O23 complete (0).

Forward counts sum 32 and every named hole appears exactly once in reverse.

**Classification:** note — hole-to-obligation reconciliation passes.

### Probe 35 — phase arithmetic, gates, and estimate credibility

**Command:** independently sum A 8–15, B 27–47, C 12–21, D 12–23, E 7–13, F 23–41, G 36–58, H 4–8; grep mandatory/re-estimation/XL gates.

**Result:** Exact sum is **129–226**. Four executive re-estimation gates and XL labels are explicit, including reachable repeated-Iter (not raw materialization), concrete O16, and accepted scanner proof. The large B/F/G ranges at least acknowledge the hard work. Probe 28 weakens B's claimed completed calibration, but the reachable fixture is explicitly still gated; no arithmetic error or obvious uncharged interface repair has yet been established.

**Classification:** note — arithmetic passes; estimate remains high-uncertainty research planning, with origin calibration caveat.

### Probe 36 — escape-hatch and hole hygiene scan

**Command:** scan exact archive `src`, `research`, and `research-tests` for named holes, `believe_me`, `assert_total`, `%default partial`, postulate/axiom declarations.

**Result:** `src` has no question-mark hole and no escape; the lone `postulate` token is a CP3 doc comment saying none is used. `research-tests` is hole/escape-free. `research` has exactly the 32 already-counted named holes and no other escape token.

**Classification:** note — production/test hygiene passes; deliberate research holes are fully catalogued.

### Probe 37 — authoritative tracked suite, fresh research/test TTC run

**Command:** delete external TTCs for all five spikes and all research-test modules; run exact tracked `bash research-tests/run-r10-suite.sh` serially; count markers.

**Result:** Exit 0 with `R10_REPRODUCIBLE_SUITE=passed`; exactly 5 spike, 24 positive, and 19 negative markers. All research/test modules were forced through fresh checks; production used the accepted seed after the unseeded host kills.

**Classification:** note — reproducibility script and declared cardinalities pass exactly.

### Probe 38 — module-specific rerun of all 19 negatives

**Command:** delete each negative TTC; run all 19 serially; require nonzero; capture each first error in `/tmp/thm73-review10-probes/probe38-negative-errors.txt`.

**Result:** 19/19 fail. Diagnostics match their declared fronts: source/reduction/sort/capital map projections, mixed/stale/polluted schedules, detached safety, wrong scanner generation, duplicate label, wrong root/birth/public schedule/shifted node/occurrence/trace, and finite-vs-whole nonempty derivation. No parser/import/not-found failure occurs.

**Classification:** note — suite negatives reject for substantive dependent boundaries. The two R10 “clone” tests already identified as weak in Probes 19/22 remain a test-quality caveat, covered by stronger generated attacks where applicable.

### Probe 39 — ambiguous wrong-birth/zero-node diagnostics drill-down

**Command:** inspect full source and error for `R8BridgeWrongBirthNegative`; inspect full zero-derivation error.

**Result:** Wrong-birth fails specifically because `()` cannot inhabit the required accepted generation-forward equality. Zero-node fails because `FiniteAdjacentSwapDone` cannot inhabit the required `WholeBlockSwapDerivation` field. Both are intended boundaries, not generic/vacuous failures.

**Classification:** note — retained wrong-birth and zero-node negatives are calibrated.

### Probe 40 — positive-suite vacuity/static audit

**Command:** inventory every positive module's declarations/bodies and line counts; grep all tracked positive tests for commented-out declarations, `Unit`/`()`, identity-only bodies, and empty code.

**Result:** No commented-out test body, hole, empty module, or unit-returning “success” theorem was found. Small modules apply substantive indexed theorems/projections; larger modules construct static fixtures, scanner equalities, Cartesian proofs, or producer/consumer telescopes. Some positives intentionally only calibrate hole-bearing function application (e.g. R7 boundaries) and the R10 origin module only repackages a supplied raw plan (Probe 28), but none passes by a trivial `Unit` conclusion.

**Classification:** note — no vacuous positive beyond the separately classified origin-calibration overstatement.

### Probe 41 — O6 fold-signature completeness attack (prefix gap)

**Command:** generated `R10OperationalFoldMissingPrefixPositive` reconstructs `AdjacentSwapOperationalOccurrenceFold` from an arbitrary correspondence plus exactly the two moved-node ordinal laws and suffix ordinal law—without any premise about occurrences in the untouched prefix.

**Result:** Exit 0 (1/1). The record contract has no law for ordinals `< transitionCount prefixTrace`. `ActionRegistrationReplayCorrespondence` preserves action/tag and generated coherence but does not make the all-action origin map injective or ordinal-preserving. Therefore repeated same-action/same-tag prefix transitions may be collapsed or permuted by a candidate O6 body while all advertised fold fields still type-check.

**Classification:** blocker — first-source authenticity is incomplete. Add an exact prefix-origin law (and retain moved/suffix laws), then make source-seal/whole-plan consumers project it. A globally fixed hole prevents caller replacement but does not make an under-specified output semantically operational.

### Probe 42 — O9 fold-signature semantic attack

**Command:** generated positive mirrors all exact O9 indices (trace, premises, candidate, immutable deletion result) and returns an arbitrary `ActionRegistrationReplayCorrespondence trace (survivingTrace result)`; no occurrence/subsequence law is required.

**Result:** Exit 0 (1/1). The immutable `DeletionResult` contains `GenerationActionSubsequence` evidence for before/episode/after, but `deletionStepOperationalOccurrenceFoldSpike`'s codomain is only the generic correspondence record. Its type states no equation connecting each surviving occurrence to those retained-subsequence embeddings or to a computed original ordinal.

**Classification:** blocker — the erased equality pins a step to one opaque family application, but the O9 hole contract does not specify operational deletion provenance. Add an explicit deletion-fold certificate with per-survivor origin/ordinal equations derived from the exact subsequence evidence; seal to that certificate/projection. Until then “operational fold” is a name/comment, not a type property.

### Probe 43 — seeded production module rebuild counter

**Command:** delete exact external `DGamma/CalculusChecks.ttc`; rerun package build.

**Result:** Exit 0; Idris freshly rebuilt the invalidated module as `9/207: Building DGamma.CalculusChecks`. This confirms the package's 207-module graph and seeded source/TTC compatibility, though not a fresh all-module compile.

**Classification:** note — seeded production closure strengthened; full unseeded run remains host-killed as disclosed.

### Probe 44 — exact seeded 207/207 release build

**Command:** delete exact external `DGamma/CP4ProgressProof.ttc`; rerun `idris2 --build dgamma.ipkg` serially.

**Result:** Exit 0 with terminal `207/207: Building DGamma.CP4ProgressProof`. This reproduces the disclosed seeded exact archive result after two honest unseeded exit-137 failures.

**Classification:** note — seeded release build claim passes exactly.

### Probe 45 — immutable theorem statement recheck

**Command:** locate `confluenceTheorem`; SHA-256 `git show` of CP3 at baseline and target; production diff exit check.

**Result:** Statement remains at CP3 lines 3785–; baseline and target SHA-256 are identical (`23a9a0...e2ec`); `git diff --exit-code 34b21c9..56b5a86 -- src dgamma.ipkg` returns 0.

**Classification:** note — immutable target and all production sources remain untouched.

### Probe 46 — raw-plan occurrence-map laundering at whole root

**Command:** generated negative attempts to reindex a `RawOperationalOriginPlan` carrying arbitrary source→source `alternate` as the identity-root raw input required by all whole constructors.

**Result:** Exit 1 at exact `alternate` versus `identityActionRegistrationReplayCorrespondence sourceTrace` index mismatch.

**Classification:** note — Probe 28's smuggled-map/documentation defect does not itself permit whole-root laundering. The map should still be removed from the “no map” claim or made an implicit, explicitly sealed threaded index.

### Probe 47 — claimed retained-negative artifact search

**Command:** search tracked plan/research/tests for generated-only retarget, tree-only clone, bridge wrong-generation, and the named map/public/wrong boundaries.

**Result:** `R8PublicScheduleCannotReachBridgeNegative`, wrong-birth, wrong-occurrence, wrong-trace, and scanner wrong-generation are tracked. **No generated-only retarget module and no tree-only capital clone module exist**, despite THM73-PLAN lines 160–161 explicitly claiming both are retained in the committed suite. There is also no dedicated bridge wrong-generation artifact; the wrong-birth test fails by omitting that exact equation, while the only named wrong-generation test is scanner-specific.

**Classification:** major — the 43-module script is reproducible, but its claimed retained front is incomplete. This repeats the suite-evidence issue at a narrower set of exact round-9 attacks.

### Probe 48 — regenerated generated-only retarget attack

**Command:** generated direct record clone keeps generation bijection, all-action origin/tag, coherence proof, and ordinal proof, but substitutes only `replayGeneratedRegistrationOrigin`.

**Result:** Exit 1 at the old coherence field: original generated origin cannot unify with `alternateGenerated`. The interface still rejects generated-only retargeting.

**Classification:** note — type boundary passes, but this exact required negative is temporary only and must be tracked to repair Probe 47.

### Probe 49 — regenerated tree/schedule-only capital clone

**Command:** generated direct O18 clone substitutes only the runtime `CanonicalSchedule` (therefore allowing a tree-only changed schedule) and reuses every other capital field/proof.

**Result:** Exit 1 at `capitalCanonicalScheduleExact`: old runtime schedule cannot unify with `replacement`.

**Classification:** note — final capital seal passes, but the required retained artifact is absent from the tracked suite (Probe 47).

### Probe 50 — final coordinate/index/worktree/process hygiene

**Command:** recheck HEAD, CP3 blob, tracked worktree diff count, staged count, status, active Idris/Chez, report line count.

**Result:** Exact HEAD `56b5a86...`; CP3 blob exact `2c697e...`; tracked diff count 0; staged count 0; no active Idris/Chez process (only the diagnostic shell/grep self-match). Status contains only pre-existing untracked `paper/` and the permitted new review report. Probe log was 411 lines before this entry.

**Classification:** note — tracked tree/index and process hygiene pass.

## Claimed-fix disposition

| # | Revision-10 claim | Checked disposition |
|---:|---|---|
| 1 | Adjacent source seal, no free result map, exact decompositions | **Partial / interface blocker.** No map field; exact decompositions are genuine and proof substitution cannot retarget the map; clone fails. But the fold certificate omits all untouched-prefix origins (Probe 41). |
| 2 | O9 deletion map sealed to operational fold; recursive reduction projections | **Partial / interface blocker.** Constructor equality and recursive projection seals work. The fixed O9 codomain states no operational-subsequence origin law, so the opaque hole is semantically under-specified (Probe 42). |
| 3 | Sorting carries finite actual derivation; O18 projects source-sealed chain | **Pass conditional on source contracts.** No free sort/capital map slot; direct replacements fail. O6/O9 under-specification propagates into these projections. |
| 4 | Concrete O16 honestly withdrawn | **Pass.** Rename and withdrawal are complete; concrete O16 remains explicit XL gate. |
| 5 | Raw origin/decomposition materialization fixtures | **Mixed.** Range laws are internally proved and elaborate. Origin materializer constructs all advertised wrapper constructors, but its “raw” family stores a prefix occurrence map and exact origin equations and no code constructs even one `RawOriginStep`; exports accept a prebuilt raw recursive plan. |
| 6 | Reproducible 5 + 24 + 19 suite and retained front | **Cardinality/run pass; coverage claim fails.** Exact suite passes, and every negative has a substantive error. Generated-only retarget and tree-only capital clone are claimed retained but absent. |
| 7 | Exactly 32 holes; exact 129–226 | **Pass arithmetically.** Exact 6/4/11/9/2, exact reverse O-map, exact row sum. Readiness/grade credibility fails until O6/O9 contracts and calibration are repaired. |
| 8 | Release closure and disclosed host kill | **Pass with disclosed environment qualification.** Unseeded builds were killed; exact seeded rebuild reached 207/207. Production diff/CP3/isolation/escapes/index checks pass. |

## Numbered findings

1. **blocker — O6's “first-source” fold does not constrain the untouched prefix** (`research/DGamma/CP5ConfluenceLocalDiamondSpike.idr:431–475`). The record constrains the moved-right ordinal, moved-left ordinal, and occurrences at target ordinals at least `prefixCount + 2`. It has no field for target ordinals below `prefixCount`. The generic action correspondence neither preserves all ordinals nor requires its all-action map to be injective. Probe 41 constructs the complete fold record from an arbitrary map and exactly the advertised three laws, with no prefix premise. Repeated same-action/same-tag prefix transitions can therefore be collapsed or permuted by a hole body without violating the O6 type. This matters when maps compose across adjacent swaps and when transitions remain untouched throughout sorting. “Globally fixed” is not equivalent to “operationally authentic.”

2. **blocker — O9 seals to an opaque function whose type contains no deletion-origin specification** (`research/DGamma/CP5ConfluenceDeletionChainSpike.idr:208–258`; immutable `src/DGamma/CP3.idr:3642–3700`). The equality field genuinely prevents a caller from cloning a step with an unequal map (Probes 24–26). But `deletionStepOperationalOccurrenceFoldSpike` returns only the generic correspondence record. It states no equation connecting a surviving occurrence to `beforeDeletion`, `episodeDeletion`, or `afterDeletion`'s exact `GenerationActionSubsequence` evidence, no retained-position embedding, and no source ordinal law. Probe 42 confirms any correspondence between the indexed traces inhabits the codomain without additional provenance. Thus the hole is fixed but semantically unconstrained: a wrong coherent family is a valid implementation of its stated type. Reduction/sorting/O18 projections faithfully propagate whatever that under-specified hole returns.

3. **major — the origin “fixtures” still assume a prebuilt recursive origin plan in renamed form** (`research-tests/DGamma/R10OperationalOriginPlanFixturesPositive.idr:55–136,249–421`). `RawOperationalOriginPlan` has an explicit `prefixOccurrences` map index and constructor argument, contrary to the plan's “no occurrence map” statement. Each step also accepts exactly the two source-origin equations that `CrossingOriginPlanStep` needs. No `RawOriginStep` is ever constructed; its occurrences are declaration and pattern matching only. The 1×1, 2×1, and 2×2 exports take an already-built raw recursive plan plus safety/count premises and repackage it. Top-level identity and recursive composition indices prevent direct map laundering (Probe 46), so this is not itself a source-seal blocker, but it is not the claimed raw fixture calibration.

4. **major — the committed suite omits exact attacks that the plan says are retained** (`THM73-PLAN.md:160–161`; `research-tests/run-r10-suite.sh:62–82`). There is no generated-only retarget module and no tree-only capital clone module. Fresh temporary reconstructions reject at the correct coherence/schedule seals (Probes 48–49), so the interfaces pass those attacks today, but the release evidence claim is false. The dedicated R10 deletion-step and coherent-capital negatives are also only universal `Refl` equalities, not direct constructor/assembly clones; stronger temporary Probe 24 was needed for the deletion constructor.

5. **minor — negative diagnostics are only generically pattern-matched by the script** (`research-tests/run-r10-suite.sh:97–102`). The broad three-pattern check would accept some unintended dependent error. Independent per-module inspection in Probe 38 found all current errors substantive, so this is test-hardening rather than a present false pass.

## Positive results / non-findings

- CP3 is exactly immutable blob `2c697e532e83989de8591fa6a4378747c6a501c0`; all `src/` and `dgamma.ipkg` are byte-identical to baseline.
- `AdjacentSwapResult` has no map field. Its decomposition equalities are indexed by the exact original trace, prefix, local pair, moved pair, replayed suffix, and swapped trace. Equality-proof substitution cannot change its projected map (Probe 27).
- O9's erased equality is real: direct clone and arbitrary-`Refl` attacks fail. An imported named hole is opaque/fixed, not a client-instantiable metavariable.
- Reduction/core and sorting maps are definitional folds over explicit actual derivations; arbitrary map equality fails before accounting. O18's runtime schedule seal also rejects direct replacement.
- Generated/action coherence rejects generated-only retarget; public schedule, wrong birth/generation equation, wrong occurrence, wrong trace, shifted coordinate, duplicate, root, and zero-node attacks fail.
- Actor-block 1×1/2×1/2×2 range disjointness is proved internally from exact starts/counts, not accepted as a range-law premise.
- O16's old claim is honestly and completely withdrawn; only the abstract hard-premise assembler remains.
- All five spikes and all 43 tracked tests run serially. Fresh research/test TTC suite emits `R10_REPRODUCIBLE_SUITE=passed` with exact 5/24/19 counts.
- All 19 tracked negatives were rerun individually and fail at substantive intended dependent boundaries; no import/parser failure or commented/trivial positive was found.
- Research tests contain no holes/escapes; research has exactly the 32 named holes; production has none and cannot reach research through `dgamma.ipkg`.
- Exact seeded external build emits `207/207: Building DGamma.CP4ProgressProof`. Two unseeded exit-137 attempts are honestly disclosed and reproduced.
- Tracked worktree and index are clean; only pre-existing untracked `paper/` and this permitted report remain.

## Residual risks

- All 32 research proof bodies remain holes by design; none is a proof of Theorem 73.
- The source-fold contract defects mean later O16/O18/O20 authentication can be internally consistent with a wrong fixed origin family.
- No concrete O16 two-birth/one-withdrawal producer exists; all hard accounting laws remain assumed by the abstract assembler.
- No reachable repeated-Iter 2×2 local-diamond execution exists. The current origin materializer assumes the recursive raw plan and origin equations.
- Multiple valid deletion/sorting derivations may induce different maps; no path-independence theorem is stated. This may be acceptable if every derivation has a complete operational-origin certificate, but it must be revisited after Findings 1–2.
- O/A, O/O, accepted-correspondence scanning, and vestigial endpoint composition remain XL gates.
- Fresh all-source/package builds can be host-killed; seeded exact closure is reproducible, but a fully unseeded 207-module run was not completed in this review.

## Estimate assessment

- **Hole count/reconciliation:** PASS — exactly 32 and exact O1–O23 reverse map.
- **Arithmetic:** PASS — exact 129–226.
- **Mandatory gates:** PASS in prose, including reachable repeated-Iter and concrete O16.
- **Grade credibility/readiness:** FAIL. B's O6 contract and C/D's O9 contract require interface repair before their hole bodies can be meaningfully proved. F/G consume those maps and cannot be called source-authentic yet. The broad bands may absorb the work numerically, but the estimate must be reconsidered after the new certificate types and genuine calibration probes exist.

## Exact changes required for round 11

1. **Complete the O6 ordinal contract.** Add a prefix-origin law for every swapped-trace occurrence strictly before the adjacent pair, or preferably one exhaustive indexed `AdjacentSwapOrdinalRelation prefixCount targetOrdinal sourceOrdinal` covering prefix, moved-right, moved-left, and suffix. Prove the four regions exhaustive/disjoint. Retain generated/action coherence.
2. **Add O6 malicious-prefix probes.** Construct or parameterize repeated same-action/same-tag prefix occurrences and show a collapsed/permuted prefix origin cannot inhabit the operational fold certificate. Projection and direct map-clone negatives alone are insufficient.
3. **Replace O9's bare map result with an operational deletion certificate.** Its type must connect each surviving occurrence to the exact before/episode/after `GenerationActionSubsequence` embedding (or an executable deletion occurrence fold) and state source occurrence/ordinal equations plus generated coherence. `DeletionChainStep` should equality-seal its runtime map to that certificate's projection.
4. **Add O9 under-specification negatives.** A caller/filler-selected coherent survivor map with no retained-subsequence proof must fail. Keep direct step-clone, recursive reduction, sorting, and capital attacks.
5. **Make origin calibration honest.** Either (a) rename the current module/plan language to “generic raw-plan repackager,” explicitly disclose the prefix map and supplied origin equations, and stop calling 1×1/2×1/2×2 exports fixtures; or (b) actually construct `RawOriginStep` chains for those sizes from lower-level semantic inputs and prove the origin equations rather than accepting a prebuilt recursive raw plan. The reachable repeated-Iter gate may remain separate.
6. **Repair tracked suite coverage.** Commit generated-only retarget, tree-only capital clone, direct deletion-step constructor clone, a stronger coherent-both-halves producer/assembly attack, and a dedicated bridge wrong-generation test. Use per-module expected diagnostic substrings/locations rather than only three generic patterns.
7. **Reconcile/re-estimate after type changes.** Recount named holes, reverse-map the new O6/O9 certificate obligations, and explicitly charge any derivation-path coherence needed by O16/O20.
8. **Repeat release closure.** Serial suite, hole/escape/reachability scans, exact CP3/source diff, seeded 207/207, best-effort unseeded retry, and clean tracked/index checks.

## Final verdict

**REJECT.** Revision 10 successfully prevents caller-side map substitution through the adjacent/deletion/sorting/capital constructors, and its decomposition equality seals are genuine. It still is not ready for the proof grind: the fixed O6 and O9 hole signatures do not fully state the operational provenance they are supposed to certify, while origin-fixture and retained-suite claims remain overstated.

**Final verdict: REJECT**

### Probe 51 — final report integrity and acceptance-state check

**Command:** inspect the final 180 report lines; run `git status --short`, `git diff --cached --name-only`, `wc -l`, and SHA-256 of the report.

**Result:** Findings/change list/verdict are present and internally consistent. Before this log entry the report was 492 lines with SHA-256 `23e2455b...261d7`; index output was empty. Worktree status contained only pre-existing untracked `paper/` and this permitted report.

**Classification:** note — report artifact and no-staged-files acceptance evidence confirmed.

**Final verdict: REJECT**
