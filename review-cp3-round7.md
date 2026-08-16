# Checkpoint 3 adversarial review — round 7 (closing round)

**Target:** `6fbc0fd3b0b47902c154945cd6731e340c73fe35`
**Scope:** paper Section 4.4; generation-bijection Theorem-73 repair; requested regression, documentation, build, runtime, and escape-hatch audits
**Mode:** review only. No repository source, documentation, package, or tracked test is edited. Probe files remain outside `/Users/vyacheslavshebanov/Work/dgamma`. Because the runtime output path is authoritative, this report is written here rather than into the repository.

## Incremental audit log

### Baseline and mandatory prior-review read

- Confirmed exact requested HEAD `6fbc0fd3b0b47902c154945cd6731e340c73fe35`.
- No staged/tracked modification exists. Pre-existing untracked paths are `paper/` and `review-cp3-round5.md`; this review created neither.
- Read `review-cp3-round6.md` fully (169 lines), then `review-cp3-round5.md` fully (205 lines), in the required order. Round 6’s sole blocker is accurately understood: its global raw-name correspondence forced `renameForward 1 = 1` for a shared live root, thereby refusing a left historical generated child at raw 1 versus right child at raw 2.

Further results are appended immediately after each completed probe or audit item.

### Historical rounds 1–4 skim

- Skimmed all four earlier reports by their complete heading/finding/disposition structure. The lineage is consistent with round 6: round 1 exposed missing reachability/support and weak canonical packaging; round 2 added reachable support, identity-deletion, totality, and placement defects; round 3 added the disciplined cross-subtree rank cycle, selected-retirement deletion, and absent renaming/provenance; round 4 found globally vacuous child provenance plus occurrence-multiplicity and actor-block defects.
- I will not re-audit standing accepted CP1/CP2, Theorem-63 ordering, prior full-premise non-vacuity, historical countermodel rejections, generation-stamped self-canonicalization, or the MINOR-sound multi-license judgment except for the specifically requested spot checks.

### Paper Section 4.4 baseline

- Read Section 4.4 in full from `paper/cordis-paper.txt:1603-2385`, including Lemma 56 and the complete Theorem-73 statement/proof.
- Fidelity criterion for this round: paper Lemma 56 is a raw-state equivariance lemma, but Theorem 73(2) uses it specifically to match registration trees whose fresh names differ. Because Preservation explicitly permits O-Remove name reissue (`:1857-1858`), an implementation may introduce birth/generation identities to avoid one raw renaming having contradictory historical/current duties. The public same-orchestration relation must nevertheless (a) match each generated birth structurally and bijectively, (b) compare current endpoints under a coherent current-name renaming, and (c) not accept unrelated registration trees or mismatched external input histories.

### Immutable review workspace and repair-diff inspection

- Created an immutable `git archive 6fbc0fd` at `/tmp/dgamma-cp3-round7.nWRKxV`. All new Idris probes will be placed under this `/tmp` tree or another `/tmp` path, never in the repository.
- `git diff --check 7317ac8..6fbc0fd` passed. The repair diff is concentrated in `DGamma.CP3`, `DGamma.CP3StatementChecks`, `DGamma.CP3Support`, README/NOTES, plus the now-committed round-6 report. The final commit only removed a stale NOTES guard reference.
- Toolchain baseline: Idris 2 **0.8.0**.

### Probe 1 — independent reconstruction of the round-6 blocker pair and exact Theorem-73 chain

- Built `/tmp/dgamma-cp3-round7.nWRKxV/src/IndependentFreshChoiceProbe.idr` without importing `DGamma.CP3StatementChecks`. It independently reconstructs both checked nine-action traces from public LTS/CP3 primitives: left generated child raw 1 at ordinal 2, right generated child raw 2 at ordinal 2, both later inserting the same external live root raw 1 at ordinal 5.
- The reconstructed `RegistrationGenerationBijection` typechecks with explicit equations `(1,2) ↦ (2,2)` and `(1,5) ↦ (1,5)`. The complete `SameOrchestrationModuloGenerated` package—including exact external-root history, structural registration correspondence, identity current-name bijection, root fixing, and current-generation coupling—is constructed. Its executable construction prints `True`.
- The independent `freshChoiceTheorem73PremiseChain` takes the exact exported `confluenceTheorem Nat ...` alias, every public premise in its declared order, and this concrete same-input package, then returns the exact indexed `ConfluenceResult`. It does not rest on the committed `FreshChoiceCorrespondenceWitness` or a predecessor/raw-name correspondence.
- **Round-6 blocker core disposition: FIXED.** The formerly refused 1-vs-2 historical fresh-choice pair now crosses the exact public Theorem-73 boundary while the shared later live root remains raw-name identity.

### Probe 2 — BLOCKER: “structural” matching is globally chronological, not registration-tree structural

**Files:** `src/DGamma/CP3.idr:1807-1879,1887-1960`; paper `cordis-paper.txt:2338-2350`.

- Constructor audit confirms useful local force: a child action cannot be skipped; every left child birth consumes exactly one right child birth; the two actions carry the same component; and `generationForward` maps both the child birth and the parent generation live at that birth. Therefore unequal generated-birth counts, child↔root event matching, and arbitrary same-position component substitution are rejected.
- But `RegistrationTraceCorrespondence` has only one scanner position per trace. `SkipLeft/RightNonRegistration` cannot skip a child, so `MatchGeneratedRegistration` must pair the **globally first remaining child birth** on each side, then the globally second, and so on. It does not match children per parent/tree node.
- `/tmp/.../IndependentFreshChoiceProbe.idr` builds two checked 12-action executions with the same external root insertions 0 then 1, the same two parents and children, trivial effects, quiet/successful endpoints, and all four fibers supported. The only difference is legal scheduling of independent generated insertions:
  - left: child 2 of root 0, then child 3 of root 1;
  - right: child 3 of root 1, then child 2 of root 0.
  The combined executable check prints `True`.
- Any correspondence must pair those first births and hence demand `generationForward (0,0) = (1,1)` for their live parent generations. Both roots remain current. `CurrentEndpointRenaming.leftLiveRootFixed` fixes raw root 0, while `leftCurrentGenerationMapped` then requires that same `(0,0)` generation to map to the right current generation found at raw 0, namely `(0,0)`. The two demands are contradictory.
- This pair is exactly the lifecycle-schedule freedom Theorem 73 is meant to quotient: child registration order across distinct parent episodes is not an orchestration input, and paper’s proof matches the registration tree **below each A-fiber**, not one global child-event word (`paper/cordis-paper.txt:2342-2348`).
- **Severity: BLOCKER (over-strong/unfaithful premise).** The round-6 collision is fixed, but the replacement still refuses paper-legal same-orchestration executions whenever generated births of distinct live parents interleave in different orders. Matching must be keyed by mapped parent generation plus per-parent child/iterator position (or an unordered structural bijection with order local to each parent), not global child-birth order.

### Probe 3 — identity self-application of the nine-action trace

- Independently constructed `roleChangingIdentityGenerationTraceCorrespondence`, `RegistrationCorrespondenceByGeneration`, `CurrentEndpointRenaming`, and the complete `SameOrchestrationModuloGenerated` for the nine-action role-changing trace paired with itself under `identityRegistrationGenerationBijection` and `identityNameBijection`.
- The proof typechecks against HEAD. It removes the old child `(1,2)` from the live environment, records later root `(1,5)`, fixes both current roots, and maps every current generation identically.
- **PASS.** The new generation design is reflexive on the exact role-changing trace; the blocker in Probe 2 is cross-parent schedule permutation, not self-canonicalization or identity-bijection failure.

### Audit 4 — generation-bijection asymmetric/current-boundary attack matrix

- **Left has more generated births:** rejected structurally. Child O-Insert cannot use either skip constructor, `MatchGeneratedRegistration` consumes one event on both sides, and `RegistrationCorrespondenceEnd` requires both traces exhausted. The relation enforces equal child-birth cardinality.
- **Generated birth mapped to root (or vice versa):** rejected for births that occur in the traces. Every source child birth is explicitly equated to a target `OInsert ... (ChildOf ...)`, and bijectivity prevents a second root generation from sharing that target generation. Endpoint `SystemEquivalentByRenaming` also distinguishes `Root` from `ChildOf` via `ParentRelatedBy`.
- **Same-parent siblings with different components permuted:** rejected, because the global matching branch requires the exact same `component` at each paired position. This is appropriate *within one parent*: Definition-60 yield/continuation stability fixes that parent iterator’s registration order. Same-component sibling fresh names remain freely bijective.
- **Different parents / different orchestration positions:** not modeled correctly. For current parents it is over-strong as Probe 2 shows. For historical removed roots it can instead be too weak: only current live roots are coupled to raw identities, so a generation bijection may swap two removed external-root generations and thereby pair a child born under external root 0 with one born under external root 1, even though `SameExternalOrchestration` matched those root births by exact raw action. There is no field coupling *historical external root birth i* to the corresponding generation on the other trace.
- **A generation both current root and withdrawn historical child:** impossible in a full `CanonicalSchedule`. One generation is one O-Insert ordinal/role; `withdrawnRegistrationRemoved` requires an exact original child occurrence, whereas the current environment records the last unremoved birth. Standalone `CanonicalEndpointRelation` remains intentionally unchecked, but its API caveat now says so.
- **Current endpoint raw/gen disagreement:** rejected for all current births. `leftCurrentGenerationMapped` and `rightCurrentGenerationMapped` look up the generation at the raw name transported by `currentNameBijection`; live-root fixed-point fields force a shared current root’s raw identity, so its current generation must have the same image under both bijections. Different historical births of that raw name may intentionally differ.
- **Residual additional fidelity defect (MAJOR, subsumed by the blocker):** historical external root births need coupling to their exact matched external O-Insert occurrences. Otherwise the type admits a parent-tree isomorphism that renames externally fixed historical roots. This is the weak dual of the global-order over-strengthening.

### Audit 5 — advertised full-package statement checks

- `DGamma.CP3StatementChecks` independently typechecks in the immutable archive.
- `roleChangingFullCanonicalScheduleStatementCheck` (`src/DGamma/CP3StatementChecks.idr:910-956`) takes every field of the public `CanonicalSchedule` record specialized to the exact nine-action trace: canonical final/trace, exact external inputs, original and canonical registration disciplines, support order/linearization, one block per support member, block order, lifecycle coverage, full input placement, endpoint relation, and canonical registration tree. Its body calls `MkCanonicalSchedule` with every field, not a subset or projection. It also constrains raw withdrawals to `[]` and historical generations to `[(1,2)]`. **PASS.** It remains honestly an assembly/type check with field proofs as arguments, not a constructive schedule proof.
- `freshChoiceTheorem73PremiseChain` (`:853-901`) quantifies the literal exported `confluenceTheorem Nat ...` alias, supplies every argument in the alias’s exact order, uses `blockerPairSameInputs witness` for the repaired premise, and returns the exact generation/current-renaming-indexed `ConfluenceResult`. **PASS.** There is no shadow theorem or premise subset.

### Probe 6 — requested prior-witness/rejection spot checks

- `/tmp/.../PriorSpotProbe.idr` typechecks. It independently projects `sourceBelongsToProgram` from the exported concrete `positiveParentRegistrationYield` and applies `emptyParentCannotRegisterGuard` to that same nonempty witness, confirming the positive source is real and the empty-parent rejection is not premise-vacuous.
- The same probe replays one round-2 support attack generically: a yielded parent→child edge gives `parentRank < childRank`; a reverse child-provides/parent-depends edge gives `childRank < parentRank`; `succNotLTEpred` rejects their composite. This exercises the actual shared `yieldedRankIncreases` and `precedenceRankIncreases` fields.
- `/tmp/.../IdentityDeletionExpectedFailure.idr` attempts generic identity replay under deletability `action = action`. Idris rejects it exactly at `KeepAction`’s fifth argument: equality `?x = ?x` cannot unify with `Not (deletable ...)`, i.e. a function to `Void`. No preceding type mismatch masks the mandatory deletion barrier.
- **PASS:** all four requested historical spot checks retain their intended substance at `6fbc0fd`.

### Audit 7 — README/NOTES truthfulness

- Read `README.md` (123 lines) and `NOTES.md` (804 lines) fully.
- **README correspondence rows outside the new defect: PASS.** Proved/partial/stated labels remain accurate; Theorem 73 is still explicitly “under round-7 review”; Definition 47 and Lemma 68 clearly disclose the finite tagged/catalogued host and the one-live-head/many-child-name over-approximation; Lemma 72 remains unproved/review; constructive deletion/sorting/general endpoint assembly are not overclaimed.
- **New correspondence description: documentation consequence of BLOCKER.** README’s Theorem-73 row says child/live-parent births are “matched bijectively,” but omits that matching is one global chronological word and therefore refuses cross-parent schedule permutations. `NOTES.md:627-633,753-761` likewise describes a registration-tree correspondence without disclosing global order or the absence of historical external-root coupling. `NOTES.md:665-666` says generation-wise renaming is no longer proposition-shape debt; that is now false.
- **Debt/status/Next:** the eleven statement-only theorem declarations are listed accurately and missing constructive proofs remain pre-approved debt. But `NOTES.md:779-804` omits both new proposition-shape debts and says the next step after review is proof implementation. It must instead repair per-parent/tree matching and historical external-root coupling before constructive Confluence work.
- **Errata/deviation record: PASS apart from the new consequence.** Definition-32 negative recursion, Lemma-68/O-Insert provenance, Lemma-72 selected-retirement proof intent, and Lemma-56 raw-name/reuse ambiguity are all retained. The generated-monoid yielded-inverse cancellation repair and finite/exact/dictionary specializations also remain disclosed. The round-7 defect is an implementation/formalization bug, not a reason to retract those paper errata.
- **Endpoint-coupling API: PASS.** Both source comments and NOTES now state that trace-free `CanonicalEndpointRelation` historical entries are unchecked metadata and gain semantic force only through `CanonicalSchedule.canonicalRegistrationTree`; no standalone helper is presented as a full regression.
- **Severity: MAJOR documentation defect, consequent on Probe 2.** Under-review labels prevent an independent false “proved” claim, but the design/debt prose explicitly closes a proposition-shape issue that remains open.

### Audit 8 — genuinely clean archive build

- Created a second untouched `git archive 6fbc0fd` at `/tmp/dgamma-cp3-round7-clean.kfXsEI`.
- Ran `idris2 --clean dgamma.ipkg && idris2 --build dgamma.ipkg` under Idris 2 0.8.0.
- **PASS: all 12/12 package modules rebuilt successfully.** No probe source or prior TTC cache was present in this archive before the build.

### Audit 9 — runtime aggregates

- A review-only runner in the clean archive evaluated the eleven individual `DGamma.CalculusChecks` regressions, `allRuleChecks`, all four individual CP3 statement/runtime checks, and `allCP3StatementChecks`.
- Output: `[True, True, True, True, True, True, True, True, True, True, True, True, True, True, True, True, True]`.
- **PASS.** The new concrete fresh-choice package executes, and no existing runtime regression was disturbed.

### Audit 10 — totality, holes, escape hatches, and repository hygiene

- All **12/12** packaged `src/DGamma/*.idr` modules contain exactly one `%default total`.
- Anchored scans found zero `believe_me`, `assert_total`, postulate, `%unsafe`, `%foreign`, unsafe IO escape, `%default partial`, `%default covering`, partial/covering declaration, or named metavariable hole.
- Exactly **11** source `TODO(proof)` sites remain: three in `Unified`, three in `Metatheory`, and five in `CP3`. They annotate the same statement-only declarations catalogued in NOTES; no TODO is an accepted inhabitant.
- `git diff --check` passes. There is no staged file or tracked modification. Repository status remains the pre-existing untracked `paper/` and `review-cp3-round5.md`; every round-7 probe and this authoritative report are outside the repo.
- **PASS.** No hidden proof/totality debt was found.

### Probe 11 — typed expected failure for the cross-parent schedule blocker

- `/tmp/.../GlobalOrderExpectedFailure.idr` defines the *proper tree bijection* for Probe 2: roots `(0,0)` and `(1,1)` stay fixed; left child `(2,4)` maps to the same child’s right birth `(2,5)`; left `(3,5)` maps to right `(3,4)`.
- Attempting the unavoidable first `MatchGeneratedRegistration` is rejected exactly at its generation-map field: the globally first right child is `(3,4)`, but the proper tree map sends the globally first left child `(2,4)` to `(2,5)`. Idris reports the concrete mismatch `MkRegistrationGeneration 3 4` versus `MkRegistrationGeneration 2 5`.
- Because neither skip constructor accepts a generated action, no alternative constructor path can postpone either first child. This mechanically confirms the source audit: the relation rejects a genuine per-parent/tree bijection solely because two parents’ generated steps were scheduled in the opposite global order.

### Audit 12 — paper Lemma-56 / Theorem-73 faithfulness adjudication

- The **generation key itself is an honest and necessary internal device**. Paper Lemma 56’s raw state action cannot simultaneously rename an old child incarnation and fix a later external incarnation of the same raw name. `(raw,birth ordinal)` plus a separate current raw bijection faithfully resolves that ambiguity, as Probe 1 demonstrates.
- The **submitted structural relation is not yet an honest registration-tree quotient**:
  1. it is stronger than the paper by preserving one global generated-event order across distinct parents, excluding Probe 2’s legal lifecycle interleaving;
  2. it is weaker than its own exact-external-input premise for removed parents, because historical external root generations may be permuted independently of the exact root O-Insert matches.
- This is not merely constructive proof debt. `SameOrchestrationModuloGenerated` defines the public domain of `confluenceTheorem`; accepting/rejecting the wrong execution pairs is a proposition-shape/fidelity error even if `ConfluenceResult` is nontrivial on the remaining domain.
- Required design: anchor **every external root birth generation** to its exact `SameExternalOrchestration` match; then match generated children under the mapped parent generation, preserving only per-parent iterator order and recursively matching descendants. Cross-parent event order must be irrelevant. Current endpoint coupling can remain a separate projection of that structural correspondence.
- **Faithfulness verdict: FAIL / BLOCKER.** No additional false conclusion on an inhabited accepted premise was found, but the theorem’s public same-orchestration domain is both too narrow and, at historical roots, too permissive.

## Round-6 finding disposition

| Round-6 finding | Round-7 disposition |
|---|---|
| Global raw-name bijection refuses child-1/live-root-1 versus child-2/live-root-1 | **FIXED.** Independently reconstructed complete generation correspondence maps `(1,2)→(2,2)`, keeps `(1,5)`, constructs the full same-input package, and crosses the exact public theorem alias. |
| Full role-changing canonical regression was only weak/generic | **FIXED as a statement assembly regression.** The replacement supplies every `CanonicalSchedule` constructor field specialized to the nine-action trace and exact withdrawal equations, while honestly leaving proofs as arguments. |
| Standalone endpoint historical metadata needed API qualification | **FIXED.** Source/NOTES state that only `canonicalRegistrationTree` validates it. |
| README/NOTES omitted the raw collision | **FIXED for that collision.** The generation/current split and exact witness are documented. **Reopened for the new global-order/historical-root defects.** |

The exact round-6 blocker is closed. Round 7 finds a distinct structural-domain blocker introduced by the replacement: global child-event order is not registration-tree structure.

## Whole-project final debt summary

### Honest, previously declared/pre-approved proof or representation debt

- Definition 32 remains an explicit finite tower approximation; Lemma 38 is only the proved relational core. Lemma 35 and Theorems 40/42 are statement-only.
- Section 4 retains documented finite static continuations, tagged/catalogued explicit host registration (including one-head/many-name over-approximation), trace-anchored full-effect monoids, exact effect equality, and explicit dictionary alignment.
- Lemmas 54–57 have structural fragments but are not individually fully packaged.
- Theorem 61, Corollary 62, and the recovery branch of Theorem 64 need the actual-accumulator temporal induction.
- Progress/Theorem 66 needs unloading-chain no-deadlock and Equation-61 ranked counting.
- Lemma 71 lacks applicability/control frames.
- Lemma 72 lacks checked deletion induction. Theorem 73 lacks constructive deletion, canonical sorting, and general endpoint assembly.
- These are explicit statement/proof debts without postulates and are not grounds for rejection.

### New blocking statement/fidelity debt

1. Replace the global chronological generated-event scan with a parent-generation-indexed registration-tree correspondence. Preserve child order only within each mapped parent; allow independent parents’ child births to interleave differently.
2. Couple every historical external root generation—not only current roots—to the exact root birth matched by `SameExternalOrchestration`. This prevents generated subtrees from being reassigned between removed external roots.
3. Add the 12-step cross-parent order permutation as a full-package regression and update README/NOTES/Status/Next before proof implementation.

## Final findings

1. **BLOCKER — `src/DGamma/CP3.idr:1807-1879,1887-1960,2382-2407`:** `RegistrationTraceCorrespondence` pairs child births in one global chronological order. Two checked, quiet, successful traces with identical external roots and identical final registration trees but opposite child-birth order across distinct live parents cannot inhabit `SameOrchestrationModuloGenerated`. A typed expected-failure probe reaches the concrete `(3,4)` versus `(2,5)` generation mismatch. The public Theorem-73 domain therefore rejects a paper-legal lifecycle scheduling pair.
2. **MAJOR / weaker dual — `src/DGamma/CP3.idr:1818-1960`:** parent generations are related only through the unconstrained generation bijection; exact external root matches are coupled only if the roots remain current. Subtrees under removed external roots can be reassigned by permuting historical root generations, admitting a registration-tree correspondence inconsistent with exact external root identities.
3. **MAJOR documentation consequence — `README.md:123`; `NOTES.md:627-666,753-804`:** the rows accurately mark Theorem 73 under review and document the 1-vs-2 repair, but describe the scanner as a registration-tree bijection and declare proposition-shape debt closed without disclosing global ordering or historical-root uncoupling.
4. **VERIFIED FIX — round-6 blocker:** an independent public-API reconstruction maps historical child `(1,2)` to `(2,2)`, keeps live root `(1,5)`, builds full `SameOrchestrationModuloGenerated`, and applies the exact public `confluenceTheorem` chain.
5. **VERIFIED — full regressions:** `roleChangingFullCanonicalScheduleStatementCheck` instantiates every `CanonicalSchedule` constructor field; the theorem-premise guard uses the literal public alias; identity generation/current bijections self-correspond the nine-action trace.
6. **VERIFIED — requested historical spots:** positive yielded source and empty-parent rejection remain substantive; a round-2 parent/precedence cycle collapses by strict ranks; identity deletion fails exactly at `Not deletable`.
7. **VERIFIED — project quality:** immutable clean build 12/12; seventeen runtime aggregate values `True`; 12/12 modules total; no escape hatch, unsafe/partial declaration, named hole, staged file, or tracked review change; 11 explicit statement-only TODO sites.

# Final verdict: REJECT

The exact round-6 raw-name blocker is genuinely repaired, but acceptance cannot close: the new generation correspondence preserves global child-event order rather than registration-tree structure, excluding legal cross-parent schedule permutations. Declared missing proofs are not the reason for rejection.