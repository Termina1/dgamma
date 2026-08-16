# Checkpoint 3 adversarial review — round 4 (closing)

**Target:** `560572f1f9231cd49db7b3746b6cba03f62c1492` (`add CP3 yielded registration and renaming witnesses`)
**Scope:** paper Section 4.4; all round-3 findings; new tagged/ranked provenance and renaming machinery; positive non-vacuity; whole-project documentation/build audit
**Mode:** review only. No Idris source, package, README, NOTES, or tracked test is being edited. All probes are under `/tmp`; this report is the sole review artifact.

## Baseline

- Confirmed exact requested HEAD `560572f`.
- Pre-review tracked tree is clean; `paper/` is the only pre-existing untracked path.
- Read `review-cp3-round1.md`, `review-cp3-round2.md`, and `review-cp3-round3.md` in full first.
- Created a fresh `git archive` at `/tmp/dgamma-cp3-round4.3Vuxg2`; all inspections/probes use that immutable snapshot rather than the working tree.
- Paper Section 4.4 is being audited from `paper/cordis-paper.txt`, with special attention to Lemmas 56, 68, 70–72 and Theorem 73.

## Incremental review log

Validation and attack results will be appended below as they complete.

### Clean archive build

- `idris2 --version`: **Idris 2 0.8.0**.
- `idris2 --clean dgamma.ipkg && idris2 --build dgamma.ipkg` in the fresh archive: **passed, 12/12 modules**.

### Initial statement audit

- The round-3 O-Retire over-deletion is structurally repaired: `EpisodeDeletedActor` has a selected-owner constructor only for lifecycle actions, and `selectedRetireSurvivesGuard`/`selectedRemoveSurvivesGuard` eliminate deletion evidence at `R=[]`.
- The old empty-parent attack is structurally rejected: `ParentRegistrationYield.sourceBelongsToProgram` together with the exact nonempty `Reloading (sourceStep :: sourceContinuation)` state has the packaged eliminator `emptyParentCannotRegisterGuard`.
- `RegistrationProtocol` assigns strict natural-number ranks to both yielded-parent and precedence edges, so the old alternating four-edge mixed cycle would require a strict rank cycle. A typed probe will check this directly rather than relying on the comments.
- A new over-strengthening risk is visible in `CanonicalSchedule`: each supported open episode must be a contiguous `ActorLifecycleOnly` block, but every surviving child O-Insert must occur while its parent is already `Reloading` at the tagged head step. The parent must later consume that head to become Active, apparently forcing the child insertion *inside* the parent episode block where `ActorLifecycleOnly` rejects it. This is being tested as the required nested-registration positive case.

### Round-3 attacks and new registration-protocol attacks

A review-only `Round4MachineryProbe.idr` typechecks the following facts:

- `sameProtocolTagUnique`: inside one protocol, one tag cannot map to two different components because `registrationCatalog` is a function. Cross-protocol collisions are harmless to the submitted theorem because both traces are required to share one protocol.
- `internallyGeneratedCannotAliasFixed`: bijectivity prevents a distinct generated name from mapping to a fixed external name. Together with bidirectional external fixed points and matched root inputs, the external-name set does not leak.
- `noRankedFourCycle`: four strict rank inequalities of the old `A < C < B < D < A` attack imply `LT a a` and contradiction. The tagged/ranked discipline blocks the requested alternating cross-subtree attack rather than merely rejecting its phase.
- A concrete swap bijection maps `[External, LeftFresh, RightFresh]` to `[External, RightFresh, LeftFresh]`; runtime checks printed `[True, True, True]`. `FiberRelatedBy` constructors typecheck for the unchanged root and for children whose parent is the fixed external root. The round-3 child-1-versus-child-2 exact-domain refutation is therefore absorbed by the new relation shape.
- `selectedRootRetirementMustSurvive` proves more than the submitted negative guard: any exact `ActionSubsequence` of an episode headed by selected `O-Retire` at `R=[]` is necessarily headed by a surviving `O-Retire`. The `DeleteAction` case is eliminated by `selectedRetireSurvivesGuard`. Thus the round-3 root-retirement survivor retains the retirement write, as required.

**BLOCKER — `src/DGamma/CP3.idr:175-185`: `yieldedRankIncreases` omits the premise that its `step` belongs to `parent.componentProgram`, making every child registration impossible.**

The protocol law quantifies an arbitrary `StepEffect` having the alleged parent's dependency/provision type. It does not include `Elem step (componentProgram parent)`, although `ParentRegistrationYield` later does. The review probe first derived the same-spec contradiction `childRank < childRank`; the stronger attack is universal:

1. for any catalog entry `registrationCatalog protocol tag = Just child` and child rank, construct a perfectly witnessed no-op `StepEffect` of *the child's own* dependency/provision type with `registrationYieldTag = Just tag`;
2. instantiate `yieldedRankIncreases` with `parent = child`, that fabricated step, and the child rank on both sides;
3. obtain `LT childRank childRank`, contradicted by `succNotLTEpred`.

The total typed eliminators `rankedCatalogEntryImpossible` and `everyParentRegistrationYieldImpossible` compile. The latter proves that **every** `ParentRegistrationYield` is empty. Consequently any `RegistrationProvenance`/`RegistrationDiscipline` trace containing a child O-Insert is uninhabitable. `emptyParentCannotRegisterGuard` is true only because the model rejects much more than the empty-parent attack.

A checked finite runtime trace confirms this is not an operational impossibility. Two distinct components with the same empty dependency/provision specification perform

```text
O-Insert parent Root; L-Begin parent; O-Insert child (ChildOf parent);
L-Finish parent; L-Begin child; L-Finish child
```

and reach a well-formed, quiet, successful state where both parent and child are supported and Active. `NestedRuntimeProbe` printed seven `True` values for exactly those diagnostics. The paper permits this finite, nonrecursive case, but no submitted protocol can state it. The law must add actual source-program membership (or index the proof by `ParentRegistrationYield`'s source occurrence), matching the field already present there.

This is both a false non-vacuity claim and the task's explicit **MAJOR-or-worse** over-strengthening condition. Because nested registration is a central paper behavior and all such premises are empty, it is a checkpoint **BLOCKER**.

### Renaming machinery audit

**Pass, with two residual limitations.**

- `NameBijection` is a genuine bijection. Review-only `inverseBijection` and `composeBijection` constructors typecheck, so the renaming indices needed for symmetry and transitivity exist.
- `SystemEquivalentByRenaming` transports ambient state, all per-name/per-key effect-table lookups, domain presence, the exact component/program, parent, retirement bit, remaining iterator, accumulator, committed view, and outcome. Its orientation is compatible with inverse bijections and its fields compose under composed bijections. I found no relation-level countermodel.
- The project does **not** package reflexivity/symmetry/transitivity for `SystemEquivalentByRenaming` itself. This is a proof/API debt, not a false statement: paper Theorem 73 only needs the one final renamed comparison, and the field shapes are closed under the required inverse/composition operations.
- External fixed points do not alias a distinct generated name: the typed `internallyGeneratedCannotAliasFixed` proof uses the left inverse. Because `SameExternalOrchestration` matches root inputs and the correspondence fixes external names from both sides, the requested external-alias leak is blocked.

**MAJOR residual — `src/DGamma/CP3.idr:1611-1643`: occurrence-existence is not a bijection of registration occurrences/generations.** `RegistrationCorrespondenceByRenaming` quantifies `ActionOccurs`, so repeated legal remove/reissue occurrences of the same raw child name can all be witnessed by one occurrence on the other trace. It transports action values, names, parents, and components, but not occurrence identity or multiplicity. A global name bijection also cannot handle a raw name first used by a matched external root generation and later reissued internally with a different fresh-name choice: the earlier external occurrence fixes it forever. There is no unsound external alias, but the price is rejecting paper-legal role-changing reissue pairs and overstating “registration-tree bijection.” Generation-stamped occurrences or an occurrence-level bijection are still needed.

### Tag-gaming disposition

- **Same tag, different components in one protocol:** blocked by the functional catalog (`sameProtocolTagUnique`).
- **Same tag across different protocols:** possible but irrelevant to one Theorem-73 application, which requires one shared protocol for both traces.
- **Tag on a non-registration/arbitrary step:** catastrophically gameable in the protocol law. The arbitrary fabricated tagged identity step is precisely what proves every ranked catalog entry inconsistent.
- **Repeated use:** even after adding program membership to the rank law, `ParentRegistrationYield` has no consumption/one-use witness. Since O-Insert does not advance the parent head, the same live head/tag can license multiple fresh child insertions before one L-Advance. This is a further provenance/multiplicity debt.
- **Cyclic rank evidence:** impossible; the checked `noRankedFourCycle` proof composes the strict `Nat` inequalities to irreflexivity.

### Canonical nested-registration compatibility

The protocol inconsistency already makes every child-bearing `CanonicalSchedule` premise empty. There is a second, independent incompatibility that will surface once the rank law is repaired:

- every supported fiber receives one `LocatedOpenEpisodeBlock` whose body is contiguous and `ActorLifecycleOnly` (`CP3.idr:1732-1756`);
- a surviving child O-Insert must occur after its parent's L-Begin while the exact tagged head is `Reloading`, and before a parent L-Advance consumes that head;
- the parent must take that later lifecycle step to become Active at the quiet endpoint, while `noLaterLifecycle` forbids moving it after the block;
- therefore the child O-Insert lies inside the parent block, where `ActorLifecycleOnly` rejects its orchestration action.

In the paper the registration is part of the parent's iterator step, not a separate global step. The explicit-host specialization must either allow provenance-linked child orchestration inside the parent block or fold registration into L-Advance. `CanonicalRegistrationCorrespondence` alone does not resolve the contiguity contradiction.

### Positive-instance / over-strengthening check

- The submitted root-only reconciliation runtime still passes unchanged. The aggregate includes the exact `[provider, consumer] -> [provider] -> []` scenario and evaluates `reconciliationScenarioChecks = True`; the full twelve-value runner printed twelve `True` values.
- Root-only protocols are not inherently empty: review-only `RootProtocolPositive.idr` constructs a protocol, an admitted root component, and its rank witness; it typechecks and prints `True`. With no catalog entries, the child-yield law is vacuous. Thus the new machinery does not block reconciliation merely because it contains root O-Insert/O-Retire/O-Remove actions.
- The required nested-registration positive case fails decisively. The checked six-action trace above is operational, quiet, supported, and successful, but `everyParentRegistrationYieldImpossible` proves that no protocol can supply its first child premise. Consequently no positive nested instance of Lemma 68, Lemma 70, Lemma 72 with nonempty `R`, or Theorem 73 can be built at this HEAD.
- `CanonicalSchedule` has no nonempty packaged witness in the project; only conditional zero-withdrawal assembly helpers remain. Even after the protocol law is repaired, its actor-only block condition conflicts with surviving child insertion as described above.

### Remaining Lemma-72 shape issue

**MAJOR — `src/DGamma/CP3.idr:1468-1482`: `RegisteredNamesWithdrawn` still requires every `R` name to be present and vestigial in the original final state.** The paper permits a later original O-Remove, in which case the name is absent from both original and survivor endpoints. Legal post-remove reissue was restored globally, but this relation still has no absent/absent case. The current fatal protocol bug makes every nonempty-`R` theorem application vacuous and masks this older defect rather than repairing it.

### Erratum #3 / #4 audit

- Erratum #3's quotation is verbatim in substance: the paper says a subtree fiber is “registered by an activation of m or of one of m's descendants, hence at a step after the L-Begin of m.” It is also correct that the printed O-Insert rule does not enforce yielded-iterator provenance. Calling it “Table-1 O-Insert” is slightly imprecise because Table 1 summarizes writes rather than all rule premises, but the identified mismatch is real.
- Erratum #4 quotes both sides accurately: Lemma 72 literally says delete “steps that act on n,” while its proof says “the deleted steps of n write no field but theta_n.” Definition 53 makes O-Retire a step acting on n and Table 1 shows it writes tau_n. Lifecycle-only selected deletion is a justified proof-intent repair and the root-retirement probe confirms its implementation.
- The documentation after the quotations is not truthful at HEAD: `RegistrationProtocol` does not successfully tie any child insertion to a step, because every `ParentRegistrationYield` is empty; and “occurrence-level yield evidence handles each birth” overstates raw-name `ActionOccurs` in the presence of reissue.
- `CP3.idr:249-251` still describes L-Leave/L-Divert/L-Raise boundaries as transitions that “execute a parent's accumulator.” Table 1 executes the accumulator only at L-Unload. The type is an earlier recovery/exit boundary, as round 3 already found.

### Whole-project documentation truthfulness

The correspondence table has 70 substantive paper rows (71 Markdown table lines including the header). Previously accepted Section 3 and CP2/Ordering rows retain their proved/partial/stated distinctions; no regression was found there. The changed CP3 rows need these corrections:

1. **Def 47 (`README.md:101`)** says theorem traces tie child O-Insert/O-Retire to the exact iterator stage. This is false by vacuity: `everyParentRegistrationYieldImpossible` eliminates all such traces.
2. **Lemmas 68/70 (`README.md:118-120`)** are cautiously labeled under review, but their descriptions and `NOTES.md:101-119,601-606` present tagged/ranked provenance as a usable repair. It admits no child trace.
3. **Lemma 72 (`README.md:122`)** accurately records lifecycle-only selected deletion, but does not disclose that nonempty `R` is currently impossible or that original-absent `R` remains unrepresentable.
4. **Theorem 73 (`README.md:123`)** is honestly labeled under review, and the exact-domain conclusion was removed as claimed. However “registration-tree correspondence” is occurrence-existence rather than a generation/occurrence bijection, child schedules are vacuous, and external/internal role-changing reissue is excluded.
5. **`NOTES.md:607-614,662-666,668-695`** correctly distinguishes proved, partial, and merely stated declarations syntactically, but its concrete CP3 repair claims and `Next` plan omit the blocking protocol/type repair. `CP3StatementChecks.childRegistrationDisciplineGuard` and `emptyParentCannotRegisterGuard` project empty domains, so the claimed guard coverage does not establish non-vacuity.

### Clean build, runtime aggregates, scans, and hygiene

- Fresh archive clean build: **12/12 passed** under Idris 2 0.8.0.
- Submitted runtime aggregate: `[True, True, True, True, True, True, True, True, True, True, True, True]`.
- Nested runtime trace diagnostics: `[True, True, True, True, True, True, True]` for well-formed, quiet, no failures, parent/child support, and parent/child Active.
- All 12 packaged modules contain exactly one `%default total`.
- Anchored source scans found no `believe_me`, `assert_total`, postulate, `%unsafe`, unsafe FFI, `%default partial`, `%default covering`, partial/covering declaration, or named metavariable hole.
- There are 11 source `TODO(proof)` declaration sites and 15 source+README+NOTES textual hits. No TODO is accepted as an inhabitant.
- `git diff --check` and report trailing-whitespace scan pass. No staged files exist. The final repository changes remain only the requested untracked report alongside the pre-existing untracked `paper/` directory.

## Probe evidence summary

All probe sources and executables are outside the repository, in the fresh `/tmp` archive.

| Probe | Result | Evidence |
|---|---:|---|
| `Round4MachineryProbe` | passed | catalog functionality, fixed-point anti-aliasing, inverse/composed bijections, strict-rank cycle rejection, fresh-child swap, selected-retirement mandatory survival, and the universal `ParentRegistrationYield -> Void` eliminator all typecheck; runtime swap flags `[True,True,True]` |
| `NestedRuntimeProbe` | passed | checked finite child-registration run; final diagnostics `[True,True,True,True,True,True,True]` |
| `RootProtocolPositive` | passed | a root-admitting empty-catalog protocol and rank witness typecheck; prints `True` |
| CP3 aggregate runner | passed | eleven submitted individual checks plus `allRuleChecks` are all `True` |
| clean archive package build | passed | all 12 package modules rebuilt |
| source/docs scans | passed | no escape hatch, partial declaration, named hole, unsafe FFI, or module missing `%default total`; 11 explicit source TODO sites |

## Per-round-3-finding disposition

| Round-3 finding | Round-4 disposition |
|---|---|
| disciplined alternating cross-subtree cycle refuted Lemma 68 | **Attack blocked only vacuously / NOT ACCEPTED.** Strict ranks forbid the cycle, but the protocol law makes every child registration impossible, so it supplies no nontrivial repair. |
| selected O-Retire was deleted by Lemma 72 | **FIXED.** Selected deletion is lifecycle-only; a typed structural probe proves O-Retire must be replayed at `R=[]`. |
| fresh child names defeated exact-domain Confluence | **FIXED at endpoint-relation level.** `NameBijection` plus `SystemEquivalentByRenaming` absorb child-1/child-2 and transport full state. Occurrence/generation correspondence remains too weak/over-conservative under reissue. |
| empty parent could fabricate arbitrary child component | **Old attack blocked, repair vacuous.** `sourceBelongsToProgram` rejects `Reloading []`, but `everyParentRegistrationYieldImpossible` rejects every nonempty parent too. |
| original-already-absent R was unexpressible | **NOT FIXED.** `RegisteredNamesWithdrawn` still requires present/vestigial original and absent survivor. |
| `ParentRecoveryStep` was described as accumulator execution | **NOT FIXED.** The source comment still makes that claim although only L-Unload executes the accumulator. |
| CP3 documentation omissions/overclaims | **REOPENED.** Under-review labels remain cautious, but Def-47/protocol/tree non-vacuity claims are now concretely false. |
| CP3StatementChecks projections | **Fields projected, semantic guard failed.** The new projections compile, but the child-domain projections are vacuous and do not test protocol inhabitation. |
| clean build/runtime/scans | **PASS.** 12/12, twelve True, total/escape-hatch clean. |

## Whole-project final summary

The historical 70-row correspondence split from round 3 remains useful syntactically: Section 3.1 has 22 rows, Section 3.2 has 10, Section 3.3 has 11, and Section 4 has 27. Semantically at this HEAD:

- **Section 3.1 (effects):** all 22 declared definitions/results remain executable/proved as previously accepted.
- **Section 3.2 (coeffects):** all 10 rows remain executable/proved at their documented indexed-partial specializations.
- **Section 3.3 (unified):** six rows are complete, Lemma 38/Definition-32 transport is partial/deviating, and Lemma 35/Theorems 40/42 remain stated only. The finite negative-recursion approximation and partial-map deviations are truthful.
- **Section 4 calculus/metatheory:** raw Preservation (Theorem 59), global Ordering (Theorem 63), executable calculus/support machinery, and the already documented structural cores remain proved. Recovery Theorem 61/Corollary 62, recovery-combined Theorem 64, Progress induction, Lemma 71 applicability frames, and constructive deletion/canonicalization remain pre-approved proof debt.
- **New statement/design debt, not pre-approved proof debt:** the Def-47 finite registration protocol has no child inhabitant; Lemmas 68/70 and child-bearing Lemma 72/Confluence premises are therefore vacuous; canonical actor-only blocks are incompatible with surviving explicit registration; occurrence-level renaming/reissue and original-absent withdrawals remain unresolved.

The repository's syntactic `## Status` remains accurate about which names export proofs versus bare `Type`s. It is not semantically acceptable as a final project status until the protocol and dependent CP3 statement types are repaired.

## Final findings

1. **BLOCKER — `src/DGamma/CP3.idr:175-185,212-247`:** `yieldedRankIncreases` ranges over arbitrary same-typed steps without program membership. A fabricated tagged identity step gives `childRank < childRank` for every ranked catalog entry; total typed proof `everyParentRegistrationYieldImpossible` eliminates all child provenance.
2. **BLOCKER — `src/DGamma/CP3.idr:1732-1762,1983-2034`:** Theorem-73's child/canonical branch is vacuous under the protocol bug; after the obvious membership repair, a surviving child O-Insert is forced inside its parent's supposedly actor-lifecycle-only canonical block, so the current canonical type still cannot express the paper scenario.
3. **MAJOR — `src/DGamma/CP3.idr:1611-1683`:** generated-tree “correspondence” matches raw `ActionOccurs` existence, not occurrence/generation multiplicity; global external fixed points reject legal external-to-internal raw-name reissue pairs.
4. **MAJOR — `src/DGamma/CP3.idr:1468-1482`:** `RegisteredNamesWithdrawn` still cannot represent a registered name already O-Removed from the original endpoint.
5. **MAJOR — `README.md:101,118-123`; `NOTES.md:101-119,587-618,662-695`:** cautious review labels do not cure false concrete claims that tagged protocol traces tie child insertions to source stages and carry a real registration-tree bijection.
6. **MAJOR — `src/DGamma/CP3StatementChecks.idr:23-45`:** child/source regression guards project an empty premise type and therefore do not establish non-vacuity; the fatal protocol-law quantification is unguarded.
7. **MINOR — `src/DGamma/CP3.idr:249-251`:** recovery-boundary constructors are still mislabeled as accumulator-executing steps.
8. **VERIFIED FIX — `src/DGamma/CP3.idr:1153-1286,1843-1851`; `src/DGamma/CP3StatementChecks.idr:251-276`:** fresh-name endpoint renaming is structurally full, external aliasing is blocked, and selected root O-Retire/O-Remove are not deletable at empty R.
9. **VERIFIED — build/runtime/totality:** clean archive 12/12; all twelve submitted aggregates true; no escape hatch, partial module, unsafe FFI, or named hole.

# Final verdict: REJECT

The closing checkpoint cannot be accepted because the central new provenance premise is universally empty for child registration. The declared missing proofs are not the reason for rejection; false non-vacuity and proposition-shape defects are.

```acceptance-report
{
  "criteriaSatisfied": [
    {
      "id": "criterion-1",
      "status": "satisfied",
      "evidence": "Concrete BLOCKER/MAJOR findings cite DGamma.CP3, CP3StatementChecks, README, and NOTES; total typed eliminators prove every ParentRegistrationYield impossible, while runtime/renaming/retirement probes and clean build/scans provide counterevidence and verified fixes."
    }
  ],
  "changedFiles": [
    "review-cp3-round4.md"
  ],
  "testsAddedOrUpdated": [],
  "commandsRun": [
    {
      "command": "git archive 560572f | tar -x ... && idris2 --clean dgamma.ipkg && idris2 --build dgamma.ipkg",
      "result": "passed",
      "summary": "Fresh archive rebuilt all 12 package modules under Idris 2 0.8.0."
    },
    {
      "command": "idris2 --source-dir src -o round4-machinery src/Round4MachineryProbe.idr && ./build/exec/round4-machinery",
      "result": "passed",
      "summary": "Typed rank-cycle, catalog, alias, retirement-survival, bijection, and universal ParentRegistrationYield-impossibility probes; printed [True, True, True]."
    },
    {
      "command": "idris2 --source-dir src -o nested-runtime src/NestedRuntimeProbe.idr && ./build/exec/nested-runtime",
      "result": "passed",
      "summary": "Checked a real finite nested-registration trace; seven well-formed/quiet/support/Active diagnostics printed True."
    },
    {
      "command": "idris2 --source-dir src -o root-protocol-positive src/RootProtocolPositive.idr && ./build/exec/root-protocol-positive",
      "result": "passed",
      "summary": "Constructed a nonempty root-only protocol/rank witness and printed True."
    },
    {
      "command": "idris2 --source-dir src -o cp3-round4-eval src/CP3Round4EvalRunner.idr && ./build/exec/cp3-round4-eval",
      "result": "passed",
      "summary": "All eleven individual CalculusChecks flags plus allRuleChecks evaluated True."
    },
    {
      "command": "anchored escape-hatch, partiality, unsafe FFI, TODO, module-totality, diff, staged-file, and whitespace scans",
      "result": "passed",
      "summary": "No escape hatch/partial declaration/named hole; 11 source TODO sites; 12 total modules; no staged files."
    }
  ],
  "validationOutput": [
    "Clean archive build: 12/12 passed.",
    "Submitted runtime aggregate: [True, True, True, True, True, True, True, True, True, True, True, True].",
    "Nested registration runtime: [True, True, True, True, True, True, True].",
    "everyParentRegistrationYieldImpossible: total typed eliminator compiled.",
    "Fresh-name swap: [True, True, True]; selected O-Retire mandatory-survival proof compiled."
  ],
  "residualRisks": [
    "RegistrationProtocol makes every child ParentRegistrationYield impossible because yieldedRankIncreases lacks source-program membership.",
    "Canonical actor-only blocks cannot host surviving explicit child registration after the protocol law is repaired.",
    "Registration correspondence is raw-name occurrence existence, not a bijection of generations; legal role-changing reissue is over-restricted.",
    "RegisteredNamesWithdrawn still excludes original-absent names.",
    "Pre-approved temporal recovery, Progress induction, Lemma-71 frames, and constructive canonicalization remain open."
  ],
  "noStagedFiles": true,
  "diffSummary": "Review-only: added review-cp3-round4.md; no tracked project source, documentation, package, or test file edited and no commit.",
  "reviewFindings": [
    "blocker: src/DGamma/CP3.idr:175-185,212-247 - arbitrary-step rank law makes every ranked catalog entry and ParentRegistrationYield contradictory.",
    "blocker: src/DGamma/CP3.idr:1732-1762,1983-2034 - child-bearing canonical/confluence branch is vacuous and actor-only blocks conflict with surviving explicit registration.",
    "major: src/DGamma/CP3.idr:1611-1683 - generated correspondence does not match registration occurrences/generations and over-restricts legal name reissue.",
    "major: src/DGamma/CP3.idr:1468-1482 - original-already-absent registered names remain unrepresentable.",
    "major: README.md and NOTES.md - concrete tagged-provenance/tree claims are false despite cautious under-review labels.",
    "verified: lifecycle-only deletion preserves selected root retirement; NameBijection absorbs fresh child choices and blocks external alias leakage; build/runtime/scans pass."
  ],
  "manualNotes": "Final verdict: REJECT. The decisive failure is a total typed proof that all child registration provenance is impossible, not any declared proof debt."
}
```
