# Checkpoint 3 adversarial review — round 6 (closing round)

**Target:** `7317ac8d466bcd2efa7bed8d7f51ae14fcdfa151`
**Scope:** paper Section 4.4; generation-stamped Theorem-73 repairs; historical regression witnesses; documentation/build/escape-hatch audit
**Mode:** review only. No repository source, package, README, NOTES, or tracked test is edited. All probe files will remain outside `/Users/vyacheslavshebanov/Work/dgamma`.

## Incremental audit log

### Baseline and required prior-round read

- Confirmed exact requested HEAD `7317ac8d466bcd2efa7bed8d7f51ae14fcdfa151`.
- Repository has no tracked modification or staged file. Pre-existing untracked paths are `paper/` and `review-cp3-round5.md`; this review does not create the requested in-repository round-6 report because the authoritative runtime output path is this artifact.
- Read `review-cp3-round5.md` fully (205 lines). Its sole blocker is precisely the child-generation/raw-live-root collision described in the task: raw-name withdrawal cannot omit historical child generation 1 while endpoint raw name 1 is a live root, while retaining that child occurrence conflicts with roots-before-lifecycle placement.

Further results are appended immediately after each completed probe or audit item.

### Historical CP3 rounds 1–4 skim

- Skimmed all four prior reports in full enough to reconstruct the repair lineage. Round 1 found missing reached-state/support structure and an under-specified canonical package; round 2 found reachable explicit-child/name-reuse attacks plus identity deletion; round 3 found the disciplined cross-subtree rank cycle, selected-root-retirement over-deletion, and missing Lemma-56 renaming/provenance; round 4 found the arbitrary-step rank-law vacuity and actor-only block incompatibility. Round 5 then verified those repairs and narrowed rejection to role-changing raw-name reissue.
- Standing accepted results will not be redundantly re-audited beyond the requested spot checks: CP1/CP2, Theorem 63 ordering, full-premise non-vacuity for Lemmas 70/72/73, historical attack rejection mechanisms, and the MINOR-sound multi-license judgment.

### Paper Section 4.4 audit baseline

- Read Section 4.4 through Theorem 73 and its proof from `paper/cordis-paper.txt:1603-2364` (including Equation 53, Lemma 56, Definition 67/Equation 62, Lemmas 68–72, and Theorem 73).
- The paper explicitly permits freed raw names to be reissued (`paper/cordis-paper.txt:1857-1858`) and compares complete traces only after a single raw-name bijection as in Lemma 56 (`:1762-1780`, `:2338-2350`). Theorem 73's proof speaks informally of matching fresh registration trees; it does not introduce persistent generation identities. Generation stamps can therefore be an internal proof device, but a faithful public premise/result must not reject trace pairs that are related by one paper-level raw-name renaming solely because their birth ordinals differ.

### Immutable review workspace and repair-diff inspection

- Created a clean immutable `git archive 7317ac8` at `/tmp/dgamma-cp3-round6.7q6kUH`; every review probe will be written there or elsewhere under `/tmp`, never in the repository.
- Inspected commits `185e319`, `1d68772`, and `7317ac8`. The code change is concentrated in `DGamma.CP3`, `DGamma.CP3StatementChecks`, and `DGamma.CP3Support`; documentation changes are confined to README/NOTES. `git diff --check 2798ee5..7317ac8` passed.
- Source inspection confirms that the two advertised witnesses alone are not a full repair proof: `roleChangingGenerationAccountingGuard` merely pairs an arbitrary occurrence with singleton-generation membership and raw-empty nonmembership, while `canonicalEndpointHistoricalOnly` is reflexive on any state and accepts an arbitrary historical list. The decisive question is whether these pieces compose with exact occurrence removal, root placement, block order, discipline, and endpoint fields in one `CanonicalSchedule`; the next probe constructs that package directly.

### Probe 1 — executable canonical replay of the role-changing trace

- `CanonicalRuntimeProbe.idr` under `/tmp/dgamma-cp3-round6.7q6kUH/src` executed both the original nine-action trace and the candidate canonical six-action replay:

  `O-Insert 0 Root; O-Insert 1 Root; L-Begin 0; L-Advance 0; L-Begin 1; L-Advance 1`.

- Both runs printed `[True, True, True, True, True, True, True]` for well-formedness, quiet, no failures, support of 0/1, Active status of 0, and Active/Root status of 1. Thus exact deletion of the historical child birth plus moving the later external root birth before lifecycle is operationally applicable and reaches the intended endpoint shape. This removes the round-5 freshness/order contradiction at the evaluator level; dependent canonical fields remain to be assembled.

### Probe 2 — BLOCKER: cross-trace role-changing fresh choices are still refused

**Files:** `src/DGamma/CP3.idr:1728-1793,2173-2222`; paper Lemma 56 / Theorem 73.

- `CrossTraceRoleRenameProbe.idr` typechecks a total eliminator `roleChangingFreshChoiceRefused`. From `RegistrationCorrespondenceByRenaming`, a historical left generated child at raw name 1, and a final live left root at raw name 1, `leftLiveRootFixed` forces `renameForward 1 = 1`. `forwardRegistration` then forces the right trace to contain a generated child at raw name 1. Hence correspondence is impossible when the right execution made the equivalent fresh choice 2 instead.
- The executable pair uses identical external root inputs and differs only in that fresh internal choice:
  - left: child 1 is inserted/retired/removed, then external root 1 is inserted;
  - right: child 2 is inserted/retired/removed, then the same external root 1 is inserted.
  Both nine-action executions printed `[True, True, True, True, True]` for quiet, successful, support of final roots 0/1, and final name 1 being a root.
- This is precisely a paper-legal pair of checked executions with the same orchestration inputs and only different names drawn by registration. The generation-stamped *canonical* accounting repairs self-canonicalization of the left trace, but cross-trace `SameOrchestrationModuloGenerated` still demands one global raw-name bijection and therefore rejects the pair. Theorem 73 assumes this correspondence instead of deriving a generation-wise Lemma-56 matching.
- **Severity: BLOCKER (faithfulness).** The proposition is not false on its stronger premise, but it is not the paper Theorem-73 domain: legal registration choices are excluded solely by a historical-generation/live-root raw collision. The needed repair is a bijection of registration generations (with current live roots compared separately), not one global raw-name function over all historical occurrences.

### Probe 3 — generation accounting composes, but the submitted named guards are weak

- `GenerationPackageProbe.idr` compiled `oneChildWithdrawalPackage`, which constructs the **entire** `CanonicalRegistrationCorrespondence` for a trace with one exact original child generation and no canonical child occurrences. It discharges `canonicalToOriginal`, every-original accounting, injectivity, and `withdrawnRegistrationRemoved` together. It also compiled `historicalLiveEndpointPackage`, pairing that historical withdrawal shape with an unchanged raw endpoint.
- Therefore the generation/raw-endpoint separation itself is coherent and is sufficient for the round-5 trace's one historical child when the finite occurrence-inversion facts are supplied. The candidate six-action replay from Probe 1 gives exactly the required no-canonical-child shape.
- However, the repository's two advertised witnesses are not substantive regressions by themselves:
  - `roleChangingGenerationAccountingGuard` (`DGamma.CP3StatementChecks:268-273`) is singleton membership plus `Elem child [] -> Void` for an arbitrary assumed occurrence; it neither constructs the role-changing occurrence nor any correspondence.
  - `canonicalEndpointHistoricalOnly` (`DGamma.CP3Support:193-205`) is reflexive for any state and accepts any arbitrary generation list, including generations not born in a trace. Only `CanonicalSchedule.canonicalRegistrationTree` prevents that abuse.
- **Finding: MINOR test-strength defect, not a false package.** The full record coupling is substantive, but these named witnesses should not be cited as evidence that the concrete nine-step trace itself has a complete schedule.

### Probe 4 — multi-generation runtime attacks

- `MultiGenerationRuntimeProbe.idr` executed two longer legal checked traces:
  1. raw name 1 follows `child-of-0 -> external root -> child-of-2`, ending as the live Active child of 2;
  2. raw name 1 has two distinct withdrawn child births and is then reissued as a live Active root.
- Both printed seven `True` values for well-formedness, quiet/success, support of names 0/1/2, and the expected final role of name 1.
- Field audit of the stamped package finds no self-canonical contradiction for these shapes. Absolute transition ordinals distinguish every birth; `originalRegistrationAccounted` may withdraw the historical generations and retain the exact final child generation; `withdrawnRegistrationRemoved` forbids a withdrawn stamp from also being a retained mapped occurrence; and current raw omission stays empty when the final incarnation is live. For the child-root-child case, moving the root birth/retire/remove prefix before lifecycle frees raw name 1 before either retained child birth, so birth-state freshness remains satisfiable.
- No ordinal-collision attack was found: a generation ordinal is `transitionCount beforeRegistration`; two distinct positions in one inductive trace cannot share that count, and the ordinal-inverse laws prevent multiple left occurrences from collapsing to one right occurrence.

### Audit 5 — placement and endpoint-accounting attacks

- **Root birth after unrelated lifecycle:** Probe 1 already exercises the decisive case: external root 1 is born only after parent 0's L-Begin in the original, but its canonical located birth is moved before every lifecycle occurrence. The new placement laws quantify located births and compare ordinals, rather than requiring the original birth order, so the field remains satisfiable. Static provision disjointness and inactive-root insertion mean this move does not invent a target provider.
- **Reissue inside a retained canonical block:** Probe 4 covers repeated raw-name use around two parent episodes. Historical child occurrences can be withdrawn; a retained child occurrence is linked to its exact birth and remains before its own lifecycle. Root generations are independently fresh at their birth states. No raw-global freshness field remains.
- **Wrong/nonexistent withdrawn generation:** `CanonicalEndpointRelation` alone is deliberately permissive—`canonicalEndpointHistoricalOnly` can attach arbitrary historical stamps to an unchanged state. In a `CanonicalSchedule`, however, every element of that same list is consumed by `CanonicalRegistrationCorrespondence.withdrawnRegistrationRemoved`, which returns an exact original `LocatedGeneratedRegistration` and proves no canonical occurrence maps to it. Thus a generation for a name that never had such a child birth cannot inhabit the **full package**.
- **Raw omission mapped to a wrong generation:** each raw omission must select a stamp of the same raw name, and schedule coupling proves that stamp is an actual removed child occurrence. The endpoint conclusion still separately requires `RegisteredNamesWithdrawn` for the current raw endpoint; choosing an older valid stamp cannot erase a live current endpoint. The metadata does not state a unique causal generation, but this permissiveness does not weaken effects or outside-name controls and did not yield a false endpoint conclusion.
- **Residual API/test risk (MINOR):** the standalone endpoint relation's prose sounds stronger than its trace-free type. Its historical list becomes meaningful only under `CanonicalSchedule`; standalone uses should be documented as unchecked metadata.

### Audit 6 — complete role-changing self-canonical package / round-5 blocker disposition

The round-5 trace's Theorem-73 **premises are unchanged** by `2798ee5..7317ac8`; only the `CanonicalSchedule` result wiring changed from raw withdrawn names to withdrawn generations. Round 5's compiled self-pair supplied aligned checked trace, complete `RegistrationDiscipline`, quiet/success, all-trace totality, independence, same external orchestration, and identity occurrence correspondence. Reapplying the exact current `confluenceTheorem` alias to that chain therefore reaches the current `ConfluenceResult`, whose left/right schedules now use the generation-stamped package.

I audited the concrete schedule needed to ensure that result is not internally contradictory:

1. canonical checked trace: the six-action replay from Probe 1;
2. external inputs: root inserts 0 and 1 match in order; the old child insert/retire/remove are internal;
3. discipline: both canonical root components have the protocol ranks already used in the original trace; no canonical child premise is required;
4. support/order: `[0,1]`, unique and complete, with no parent or precedence edge at the final all-root/empty-key state;
5. blocks: `L-Begin 0; L-Advance 0` then `L-Begin 1; L-Advance 1`, contiguous, installed, Active at the final state, and covering all lifecycle actions;
6. placement: root births have ordinals 0 and 1 and every lifecycle occurrence has ordinal 2–5; both roots are fresh at their respective birth states; the child placement clause is impossible because each supported endpoint fiber is Root;
7. endpoint: no current raw omission, exact effects and full controls; historical list is the original child stamp `(1,2)`;
8. registration tree: the original has exactly the child occurrence at ordinal 2, the canonical trace has none, and Probe 3 constructs every field of the resulting exact one-child withdrawal correspondence.

**Disposition of the round-5 self-canonical blocker: FIXED.** No `CanonicalSchedule` field still fails for that nine-action trace. The repair is not established by the two small submitted witnesses alone, but the full field package is coherent and the executable canonical replay exists.

This does **not** cure the distinct cross-trace faithfulness blocker in Probe 2: replacing the left historical fresh choice 1 by right choice 2 is still rejected before `ConfluenceResult` by the raw `NameBijection` premise.

### Probe 6 — prior positive/source/rank witnesses still hold

- `PriorWitnessSpotProbe.idr` compiled at HEAD. It projects `sourceBelongsToProgram` from the concrete exported `positiveParentRegistrationYield`, reuses `emptyParentCannotRegisterGuard`, and proves the round-2 support-cycle shape impossible: a yielded parent-to-child rank edge plus a reverse provision/dependency edge composes to `LT r r` and is eliminated by `succNotLTEpred`.
- This confirms the positive child-yield is still nonempty, the empty-parent guard still targets the actual source-membership field, and one representative round-2 support attack is still rejected at the strict-rank protocol rather than at name reuse.

### Probe 7 — identity deletion remains structurally rejected

- Replayed generic unchanged-trace deletion in `/tmp/.../IdentityDeletionExpectedFailure.idr`. Idris rejected `KeepAction ... Refl ...` exactly because equality `?x = ?x` cannot inhabit `Not (deletable (transitionAction transition))`. This is the intended mandatory-filter barrier; no earlier type mismatch masked it.

### Audit 8 — README/NOTES truthfulness

- **Definition 47 row: PASS.** `README.md:101` and `NOTES.md:114-126` now explicitly disclose the finite tagged/catalogued host representation and the one-live-head/many-child-name over-approximation. They accurately state why strict ranks and per-child retirement keep the support argument sound.
- **Lemma 68 row: PASS.** `README.md:118` labels the statement under review, names actual source membership and both rank laws, allows post-remove reissue, and does not claim the theorem proved.
- **Theorem 73 row: PARTIAL / documentation blocker consequence.** The row accurately describes per-birth canonical deletion and the checked self role-change regression, but omits that cross-trace correspondence is still global-raw and refuses Probe 2. `NOTES.md:738-747` explicitly claims “No restriction on paper-legal raw-name role changes was added” and that there is “not another known proposition-shape defect”; those sentences are false. `NOTES.md:775-777` lists only constructive implementation debt and likewise omits generation-wise cross-trace renaming.
- **Named-witness overclaim:** `NOTES.md:625-635,738-746` presents `canonicalEndpointHistoricalOnly` and `roleChangingGenerationAccountingGuard` as constructive evidence for the regression, although Audit/Probe 3 shows both are generic reflexive/membership shapes and no concrete full `CanonicalSchedule` is packaged in the repository. The underlying self-package is coherent, but the stated regression strength is overstated.
- **Three critical historical errata/deviation records remain intact:** the non-strictly-positive Definition 32 issue (`NOTES.md:45-54`), the per-yield generated-monoid/cancellation repair (`:450-486`), and Lemma-68 yielded-registration mismatch plus tagged/ranked host repair (`:93-126`). Erratum #4's lifecycle-only deletion ambiguity is also preserved.
- Proof-debt statuses are otherwise truthful: Theorems 61/62/64 recovery, Progress, Lemma 71 frames, Lemma 72 replay, and constructive Theorem-73 sorting are not called proved.

### Audit 9 — genuinely clean archive build

- `idris2 --version`: **Idris 2 0.8.0**.
- Created a second untouched archive at `/tmp/dgamma-cp3-round6-clean.*` (no probe TTC cache), ran `idris2 --clean dgamma.ipkg && idris2 --build dgamma.ipkg`, and rebuilt **all 12/12 package modules successfully**.

### Audit 10 — runtime aggregates

- A review-only runner in the clean archive evaluated the eleven individual `DGamma.CalculusChecks` regressions, `allRuleChecks`, and both new role-changing checks.
- Output: `[True, True, True, True, True, True, True, True, True, True, True, True, True, True]`.

### Audit 11 — totality, holes, escape hatches, and repository hygiene

- All 12 packaged `src/DGamma/*.idr` modules contain exactly one `%default total`.
- Anchored source scans found zero `believe_me`, `assert_total`, postulate, `%unsafe`, `%default partial`, `%default covering`, partial/covering declaration, or named metavariable hole.
- There are exactly **11** explicit source `TODO(proof)` declaration sites, matching the documented statement-only debt; no TODO inhabits a theorem.
- `git diff --check` passed; no staged file exists. Repository status remains exactly the pre-existing untracked `paper/` and `review-cp3-round5.md`. No round-6 report or probe was written into the repository.

## Round-5 blocker disposition

**FIXED for the exact nine-action self-canonical trace.** Generation-stamped withdrawal, per-birth placement, and raw endpoint separation admit the six-action canonical replay and no full `CanonicalSchedule` field is contradictory.

**Not a complete Theorem-73 repair.** A distinct same-input pair that chooses different fresh child names around the same later live root remains excluded by the global raw-name `RegistrationCorrespondenceByRenaming` premise. This is the closing-round blocker.

## Whole-project final debt summary

### Honest, previously declared/pre-approved proof or representation debt

- Definition 32 remains an explicit finite tower approximation; Lemma 38 is only the proved relational core. Lemma 35 and Theorems 40/42 remain statement-only.
- Section 4 uses finite static continuations, explicit tagged/catalogued host registration (including the documented one-head/many-name over-approximation), trace-anchored full-effect monoids, exact effect equality, and explicit dictionary alignment.
- Lemmas 54–57 are represented by structural fragments but are not each packaged completely.
- Theorem 61, Corollary 62, and the recovery branch of Theorem 64 still need the actual-accumulator temporal induction.
- Progress/Theorem 66 still needs unloading-chain no-deadlock and ranked Equation-61 counting.
- Lemma 71 still lacks applicability/control frames.
- Lemma 72 still lacks the checked deletion induction; Theorem 73 still lacks constructive deletion, canonical sorting, and general endpoint assembly.

### New blocking statement/fidelity debt

1. Replace the historical generated-name side of `RegistrationCorrespondenceByRenaming` with a correspondence/bijection of **registration generations**. Keep a separate raw-name bijection (or exact comparison) for live endpoint names and root inputs. This must admit the child-1/live-root-1 versus child-2/live-root-1 pair.
2. State the paper ambiguity as an erratum: global raw Lemma-56 renaming and legal post-remove name reuse do not compose when one raw name changes role across generations.
3. Correct README/NOTES claims that no paper-legal role change is restricted and add this proposition-shape debt to Status/Next.
4. Strengthen the concrete role-changing regression to package an actual `CanonicalSchedule`/`ConfluenceResult` premise application; the current two named witnesses are generic shapes only.

## Final findings

1. **BLOCKER — `src/DGamma/CP3.idr:1728-1793,2173-2222`:** cross-trace registration correspondence remains a global raw-name bijection. A historical generated child at raw 1 plus a final live root 1 forces `renameForward 1 = 1`, so it cannot correspond to an otherwise equivalent trace whose child fresh choice is 2. Both checked traces are quiet, successful, and have the same final supported roots. This refuses a paper-legal same-orchestration pair and makes the Theorem-73 statement unfaithful.
2. **MAJOR documentation consequence — `README.md:123`; `NOTES.md:615-640,714-747,751-777`:** generation-stamped self-canonicalization is accurately described, but “No restriction on paper-legal raw-name role changes was added” and “not another known proposition-shape defect” are false; the debt/Next lists omit generation-wise cross-trace renaming.
3. **MINOR — `src/DGamma/CP3StatementChecks.idr:263-276`; `src/DGamma/CP3Support.idr:188-205`:** `roleChangingGenerationAccountingGuard` is singleton/empty-list bookkeeping and `canonicalEndpointHistoricalOnly` is arbitrary-list reflexivity. They are not concrete full-package regressions, although schedule coupling makes the underlying record design substantive.
4. **MINOR — `src/DGamma/CP3.idr:1890-1914`:** standalone `CanonicalEndpointRelation` accepts unchecked historical metadata; only the enclosing `CanonicalSchedule` proves that each stamp is an actual removed child birth. The API prose should make that dependency explicit.
5. **VERIFIED FIX — `src/DGamma/CP3.idr:1698-1950`:** the exact round-5 child-generation-to-live-root self trace is canonically coherent. The checked six-action replay succeeds; historical `(1,2)` withdrawal coexists with a live raw root 1; no canonical order/block/placement/endpoint/occurrence field fails.
6. **VERIFIED — historical regressions:** the positive parent yield and empty-parent guard still project actual source membership; the representative round-2 support cycle collapses to strict-rank irreflexivity; generic identity deletion is still rejected exactly at `Not deletable`.
7. **VERIFIED — project quality:** clean immutable archive build 12/12; fourteen runtime aggregate values `True`; all 12 modules total; zero escape hatch, unsafe/partial declaration, named hole, or staged file; 11 explicit statement-only TODO sites.

# Final verdict: REJECT

The round-5 self-canonical blocker is repaired, but project acceptance still fails on one statement-fidelity blocker: Theorem 73 refuses legal cross-trace fresh-name choices when a historical generated raw name is later a shared live root. Declared missing proofs are not the reason for rejection.