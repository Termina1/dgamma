# CP3 Round 10 Closing Adversarial Review

**Target:** `/Users/vyacheslavshebanov/Work/dgamma` at HEAD `b7f12c9b58471b1bb1423efedb2cede167183ea2`  
**Scope:** paper Section 4.4, round-9 vestigial-endpoint repairs, closing audits  
**Mode:** review only. Repository sources are untouched; compilable probes are kept outside the repository. This file is the explicitly authorized reviewer report.

## Incremental audit log

### 0. Baseline identity and cleanliness

- `git rev-parse HEAD` is exactly `b7f12c9b58471b1bb1423efedb2cede167183ea2`.
- Initial `git status --short` contains only the pre-existing untracked `paper/`; no tracked or staged changes exist.
- The package currently contains 13 Idris modules, including the new `DGamma.CP3VestigialChecks` module.

### 1. Mandatory prior-review reading

- Read `review-cp3-round9.md` (205 lines) fully first, then `review-cp3-round8.md` (164 lines) fully, as required.
- Round 9's rejection is understood precisely: deleted closing-episode births were correctly excluded from registration-tree matching but remained mandatory in `CurrentEndpointRenaming`, and exact-domain `SystemEquivalentByRenaming` could not express an unmatched vestigial registration at the final endpoint.
- Round 8's repaired activation-local positions and surviving-only registration matching, plus its earlier standing results, will not be re-audited except for the requested spot checks.

### 2. Earlier-round skim and standing-result boundary

- Skimmed CP3 rounds 1–7 by headings, disposition tables, final findings, and verdicts. The repair lineage is consistent: support/reachability and selected-retirement defects; registration provenance vacuity; raw-name/generation reuse; global child chronology; historical external-root coupling; activation-local positions; surviving-only matching; then round 9's vestigial endpoint boundary.
- I treat CP1/CP2, Theorem 63, prior non-vacuity chains, rejected historical countermodels, generation stamping, 1-vs-2 choice, parent-local/cross-parent matching, external-root coupling, per-activation position reset, surviving-only matching, and the complete removed-root guard as standing. Only the task's requested regression spot checks are repeated.

### 3. Paper Section 4.4 fidelity baseline

- Read Section 4.4 in full (`paper/cordis-paper.txt:1603-2385`), with special attention to Lemmas 56, 57, 72 and Theorem 73.
- Paper Lemma 57's literal vestigial conditions are exactly: retired (`τₙ = ⊤`), clean inactive (`θₙ = Inactive(⊥)`), empty table (`σₙ = ∅`), and no child points to `n`. It then permits removing that entry for rule observations away from `n`.
- Lemma 72's outside-`R` conclusion is stronger and provenance-specific: `R` is precisely the set of names registered in the selected closing episode; at the original endpoint each is vestigial, while the replay endpoint omits it, and the endpoints agree on every field outside `R` (with effect/control observation qualifications).
- Theorem 73 recursively deletes all closing episodes and then compares canonical surviving activation trees up to fresh-name renaming. Thus an endpoint quotient used specifically by Theorem 73 may legitimately require both scanner-derived “birth lies in a closing episode” evidence and Lemma-57 inertness; it must not allow arbitrary live/supported structure to be erased.

### 4. Immutable workspace and repair-diff inspection

- Created immutable `git archive b7f12c9` workspace at `/tmp/dgamma-cp3-round10.B88GBM`; all generated source probes and runners will remain under `/tmp`.
- Idris toolchain is Idris 2 0.8.0.
- Inspected the five submitted commits: `ad67569` archives round 9, `64803b3` changes endpoint coupling/result shape, `17b171e` makes inertness checks constructive, `340adef` adds the 2,082-line vestigial check module and package entry, and `b7f12c9` updates docs.
- The substantive diff from round 9 is confined to `CP3.idr`, `CP3StatementChecks.idr`, new `CP3VestigialChecks.idr`, package metadata, and docs. `git diff --check` on the repair commits reports no new whitespace issue (the only full-range diagnostics are archived round-9 report trailing spaces).

### 5. Probe A — independent executable reconstruction of 23/18 and 27/18

**Probe:** `/tmp/dgamma-cp3-round10.B88GBM/src/IndependentVestigialRuntime.idr`; imports core/runtime modules but neither committed CP3 check module. Executable output: `(True, True)`.

- Independently defined the registration-producing parent and empty child components, then replayed each literal action list through `checkedApplyAction` from `initialSystem`.
- The 23-action left schedule registers child 2, retires it, never O-Removes it, closes/reopens parent 1 around provider replacement, and retains child 4. The 27-action left schedule additionally begins/finishes child 2, retires it while Active, closes parent 1 first, then leaves/unloads child 2; it likewise never O-Removes child 2. The independently rebuilt right schedule has exactly 18 actions and never creates child 2.
- Both pairs execute completely. Every endpoint is quiet and failure-free; names 1, 3, 4 are supported; provider 3 provides `ServiceA`; left child 2 is present, retired, `Inactive Nothing`, empty-table, childless, and unsupported; left/right registry sizes are 4/3.
- **PASS.** The claimed no-O-Remove schedules are genuine checked executions, including the stronger activated-child variant, not hand-authored impossible traces.

### 6. Probe B — full public Theorem-73 boundary for both repaired pairs

**Evidence:** Idris REPL type dump `/tmp/dgamma-cp3-round10-boundary-types.txt`; source `src/DGamma/CP3VestigialChecks.idr:1112-1178,1969-2024`.

- Idris reports both wrappers' first argument literally as `confluenceTheorem Nat ToyKey ToyValue ToyRuntime String`; neither uses a private theorem or a weakened shadow alias.
- Each wrapper retains the complete premise sequence: both alignments, both registration disciplines, well-formed/empty initial registry, both quietness proofs, both no-failure proofs, both all-trace component-totality witnesses, both trace-independence witnesses, then the concrete `SameOrchestrationModuloGenerated` package.
- Source inspection confirms each implementation invokes that `claim` directly in public theorem order with its concrete checked 23/18 or 27/18 traces and same-input package.
- Each wrapper then projects from the actual `ConfluenceResult`: existential `finalRegistrationCorrespondence` paired with `finalEndpointsEquivalent : SystemEquivalentByRenamingModuloVestigial ...`, indexed by the same generated-tree relation and endpoint raw-name bijection. This is the repaired vestigial-aware conclusion, not exact-domain `SystemEquivalentByRenaming`.
- Both concrete `Maybe` correspondence witnesses evaluate successfully (covered again in the runtime aggregate below).
- **PASS.** The no-O-Remove pairs reach the full public theorem boundary and the intended new conclusion type.

### 7. Probe C — live `ServiceA` provider rejection and exact failing conjunct

**Probe extension:** independent runtime module now calls `vestigialEndpointGeneration` on live provider 3 while deliberately supplying a current generation and fabricated discarded-list membership; both pair runs remain `True` because the checker returns `Nothing`.

- At the executable checker (`src/DGamma/CP3.idr:2448-2508`), the concrete provider fiber is not retired, so pattern matching rejects it first at **`vestigialRetired`** (`retired = False`), before later inertness tests.
- The committed eliminator `liveProvidingFiberVestigialRejected` (`src/DGamma/CP3VestigialChecks.idr:2048-2063`) assumes the entire `VestigialEndpointGeneration` record—not merely discarded metadata or one isolated field—plus concrete support/provision facts. It delegates to `supportedGenerationNotVestigial`, which derives `Void` specifically from **`vestigialUnsupported : isSupported ... = False`** contradicting the provider's proved `isSupported ... = True`.
- The `providerOf ServiceA = Just 3` argument is semantically corroborating but is not needed for the contradiction; support alone excludes the complete certificate. This is not a strawman: the premise is the complete certificate carrying current stamp, discarded birth, presence, retirement, clean inactivity, empty table, childlessness, and unsupportedness.
- **PASS.** Live provider rejection is substantive; operational rejection occurs at retirement, while the total complete-certificate eliminator chooses the unsupported conjunct.

### 8. Conclusion-weakening attack matrix — vestigial inertness fields

**Probe:** `IndependentVestigialRuntime.inertnessMatrix`; combined executable output remains `(True, (True, True))`, with the final `True` covering this matrix.

- **Retired-but-providing:** independently stopped provider 0 immediately after `O-Retire`, while it remains Active with its `ServiceA` table installed; `providerOf ServiceA = Just 0`. Even with fabricated current/discarded metadata, the checker rejects it at **clean-Inactive** (its retirement field passes, lifecycle does not). Its nonempty table would independently fail the next field.
- **Empty-table-but-supported:** final child 4 is supported and has an empty table. The checker rejects it first at **retired** (`False`), and its Active lifecycle also fails. The explicit `vestigialUnsupported` field gives the propositional second barrier. A supported fiber cannot satisfy the certificate merely because it provides no key.
- **Childful inert fiber:** constructed a retired, clean-Inactive, empty-table child 2 with a currently present child 5. The checker reaches and rejects **`vestigialHasNoChild`**.
- **Childless but parent of a removed fiber:** after retiring/removing child 5, the same endpoint fiber 2 is accepted by the endpoint-shape checker. This is faithful, not a weakening: paper Lemma 57 quantifies current parent pointers, not historical children. Moreover, the registration scanner separately accounts for child 5—matching it if its parent activation survives, or discarding it only if that activation closes—so removed history is not silently erased by the endpoint certificate.
- **Clean-Inactive with effectful history:** historical effects are not checked by the certificate, correctly: Lemma 57 is an endpoint notion. False residual effects cannot be hidden because `SystemEquivalentByRenamingModuloVestigial` separately requires exact ambient equality and every table lookup equal under renaming. If recovery erased the history, quotienting it is intended; if residue remains, the effect fields reject the endpoint relation.
- **PASS.** No live-ish fiber can be misclassified through any one inertness field. The two seemingly redundant checks (`retired` and `unsupported`) are deliberate independent barriers at the record boundary, although support's definition already begins with not-retired.

### 9. Probe D — cross-side asymmetry (left vestigial raw 2, right live raw 2)

**Probe:** `/tmp/dgamma-cp3-round10.B88GBM/src/VestigialAsymmetryProbe.idr`; total core-only module typechecks.

- Proved `systemCannotHideRightLivePreimage`: for any `SystemEquivalentByRenamingModuloVestigial`, if the left lookup at a name is absent, the right lookup at its renamed image is present, and that right fiber cannot carry a vestigial certificate, then `Void` follows.
- The proof exhausts all four disposition families. Exact control matching cannot relate absent/present; left-vestigial/right-absent contradicts right presence; the other two unmatched/both-vestigial branches require a right certificate and are eliminated by live non-vestigiality.
- Therefore identity mapping directly refuses “left vestigial raw 2 / right live raw 2.” Choosing a nonidentity raw bijection cannot evade the guard: because the bijection is surjective and `controlsModuloVestigial` is quantified over every source name, the live right name is examined at its left preimage and must have an exact live counterpart or itself be certified vestigial.
- If another genuinely corresponding live fiber exists on the left and the bijection maps it to right raw 2 while sending left vestigial raw 2 to an absent right name, acceptance is correct fresh-name renaming—not hidden live structure.
- **PASS.** No cross-side asymmetric live structure is erased by the quotient.

### 10. Premise attack — reactivation and fabricated discarded births

**Probe:** `/tmp/dgamma-cp3-round10.B88GBM/src/ScannerBoundaryProbe.idr`; total module typechecks. Runtime probe additionally confirms `LBegin 2` is inapplicable at both repaired final endpoints' retired child 2.

- A **parent** can reactivate without O-Remove, so multiple episodes share one O-Insert generation. This is intentional: `RegistrationActivation` pairs that generation with the exact `LBegin` ordinal; `advanceRegistrationIndex` replaces the live activation at each begin and removes it at unload. The 23-action pair itself exercises closed and surviving activations of parent generation `1@1` without conflating them.
- A generated child can also have episodes while its birth's registering-parent activation is destined to close; the 27-action pair exercises this. It may even reactivate before retirement, still at one child generation. Once the registering parent's recovery retires it and it reaches clean Inactive, checked `LBegin` is impossible because `target = ⊥`; the runtime negative check confirms no later post-retirement episode can make a certified final fiber live again.
- Proved `discardedBirthHasActivation` and `discardedBirthHasLaterUnload`: every `DeletedClosingRegistration` necessarily carries `eventParentActivation = Just ...` plus an actual later `LUnload` of that event's parent. A birth outside any activation, or one whose parent episode remains open through the endpoint, cannot be stamped discarded.
- Proved `survivingBirthCannotBeDiscarded` by structural recursion over `NoParentUnload`: the explicit later unload evidence in `DeletedClosingRegistration` contradicts the surviving certificate. Thus the scanner cannot arbitrarily choose whichever classification helps a candidate.
- Raw-name remove/reissue cannot let an unrelated later episode donate the unload: checked O-Remove of an installed parent requires its old episode to unload first. Hence existence of any later unload after the event already closes the activation current at the birth, even if the witness points to a still later occurrence.
- **PASS.** No premise-side fabricated deletion or reactivation escape was found.

### 11. Symmetry, transitivity, and canonicalization composition sanity

**Probe:** `/tmp/dgamma-cp3-round10.B88GBM/src/BijectionCompositionProbe.idr`; total definitions of inverse/composition for both `NameBijection` and `RegistrationGenerationBijection` typecheck.

- Pointwise, the endpoint relation is the ordinary exact renamed relation after erasing only certified vestigial domain points. Its four dispositions are symmetric under inverse renaming: exact↔exact, left-vestigial/absent↔absent/right-vestigial, and both-vestigial↔itself.
- Transitivity's potentially dangerous case is an absent/vestigial intermediate. Probe D rules out a live fiber on the far side: absent can compose only with absent or a certified vestigial; a certified vestigial can match exactly only another fiber with the same retired/clean-Inactive control shape, or be erased. Ambient/table equalities compose directly under the composed raw bijection.
- Scanner classifications are trace-determined rather than witness-selectable (`survivingBirthCannotBeDiscarded`). Thus a middle current birth certified discarded in one comparison cannot be treated as surviving in another comparison to manufacture an outer live match. Surviving registration-tree generation bijections and parent-local positions compose normally.
- Canonicalization remains compatible: each `CanonicalSchedule` already validates withdrawals by `canonicalRegistrationTree`, while `ConfluenceResult` carries a direct final endpoint quotient rather than assuming exact-domain equality. The result does not infer equivalence merely from two unrelated canonical endpoints.
- The project exports no general reflexivity/symmetry/transitivity theorem for the **trace-indexed** full relation, nor constructors composing `RegistrationTraceCorrespondence`; these remain part of the declared general endpoint-assembly/proof debt. I found no countermodel to equivalence, but this algebraic closure is manually audited rather than mechanized.
- **PASS with residual proof debt, not a statement defect.** Name/generation bijections themselves compose and invert constructively, and no non-transitive live/vestigial case survives the certificates.

### 12. Requested prior-witness spot checks

**Probe:** `/tmp/dgamma-cp3-round10.B88GBM/src/PriorSpotRunner.idr`; output is 14 values, all `True`.

- **24/18 activation-reset pair:** runtime and full correspondence checks remain `True`; source still classifies the removed child birth as deleted, final child positions as 0/0, and `episodeBoundaryTheorem73PremiseChain` still accepts the literal public theorem alias with every premise.
- **Cross-parent permutation:** runtime/full correspondence remain `True`; mapped child generations still swap the cross-parent global ordinals while each parent's local position is 0.
- **1-vs-2 fresh-name pair:** `freshChoiceCorrespondenceCheck=True`; historical generation-wise renaming remains separate from current-root naming.
- **Nine-action self/canonical trace:** runtime, canonical replay, and proof-indexed trace checks all remain `True`; generation-stamped raw-role reuse is intact.
- **Removed-root guard:** executable empty-endpoint history remains `True`. `CompleteRemovedRootPermutationCandidate` still contains the full `SameOrchestrationModuloGenerated` package plus equality to the forbidden permutation, and `historicalExternalRootPermutationRejected` derives `Void` from exact first-root occurrence coupling.
- **Identity deletion:** `/tmp/.../IdentityDeletionExpectedFailure.idr` is rejected exactly at `KeepAction`'s `Not (deletable action)` argument: Idris reports a mismatch between reflexive action equality and `Void`. Deletable actions still cannot be retained.
- **PASS.** No round-10 regression in the requested historical witnesses.

### 13. Faithfulness adjudication — certificate and effect/control conclusion

- **Literal Lemma-57 fields match exactly.** `vestigialRetired`, `vestigialInactiveClean = Inactive Nothing`, empty owned-table bindings, and `hasChild = False` are precisely paper Lemma 57's `τ=⊤`, `θ=Inactive(⊥)`, `σ=∅`, and no current parent pointer to the name.
- **`vestigialUnsupported` is not an extra semantic refusal.** Definition 67 support begins with not-retired, so any fiber satisfying `vestigialRetired=True` is already unsupported. The explicit field is redundant but useful as a direct negative barrier; it cannot reject a paper-vestigial fiber that passed retirement.
- **Current-generation/discarded-birth evidence is intentionally stronger than generic Lemma 57, but faithful at this boundary.** The quotient is used for Lemma 72/Theorem 73, where an unmatched present name must belong to `R`, the births of a closing registration episode. Generic vestigial entries unrelated to a deleted episode either appear exactly on both sides or are governed by shared external orchestration; permitting them to disappear would weaken Theorem 73 incorrectly.
- **No missing inertness condition found.** Presence/current-stamp ties the certificate to the actual endpoint fiber; current childlessness is all Lemma 57 requires; declared component provisions need not be empty because the empty installed table and non-Active lifecycle mean the fiber currently provides nothing. Historical children/effects are separately controlled by the scanner and exact effect comparison.
- **Effects exact under renaming is the right companion.** Paper's `≈` compares ambient state and installed tables exactly while forgetting control ownership; `exactRenamedAmbient` plus pointwise `exactRenamedTables` implements exactly that after Lemma-56 naming. The control quotient then implements Equation-53-style exact renamed controls outside certified `R` names. Observational equality debt inside function-valued control/effect fields remains the already documented exact-equality host specialization, not a new vestigial defect.
- **PASS.** The certificate is neither too weak nor materially too strong for Lemma 72's outside-`R` equivalence, and the conclusion retains the paper's required effect strength.

### 14. README/NOTES truthfulness audit

- Read `README.md` fully and all 917 lines of `NOTES.md`.
- **Vestigial quotient description: PASS.** Both documents state that current coupling skips only exact trace-derived discarded generations, list retired/clean-Inactive/empty-table/childless/unsupported evidence, preserve exact effects and exact non-vestigial controls, and describe the 23/18 and 27/18 no-O-Remove pairs plus live-provider rejection. They no longer imply exact raw registry domains.
- **Debt/status list: PASS.** Theorem 73 is “submitted for round-10 review,” not proved. Constructive deletion, canonical sorting, and general endpoint assembly remain explicit; temporal accumulator induction, ranked Progress, Lemmas 68/70/71/72, and the eleven statement-only theorem aliases are retained. `confluenceTheorem` appears under both partial structural work and “merely stated” alias status with the distinction explained.
- **Errata: PASS.** The three Section-4 issues remain explicit: Lemma-68/O-Insert yielded provenance, Lemma-72 selected-retirement proof-intent ambiguity, and Lemma-56 raw-name reuse. The new likely Theorem-73 full-domain clarification is also recorded, accurately explaining why Lemma 72's outside-`R` result requires the quotient.
- **Over-approximation disclosure: PASS.** README Definition 47 and NOTES state plainly that one unconsumed tagged source head may license several fresh child names, unlike one literal Definition-47 yield; ranks/retirement justify the limited host result. Finite continuations, exact equality, trace-generated monoids, and dictionary alignment remain disclosed.
- Minor wording nuance only: README's Lemmas 54–57 row calls the whole certificate the “exact Lemma-57 inert endpoint shape” while including the additional discarded stamp/unsupported field. The source and the Theorem-73 row explicitly say it is trace-augmented, so this does not create a material false claim.
- **PASS.** Documentation is final-review truthful for the submitted statement and all declared debt.

### 15. Escape-hatch, hole, totality, and hygiene scans

- All **13/13** packaged `src/DGamma/*.idr` modules contain exactly one `%default total`.
- Anchored source scans find zero `believe_me`, `assert_total`, postulate declarations, `%unsafe`, `%foreign`, `%default partial`/`covering`, partial/covering declarations, or named metavariable holes.
- Exactly **11** `TODO(proof)` markers remain, matching the documented statement-only declarations: 3 in `Unified`, 3 in `Metatheory`, and 5 in `CP3`.
- No staged or tracked diff exists. Repository status is only pre-existing untracked `paper/` plus this explicitly authorized `review-cp3-round10.md`; all generated probes remain outside the repository.
- **PASS.** No hidden proof inhabitant, totality escape, or source contamination was found.

### 16. Runtime aggregates

- A fresh-archive runner evaluated the eleven individual `DGamma.CalculusChecks` values plus `allRuleChecks`, the nine individual `DGamma.CP3StatementChecks` values plus its aggregate, and the five new `DGamma.CP3VestigialChecks` values plus its aggregate.
- Output is **28/28 `True`**. The task's closing 14-value regression set (24/18, prior correspondence/runtime spots, both vestigial pairs, and live provider) separately printed **14/14 `True`**.
- **PASS.** All committed executable regressions evaluate at `b7f12c9`.

### 17. Genuinely clean archive build

- Created a second untouched `git archive b7f12c9` at `/tmp/dgamma-cp3-round10-clean.cL1vAg`, with no probe source and no inherited TTC cache.
- Ran `idris2 --clean dgamma.ipkg && idris2 --build dgamma.ipkg` under Idris 2 0.8.0.
- **PASS: all 13/13 package modules rebuilt successfully**, including `DGamma.CP3VestigialChecks`.

## Round-9 finding disposition

| Round-9 finding | Round-10 disposition |
|---|---|
| **BLOCKER:** discarded-but-unremoved current generations still had to biject | **FIXED.** `CurrentEndpointRenaming` (`src/DGamma/CP3.idr:2516-2560`) now permits omission only through the complete trace-derived vestigial certificate. Independent 23/18 and 27/18 executions have 4-vs-3 domains, construct complete same-input witnesses, and reach the public theorem boundary. |
| **BLOCKER:** exact-domain `finalEndpointsEquivalent` could not state absent/vestigial | **FIXED.** `ConfluenceResult` now returns `SystemEquivalentByRenamingModuloVestigial` (`src/DGamma/CP3.idr:2638-2659,3053-3073`): exact ambient/tables, exact controls unless certified vestigial, and symmetric unmatched-side cases. |
| **MAJOR:** 24/18 regression's early child O-Remove masked the paper case | **FIXED.** New 23/18 and activated-child 27/18 pairs omit child O-Remove, execute successfully, build full relation packages, and project the vestigial-aware conclusion (`src/DGamma/CP3VestigialChecks.idr:1122-1177,1969-2024`). |
| **MAJOR documentation consequence:** quotient/proposition debt omitted | **FIXED.** README/NOTES describe the exact quotient, no-O-Remove pairs, live-provider rejection, likely Theorem-73 clarification, and remaining proof debt accurately. |

## Whole-project final debt summary

### Declared/pre-approved proof and representation debt

- Definition 32 remains an explicitly finite approximation. Lemma 38 proves only the relational composition/accumulator core. Lemma 35 and Theorems 40/42 are precise statement-only types.
- Section 4 retains disclosed finite static continuations, explicit tagged/catalogued registration (including one-source-head/many-name over-approximation), trace-generated full-effect monoids, exact effect equality, and explicit dictionary alignment.
- Lemmas 54–57 are only partially packaged; the new certificate covers the exact Lemma-57 endpoint shape needed here, not its whole rule bisimulation.
- Theorem 61, Corollary 62, and the recovery branch of Theorem 64 still need the temporal accumulator induction.
- Progress/Theorem 66 still needs unloading-chain no-deadlock and Equation-61 ranking.
- Lemmas 68/70/71/72 and Theorem 73 retain declared constructive proof debt: support induction, control applicability frames, checked deletion, canonical sorting, and general endpoint assembly. The trace-indexed quotient's general symmetry/transitivity constructors are not separately mechanized and belong to that assembly debt.
- Exactly eleven `TODO(proof)` declarations remain. None has an exported inhabitant, postulate, unsafe escape, or partial definition.

### Final statement/fidelity assessment

- No remaining false, vacuous, or materially over-strong public statement was found.
- No conclusion-weakening countermodel was found: every unmatched present fiber is a scanner-proved discarded birth satisfying all Lemma-57 inertness fields; live structure is total-pointwise protected on both sides; effects stay exact.
- The three historical Section-4 errata/deviations and all remaining theorem debt are documented. Theorem 63 and prior accepted CP1/CP2 results were not reopened.

## Final findings

1. **VERIFIED FIX — `src/DGamma/CP3.idr:2409-2659`:** vestigial omission requires current discarded generation, fiber presence, retired, clean-Inactive, empty table, childless, and unsupported evidence. Independent attacks show retired providers, supported empty fibers, and childful inert fibers are rejected at the intended fields.
2. **VERIFIED FIX — `src/DGamma/CP3.idr:3053-3073`; `src/DGamma/CP3VestigialChecks.idr:1122-1177,1969-2024`:** both no-O-Remove pairs use the literal public `confluenceTheorem`, retain every semantic premise, and project the new vestigial-aware result.
3. **VERIFIED NEGATIVE — `src/DGamma/CP3VestigialChecks.idr:2030-2067`:** the concrete supported `ServiceA` provider cannot inhabit the complete vestigial certificate; the total contradiction uses `vestigialUnsupported`, while the executable checker rejects earlier at `vestigialRetired`.
4. **VERIFIED QUOTIENT SAFETY:** a total typed eliminator proves an unmatched live right fiber cannot be hidden by left absence/vestigiality under any raw bijection; scanner classifications cannot treat one birth as both surviving and discarded.
5. **VERIFIED REGRESSIONS:** requested prior witnesses remain substantive; 14/14 closing regressions and 28/28 full runtime values are `True`; identity deletion fails at `Not deletable`; removed-root rejection still starts from a complete candidate.
6. **VERIFIED QUALITY:** clean archive build 13/13; all 13 modules `%default total`; zero escape hatches/unsafe/partial/named holes; exactly 11 documented statement-only TODOs; docs truthful.
7. **RESIDUAL RISK (declared proof debt, non-blocking):** full symmetry/transitivity and canonical endpoint assembly are manually audited but not separately mechanized; the public Theorem-73 alias itself remains uninhabited pending the declared constructive proof.

# Final verdict: ACCEPT

FINAL VERDICT: ACCEPT
