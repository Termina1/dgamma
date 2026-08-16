# Checkpoint 3 adversarial review — round 8 (closing round)

**Target:** `cd5659eee0ba93f54bb3552d74c035197d99d334`
**Scope:** paper Section 4.4; parent-local Theorem-73 matching and external-root coupling repairs; requested regressions, adversarial attacks, documentation, build, runtime, and escape-hatch audits
**Mode:** review only. No repository sources, package, README, NOTES, or tracked tests are edited. This report is the explicitly authorized reviewer output. All probe files remain outside `/Users/vyacheslavshebanov/Work/dgamma`.

## Incremental audit log

### Baseline and mandatory prior-review read

- Confirmed exact requested HEAD `cd5659eee0ba93f54bb3552d74c035197d99d334`.
- No staged or tracked modification existed before this review. The sole pre-existing untracked path was `paper/`; `review-cp3-round8.md` is this authorized review artifact.
- Read `review-cp3-round7.md` (170 lines) and `review-cp3-round6.md` (169 lines) fully. Round 7's two defects are understood precisely: one global generated-event scanner refused cross-parent scheduling permutations; the dual missing historical-root anchor admitted reassignment of removed-root subtrees.
- Skimmed rounds 1–5 by their finding/disposition structure. Their history is consistent with the standing-results exclusions in the task; those accepted results will only receive the explicitly requested spot checks.

Further results are appended immediately after each completed probe or audit item.

### Paper Section 4.4 baseline

- Read Section 4.4 fully (`paper/cordis-paper.txt:1603-2385`), including Lemma 56 and Theorem 73's complete statement/proof.
- Fidelity criterion: Lemma 56 transports a whole sequence by one raw-name bijection, while Theorem 73 applies it informally to match fresh **registration trees below each supported fiber**. Definition 60 fixes, at each parent iterator stage, both the component registered and continuation across interleavings; it does not impose a global chronological order across independent parents. Thus a faithful implementation may use generation identities to resolve legal raw-name reuse, but matching must be recursive through mapped parents, preserve a parent's iterator/yield order, ignore cross-parent scheduling order, and anchor orchestrator O-Insert births to the same external input occurrences.
- A per-parent position is faithful only if it counts the iterator registrations belonging to the relevant parent activation/registration-producing run in the way the paper's continuation fixes. Whether the submitted counter is generation-global or resets across separate parent episodes is therefore a central new audit target, not assumed correct.

### Immutable review workspace and repair-diff inspection

- Created immutable `git archive cd5659e` at `/tmp/dgamma-cp3-round8.uf8tOP`; all Idris probes will live there or in another `/tmp` tree.
- Inspected the four repair commits (`96f2f37`, `3f97919`, `8a0d400`, `cd5659e`). `git diff --check 6fbc0fd..cd5659e` passes. Relevant code changes are confined to `DGamma.CP3` and `DGamma.CP3StatementChecks`; README/NOTES describe them. The diff also archives earlier authorized review reports.
- Toolchain is Idris 2 **0.8.0**.

### Probe 1 — independent 12-action cross-parent reconstruction and public Theorem-73 boundary

- Built `/tmp/dgamma-cp3-round8.uf8tOP/src/IndependentCrossParentProbe.idr` in a fresh namespace importing only `Calculus`, `Coeffects`, `Metatheory`, and `CP3` (not `CP3StatementChecks`). It defines its own empty-key components/protocol, checked named-transition wrapper, and both 12-action traces.
- Both traces independently execute: exact external root births `0@0,1@1`; both parents begin; left births child `2` of parent 0 at ordinal 4 then child `3` of parent 1 at ordinal 5, while right births those same child/parent pairs in the opposite global order; all four fibers then finish. The runtime quiet/success/support aggregate prints `True`.
- The probe constructs `RegistrationGenerationBijection` with `(2,4)↦(2,5)`, `(3,5)↦(3,4)`, and both root generations fixed. Its pending-event scanner matches each child at local position 0 under mapped parents `(0,0)` and `(1,1)`, then packages exact external inputs, every historical root coupling, generated-tree correspondence, identity endpoint names, and current generation coupling into `SameOrchestrationModuloGenerated`.
- Its `crossParentPermutationTheorem73PremiseChain` takes the literal exported `confluenceTheorem Nat ...` alias, all premises in declared order, this exact concrete same-input witness, and returns the exact bijection-indexed `ConfluenceResult`. The module typechecks under Idris 2 0.8.0.
- **Round-7 chronological-order BLOCKER disposition: FIXED.** The repaired relation genuinely ignores cross-parent chronology and the concrete legal permutation reaches the full public theorem boundary.

### Probe 2 — historical external-root generation permutation rejection

- Extended the independent probe with two concrete checked six-action traces: root 0 is inserted, retired, and removed; then root 1 is inserted, retired, and removed. Both endpoints are empty, so current-root/current-generation constraints cannot accidentally reject the attack. Construction executes and prints `True`.
- Defined a genuine generation bijection swapping the removed external births `(0,0)` and `(1,3)`. The total eliminator `concreteHistoricalPermutationRejected` accepts an alleged complete `SameOrchestrationModuloGenerated` for those concrete traces plus equality of its packaged bijection to that permutation, projects **only** `externalRootGenerationsCoupled`, obtains the first exact root match through `firstExternalRootBirthMapped`, and reduces the resulting `(1,3)=(0,0)` equality to `Void`.
- **Round-7 historical-root MAJOR disposition: FIXED.** The rejection occurs at the intended historical external-root coupling, even with empty endpoints; it is not being masked by live-root fixed points or current-generation coupling.

### Probe 3 — BLOCKER: child position is global to a parent lifetime, not local to an activation

**Files:** `src/DGamma/CP3.idr:1898-1963,1981-2014,2022-2156,2236-2250`; paper `cordis-paper.txt:2321-2350`.

- Built `/tmp/dgamma-cp3-round8.uf8tOP/src/EpisodePositionProbe.idr`. It executes two quiet, successful checked schedules with identical external root inputs/retirements/replacement and the same final supported parent/child. In the left schedule, parent 1 begins against provider 0, produces child 2, is diverted/unloaded after provider 0 retires, and later reopens against replacement provider 3 and produces child 4. In the right schedule, parent 1 is simply delayed until provider 3 and produces only final child 4. The runtime aggregate prints `True`.
- This is exactly lifecycle nondeterminism paper Theorem 73 quotients. The registration-producing step is tagged and restarts from the component's initial iterator at each `L-Begin`; the first child of each activation is therefore iterator position 0. Paper's proof first deletes closing episodes, then matches the registration tree of the one surviving episode below each supported fiber.
- The implementation never observes `L-Begin`/`L-Unload` in its child counter. `indexedChildCounts` is keyed only by the parent's O-Insert generation and is incremented for every child birth until that parent is O-Removed. The compiled probe proves that child 4 is assigned position **1** after the earlier closed episode on the left but position **0** on the right, and `resetPositionCannotMatch` eliminates a `RegistrationEventMatch` exactly through `matchedPerParentPosition`.
- More fundamentally, `RegistrationTraceCorrespondence` requires **every historical generated birth** in both original traces to be consumed once and ends only with both pending lists empty. Thus the concrete paper-legal pair with one deleted historical child versus none is excluded even before canonical deletion; same external orchestration alone cannot reach the public `confluenceTheorem` premise.
- **Severity: BLOCKER (over-strong/unfaithful theorem domain).** “Per-parent position” is not the paper's iterator position across multiple activations, and matching entire pre-canonical registration histories wrongly requires schedule-dependent closing episodes to have identical generated cardinality. A faithful statement must derive/match the surviving canonical registration trees after deleting closed episodes, or at minimum key yields by mapped parent **episode** plus iterator position and permit unmatched births belonging to deleted episodes.

### Probe 4 — same-parent siblings, component mismatch, and recursive mixed chains

- Built `/tmp/dgamma-cp3-round8.uf8tOP/src/ParentLocalAttackProbe.idr`; all expected rejection/positive witnesses typecheck.
- **Same-parent same-component sibling swap:** attempting to pair the position-0 child with the position-1 sibling is eliminated by `matchedPerParentPosition`. Because every event is consumed exactly once and the generation bijection is injective, a same-component sibling cannot be duplicated or silently reassigned. Descendant fate follows the mapped child generation, so correct direct-child positions pin subtrees as intended.
- **Component mismatch:** two events with identical child generation, mapped parent generation, and position but components `MkComponent ... []` versus `MkComponent ... [oneStep]` are eliminated by `matchedComponent`. The rejection is exactly at `RegistrationEventMatch.matchedComponent` (`src/DGamma/CP3.idr:2003`), not an incidental ordinal mismatch.
- **Mixed root/child/grandchild chain:** the positive probe uses different raw parent/child names on the two sides. It first matches the generated parent births under a fixed root, then matches grandchild births whose parent generations are related by the same nontrivial generation bijection. Both `RegistrationEventMatch` values inhabit. Thus `matchedParentGeneration` is genuinely **mapped**, not raw; exhaustive one-use event matching makes the recursion anchor at `ExternalRootBirthCorrespondence`.
- **PASS for these attack classes.** No same-episode sibling reassignment, component substitution, or raw-parent shortcut was found. The blocking defect remains the missing activation-episode dimension/full-history overconstraint from Probe 3.

### Audit 5 — committed regression substance

- `crossParentPermutationTheorem73PremiseChain` (`src/DGamma/CP3StatementChecks.idr:1676-1724`) literally accepts `confluenceTheorem Nat ...`, takes every public premise in the alias's order, passes `crossParentBlockerSameInputs witness`, and returns the exact generation/current-renaming-indexed `ConfluenceResult`. **PASS.** It is not a shadow theorem or projection-only check.
- `CrossParentPermutationCorrespondenceWitness` contains both checked 12-action traces and the complete `SameOrchestrationModuloGenerated` package. The independent strengthened runtime check additionally tests support of all four names on **both** endpoints and prints `True`. The committed `crossParentPermutationRuntimeCheck` tests right quiet/success but only left support; this small omission does not undermine the typed full-package regression.
- `historicalExternalRootPermutationRejected` (`:392-408`) does derive `Void` at the exact new conjunct, but its premise is only a generic `ExternalRootBirthCorrespondence` for traces beginning with root 0. It packages neither a concrete removed-root trace nor the rest of `SameOrchestrationModuloGenerated`; by the task's “complete permuted witness” standard it is a **strawman/weak negative regression**. The independent removed-root `SameOrchestrationModuloGenerated` eliminator in Probe 2 supplies the missing complete-context check and confirms the implementation repair itself.
- **Severity: MINOR regression-strength defect — `src/DGamma/CP3StatementChecks.idr:388-408`.** The source relation is genuinely repaired, but the committed negative guard is materially weaker than advertised/requested project-closing evidence.

### Audit 6 — requested prior-witness spot checks

- A clean probe runner prints `[True, True, True, True]` for the 1-vs-2 fresh-choice correspondence, nine-action role-changing runtime, six-action canonical replay comparison, and proof-indexed nine-action trace. Source inspection confirms the fresh pair still maps only historical `(1,2)↔(2,2)`, fixes later root `(1,5)`, includes exact historical-root coupling, and packages the complete same-input relation used by the literal theorem chain.
- The nine-action self-canonicalization remains generation-stamped: `roleChangingFullCanonicalScheduleStatementCheck` still assembles every `CanonicalSchedule` field for that exact trace, forces current raw withdrawals to `[]`, and forces historical withdrawals to `[(1,2)]`; the executable six-action replay remains quiet/successful with both final roots Active. No round-8 matching change touched canonical deletion accounting.
- In the independent core-only namespace, reconstructed `independentPositiveParentRegistrationYield` projects an actual `sourceStep` member of the parent's nonempty program. `independentPositiveCannotBeEmpty` eliminates the same witness after a hypothetical `componentProgram = []`; the positive and negative guards are not premise-vacuous.
- `/tmp/.../IdentityDeletionExpectedFailure.idr` attempts to keep a transition when `deletable action = (action = action)`. Idris rejects it exactly at `KeepAction`'s fifth argument: equality cannot inhabit `Not (deletable ...)`. **PASS.** The mandatory deletion barrier remains structural.

### Audit 7 — README/NOTES truthfulness

- Read `README.md` and all 837 lines of `NOTES.md` fully.
- **General correspondence/debt labels: PASS.** Theorem 73 is “submitted for round-8 review,” not called proved. The eleven statement-only declarations and constructive deletion/sorting/general endpoint debt are retained. Section 3/CP2 statuses remain consistent with earlier accepted reviews.
- **Errata/deviations: PASS.** The Definition-32 negative-recursion issue, Lemma-68/O-Insert provenance erratum, Lemma-72 selected-retirement proof-intent ambiguity, and Lemma-56 raw-reuse ambiguity are preserved. Finite continuations, explicit dictionary alignment, exact effect equality, and the tagged/catalogued host specialization remain disclosed.
- **Over-approximation disclosure: PASS.** README Definition 47 and NOTES explicitly state that one unconsumed tagged source head may license several child names and classify it as a rank-preserving over-approximation; no one-yield claim is hidden there.
- **MAJOR documentation consequence of Probe 3 — `README.md:123`; `NOTES.md:631-640,659-687,760-814,829-837`.** The new text calls the lifetime-global count a “per-parent child/yield position” that preserves iterator order and says the two round-7 proposition-shape defects are closed. It does not disclose that the count never resets at a new activation, that multiple first yields of the same parent generation receive positions 0,1,…, or that all schedule-dependent historical births must be bijected before deletion. The Status/Next section therefore omits a blocking proposition-shape repair and incorrectly proceeds directly to constructive proof work.
- The docs are cautious about acceptance, but the concrete semantic description is still false. They must distinguish parent **generation** order from parent **activation/iterator** position and add the full-history overconstraint to debt.

### Audit 8 — Lemma-56 / Theorem-73 faithfulness adjudication

- The **generation/current-name split is honest**: it resolves a real conflict between Lemma 56's one raw bijection and Preservation's legal remove/reuse, while still comparing current registries coherently.
- The **external-root coupling is honest**: same orchestration fixes each externally supplied root action in order, so anchoring every root birth generation to that exact occurrence prevents distinct external histories/subtree reassignment without restricting lifecycle scheduling.
- The **pending parent-local matcher is honest for one canonical activation tree**: exact component, mapped child, mapped parent, and local order recursively define the ordered registration tree, while pending events correctly forget independent parents' global interleaving.
- The submitted public premise applies that matcher at the wrong semantic level. Paper Theorem 73 deletes closing episodes first and then compares the trees produced by the surviving one-episode-per-supported-fiber canonical schedules. The implementation instead scans the unreduced histories, counts births over a whole parent lifetime, and insists those schedule-dependent histories are bijective.
- Consequently it both misnames lifetime rank as iterator position and refuses Probe 3's legal delay/divert pair. This is proposition shape, not merely missing proof: no future inhabitant of `confluenceTheorem` can cover that pair because `SameOrchestrationModuloGenerated` excludes it.
- **Faithfulness verdict: FAIL / BLOCKER.** No new unsound acceptance of distinct canonical registration trees was found; the decisive defect is over-strengthening. Required repair: relate canonical surviving trees (preferably derive the relation from the semantic premises), or add mapped activation-episode identities, reset iterator position at each `L-Begin`, and allow unmatched child births proved to belong to deleted closing episodes.

### Audit 9 — totality, holes, escape hatches, and repository hygiene

- All **12/12** packaged `src/DGamma/*.idr` modules contain exactly one `%default total`.
- Anchored scans find zero `believe_me`, `assert_total`, postulate, `%unsafe`, `%foreign`, unsafe IO escape, `%default partial`/`covering`, partial/covering declaration, or named metavariable hole.
- Exactly **11** `TODO(proof)` declaration comments remain: three in `Unified`, three in `Metatheory`, and five in `CP3`. They match the statement-only theorem list; no TODO is an accepted inhabitant.
- `git diff --check` passes; no staged or tracked source modification exists. Status is only pre-existing `paper/` plus this explicitly authorized untracked `review-cp3-round8.md`. All probe sources remain under `/tmp`.
- **PASS.** No hidden proof/totality debt was found.

### Audit 10 — genuinely clean archive build

- Created a second untouched `git archive cd5659e` at the recorded `/tmp/dgamma-cp3-round8-clean.*` path, with no probes or inherited TTC cache.
- Ran `idris2 --clean dgamma.ipkg && idris2 --build dgamma.ipkg` under Idris 2 0.8.0.
- **PASS: all 12/12 package modules rebuilt successfully.**

### Audit 11 — runtime aggregates

- A review-only runner in the clean archive evaluated the eleven individual `DGamma.CalculusChecks` regressions, `allRuleChecks`, the six individual CP3 runtime/statement checks, and `allCP3StatementChecks`.
- Output: `[True, True, True, True, True, True, True, True, True, True, True, True, True, True, True, True, True, True, True]`.
- **PASS.** All 19 committed runtime aggregates succeed at `cd5659e`.

## Round-7 finding disposition

| Round-7 finding | Round-8 disposition |
|---|---|
| **BLOCKER:** global chronological child matching refused cross-parent schedule permutations | **FIXED.** Independent checked 12-action reconstruction maps `(2,4)→(2,5)` and `(3,5)→(3,4)`, builds full `SameOrchestrationModuloGenerated`, and reaches the literal public theorem chain. |
| **MAJOR dual:** historical external roots were uncoupled, permitting subtree reassignment | **FIXED.** Every root birth is chronologically/exactly generation-coupled; a concrete removed-root generation permutation collapses at that conjunct even with empty endpoints. |
| Documentation called the old scanner structural | **FIXED for both round-7 defects, but reopened for Probe 3.** The new prose accurately describes pending cross-parent matching and exact historical roots, yet falsely identifies lifetime-global counts with iterator/yield positions and omits closed-episode history over-strengthening. |

Both exact round-7 findings are closed. Round 8 finds a distinct activation-episode/theorem-domain blocker in the replacement.

## Whole-project final debt summary

### Honest, previously declared/pre-approved proof or representation debt

- Definition 32 remains an explicit finite tower approximation; Lemma 38 is only the proved relational core. Lemma 35 and Theorems 40/42 remain statement-only.
- Section 4 retains documented finite static continuations, tagged/catalogued explicit registration (including the one-head/many-name over-approximation), trace-anchored generated monoids, exact effect equality, and explicit dictionary alignment.
- Lemmas 54–57 have structural fragments but are not individually fully packaged.
- Theorem 61, Corollary 62, and Theorem 64's recovery branch still need the actual-accumulator temporal induction.
- Progress/Theorem 66 still needs unloading-chain no-deadlock and Equation-61 ranked counting.
- Lemma 71 lacks control applicability frames.
- Lemma 72 lacks the checked deletion induction. Theorem 73 lacks constructive deletion, sorting, and general endpoint assembly.
- These are explicit statement/proof debts without escape hatches and are not the reason for rejection.

### New blocking proposition/fidelity debt

1. Stop treating `childrenBornUnder (raw,birthOrdinal)` as iterator/yield position across all activations of that parent lifetime. A registration position must be scoped to a mapped activation episode and reset with the component iterator at `L-Begin`.
2. More importantly, do not require original traces to biject every registration from closing episodes that paper Lemma 72 deletes. Match the surviving canonical registration trees after deletion, or allow unmatched events with checked evidence that their parent episode/descendant subtree is deleted.
3. Add the checked delay-versus-divert/reopen pair as a negative-domain regression, update README/NOTES/Status/Next, and replace the generic historical-root guard with a concrete complete removed-root candidate.

## Final findings

1. **BLOCKER — `src/DGamma/CP3.idr:1898-1963,1981-2014,2022-2156,2236-2250`:** per-parent child counts persist for an entire parent O-Insert generation and ignore activation boundaries. A checked pair with the same external roots/replacement and same final supported parent/child assigns the final activation's first child position 1 after a deleted prior episode on the left, but position 0 when activation is delayed on the right. `matchedPerParentPosition` rejects the paper-legal pair.
2. **BLOCKER — same files / public `confluenceTheorem` domain at `src/DGamma/CP3.idr:2672-2697`:** `RegistrationTraceCorrespondence` consumes every historical generated birth and requires equal cardinality before canonical deletion. Paper Theorem 73 first deletes closing episodes, whose registration counts are schedule-dependent, and compares the surviving canonical trees. This is an over-strong proposition shape, not constructive proof debt.
3. **MAJOR documentation consequence — `README.md:123`; `NOTES.md:631-687,760-837`:** lifetime-global rank is called iterator/yield position, both round-7 proposition defects are declared closed, and Status/Next omits activation-episode/full-history debt.
4. **MINOR regression-strength — `src/DGamma/CP3StatementChecks.idr:388-408`:** the historical-root rejection guard assumes only the new root-coupling conjunct for arbitrary first root actions; it does not construct a complete removed-root permuted candidate. The relation itself is nevertheless verified fixed by the independent complete-context eliminator.
5. **VERIFIED FIX — round-7 cross-parent blocker:** independent 12-action traces are checked, quiet/successful/supported on both sides, inhabit the full same-input package, and cross the exact public theorem alias with all premises.
6. **VERIFIED FIX — round-7 historical-root dual:** exact coupling of every external O-Insert rejects generation permutation after roots are removed; current endpoint constraints do not mask the rejection.
7. **VERIFIED — local matching guards:** same-parent same-component sibling swaps fail at position; same-position component substitutions fail at exact component equality; grandchild matching uses recursively mapped generated-parent generations rather than raw names.
8. **VERIFIED — prior witnesses/project quality:** 1-vs-2 fresh choice, nine-action generation-stamped canonical replay/package, positive parent yield, empty-parent rejection, and identity-deletion barrier remain substantive; clean build 12/12; 19 runtime values `True`; 12/12 modules total; zero escape hatch/unsafe/partial/named hole; 11 explicit statement-only TODO sites.

# Final verdict: REJECT

The two round-7 repairs are genuine, but project acceptance cannot close. The parent-local replacement conflates parent lifetime order with activation-local iterator position and requires schedule-dependent registrations from deleted closing episodes to match. It therefore refuses a paper-legal same-orchestration pair before the public Theorem-73 result.

FINAL VERDICT: REJECT

### Post-verdict probe hardening

- Reordered the outside-repository episode probe so the historical child's O-Retire/O-Remove occurs **before** the parent's L-Unload recovery boundary, matching `ChildRetirementProvenance` rather than relying on a late manual retirement. The complete checked runtime still prints `True`, and the position-1-versus-position-0 eliminator still typechecks. The BLOCKER is unchanged and is not an artifact of retirement timing.

FINAL VERDICT: REJECT
