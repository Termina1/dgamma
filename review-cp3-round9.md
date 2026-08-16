# CP3 Round 9 Closing Adversarial Review

**Target:** `/Users/vyacheslavshebanov/Work/dgamma` at requested HEAD `c5ab667`  
**Scope:** Section 4.4 / Theorem 73 repairs and requested closing audits  
**Mode:** review only; all generated probes are outside the repository.

## Review log (appended item by item)

### 0. Baseline identity and cleanliness

- `git rev-parse HEAD` = `c5ab667760ac82636d5c0134b8452fe28ad8a16d`, exactly the requested revision.
- Initial tracked tree is clean. `git status --short --branch` reports only pre-existing untracked `paper/`; no source or repository report was created or edited by this review.

### 1. Mandatory prior-review reading and historical skim

- Read `review-cp3-round8.md` (164 lines) fully, then `review-cp3-round7.md` (170 lines) fully, in the required order.
- Round 8's two blockers are understood as distinct statement-domain failures: lifetime-global parent-generation ranks did not reset at activation, and all historical generated births had to biject before Lemma-72-style deletion. Round 8 also left a MINOR weak regression guard for removed historical roots.
- Skimmed rounds 1–6 by headings, dispositions, and final findings. Their repair lineage is consistent with the standing exclusions: support/reachability and selected-retirement defects; provenance vacuity; raw-generation reuse; cross-parent ordering; historical-root coupling; then activation/deletion scope.
- I will not redo the standing CP1/CP2, Theorem-63 ordering, full-premise non-vacuity, old countermodel, generation-stamped self-canonicalization, 1-vs-2 fresh-choice, or round-8 parent-local/external-root audits except for the requested spot checks.

### 2. Paper Section 4.4 fidelity baseline

- Read Section 4.4 in full (`paper/cordis-paper.txt:1603-2385`), including Definitions 53/58/60/65/67/69, Lemmas 54–57 and 68–72, and Theorem 73.
- Critical paper boundary: an **episode** is an installed interval opened by `L-Begin` and closed by `L-Unload`; a final episode may remain open at the compared endpoint. Lemma 72 deletes one selected episode that actually closes, plus all steps of names registered during it, under the explicit hypothesis that those children have no episode.
- Theorem 73(1) recursively deletes all closing episodes; only then does it retain one final open episode for each supported fiber, sort those surviving episodes, and obtain the canonical sequence. Part (2) matches registrations performed by those surviving canonical activations, parent-tree recursively and up to fresh-name bijection.
- Therefore the repair's intended `retain iff parent activation has no later L-Unload` is faithful only when (a) “parent activation” is the exact `L-Begin` occurrence, (b) births in a closed activation are removed with their descendants rather than left dangling, (c) a final open activation remains retained, and (d) the relation does not erase structural differences among births in surviving activations.
- Paper Lemma 72 expressly assumes a child registered by the selected closing parent episode has **no episode**. Thus a purported child fiber that itself begins/continues an activation cannot outlive deletion of that parent episode under the lemma's admissible deletion step; such a trace must be handled by first deleting maximal closing descendant episodes, not by orphaning a surviving child.

### 3. Immutable workspace and repair-diff inspection

- Created immutable `git archive c5ab667` at `/tmp/dgamma-cp3-round9.AagB95`; all compilable probes and generated runners will stay in `/tmp` copies.
- Idris toolchain is **Idris 2 0.8.0**.
- Inspected repair commits `eece7fb` (core relation), `53bc2e9` (hardened regressions), and `c5ab667` (documentation). Source changes are limited to `DGamma.CP3`, `DGamma.CP3StatementChecks`, README/NOTES, plus archived round-8 report. `git diff --check cd5659e..c5ab667` passes.
- The unusually large check-module diff (1,488 added lines in the hardening commit) warrants checking independently that the claimed 24/18 pair and complete removed-root rejection use public relation types rather than private shadows.

### 4. Probe A — independent delay/divert/delete/reopen reconstruction and full public boundary

**Probe:** `/tmp/dgamma-cp3-round9.AagB95/src/IndependentEpisodeProbe.idr` (1,500+ lines), importing core modules and **not** `DGamma.CP3StatementChecks`; runner prints `True`.

- Independently rebuilt the checked pair. Common actions 0–4 insert provider 0 and parent 1, then activate provider 0. Left has 24 actions: begin parent 1; register child 2; retire/remove child 2; retire provider 0; leave 0; divert/unload parent 1; unload/remove 0; insert/activate replacement 3; reopen parent 1; register child 4; finish 1; begin/finish 4. Right has 18 actions: it delays parent 1 until after provider 0 is retired/unloaded/removed and replacement 3 is active, then registers/finishes the same child 4 and activates it.
- Independent trace enumeration confirms the round-8 **old lifetime-position observation**: before final child 4, the left parent generation has one earlier generated birth (child 2) while the right has none — **1 versus 0**. Runtime `transitionCount` verifies **24 versus 18**.
- Both checked executions are quiet and failure-free and support exactly the intended final parent/provider/child names `1,3,4` on both sides. The deleted child is retired and removed before its parent `L-Unload`, so the pair does not exploit late manual cleanup.
- The new index stamps left activations `(parent 1@birth 1, begin 5)` and `(1@1, begin 19)` separately; the right surviving activation is `(1@1, begin 13)`. Child 2 has `DeletedClosingRegistration` from the later left `L-Unload 1`; final child 4 has `SurvivingRegistration` on both sides. Because deleted births do not consume `indexedSurvivingChildCounts`, both final births reduce to position 0 (`episodeBoundaryPositionsReset`).
- Constructed a complete `RegistrationTraceCorrespondence`: it discards only child 2, queues left child 4, matches right child 4 by exact component, mapped parent generation, child generation `(4,20)↔(4,14)`, and position 0, and ends with both pending lists empty. External roots `(0,0),(1,1),(3,15/9)` are exactly occurrence-coupled. Current raw names are identity-coupled while current generations map `3@15↔3@9` and `4@20↔4@14`.
- Therefore the pair genuinely inhabits full `SameOrchestrationModuloGenerated`, not merely its registration projection.
- The independent `episodeBoundaryTheorem73PremiseChain` accepts the literal exported `confluenceTheorem Nat ToyKey ToyValue ToyRuntime String`, then every public premise in declared order (alignment, discipline, well-formed empty start, both quiet/success, all-trace totality, both independence witnesses), supplies the concrete same-input package, and returns the exact bijection-indexed `ConfluenceResult`.
- **Round-8 activation-boundary BLOCKER disposition: FIXED. Round-8 pre-deletion full-history BLOCKER disposition: FIXED for the concrete hardened pair.**

### 5. Probe B — complete removed-root permutation guard

**Probe:** `/tmp/dgamma-cp3-round9.AagB95/src/IndependentRemovedRootProbe.idr`, core imports only; typechecks and its six-action runtime prints `True`.

- Independently built the concrete history `insert 0; retire 0; remove 0; insert 1; retire 1; remove 1`. Its endpoint registry is empty, so current-name/current-generation endpoint constraints cannot mask historical-root coupling.
- Defined the forbidden generation involution `(0,0)↔(1,3)` and a `CompletePermutedCandidate` containing the **entire** `SameOrchestrationModuloGenerated nameEq trace trace`, plus equality of that package's `generatedGenerationBijection` to the permutation. This premise includes exact external inputs, external-root occurrence coupling, the complete surviving-tree correspondence, and current endpoint renaming—not merely one conjunct.
- `completeCandidateRejected` projects `externalRootGenerationsCoupled` from the complete package; `firstExternalRootBirthMapped` forces `(0,0)` to itself; congruence with the packaged permutation forces it to `(1,3)`; the constructor clash yields `Void`.
- The committed `CompleteRemovedRootPermutationCandidate` / `historicalExternalRootPermutationRejected` at `src/DGamma/CP3StatementChecks.idr:474-502` has the same complete shape. **Round-8 MINOR weak-guard finding: FIXED.**

### 6. Deletion-boundary attack 1 — endpoint before a future close

- `SurvivingRegistration` is intentionally endpoint-relative: it proves `NoParentUnload parent rest`, where `rest` ends at the compared endpoint. Extending that trace later with `L-Unload` would reclassify the same historical birth as deleted in the longer trace.
- This does **not** admit a bad Theorem-73 pair. If one side retains the only birth and the other discards it, the retained event remains pending and `RegistrationCorrespondenceEnd` is unavailable; the full `SameOrchestrationModuloGenerated` package is rejected.
- Nor is that rejection an over-strengthening on the public theorem domain. With the same external inputs, an episode open on only one side after its support has vanished leaves that side non-quiet; if support remains at the endpoint, Lemma-70 premises require the successful quiet side to have a final Active/open episode too. A comparison literally before versus after the orchestration event that makes the episode close has different external inputs.
- **PASS.** “No later `L-Unload` within this finite trace” correctly means “the final episode is still open at this endpoint”; it does not speculate about actions after the theorem's endpoint.

### 7. Deletion-boundary attack 2 — nested deleted subtree

- A discarded child birth still advances `indexedLiveGenerations` via `advanceRegistrationIndex`; therefore a later checked `L-Begin` of that child can stamp its own `RegistrationActivation`, and a grandchild birth receives the correct immediate-parent generation rather than `Nothing`.
- If the child's episode also closes, the grandchild independently carries `DeletedClosingRegistration` from the later `L-Unload child`. Thus parent birth and grandchild birth are both excluded, regardless of deletion-order interleaving; neither enters pending lists or surviving counts.
- This mirrors Theorem 73's maximal-closing-episode induction: descendant closing episodes are deleted before the ancestor episode can satisfy Lemma 72's `NoRegisteredEpisode` hypothesis. The relation computes the same eventual surviving-tree projection without requiring the proof's operational deletion order.
- If the child has no episode, it cannot register a grandchild through the checked Definition-47 provenance discipline. The remaining “child episode still open” case is the next separate attack.
- **PASS.** Fully closing nested subtrees are excluded transitively and do not leave dangling grandchild registrations.

### 8. Deletion-boundary attack 3 — **BLOCKER: deleted birth remains vestigial at endpoint**

**Files:** `src/DGamma/CP3.idr:1996-2023,2138-2277,2347-2400,2820-2830`; paper `cordis-paper.txt:2266-2310`.  
**Probe:** `/tmp/dgamma-cp3-round9.AagB95/src/VestigialBoundaryRuntime.idr`; executable aggregate prints `True`.

- Starting from the accepted 24/18 repair, I removed only the left `ORemove 2`. The resulting checked 23/18 schedules have the same external root inputs and the same supported final tree `1,3,4`; both are quiet and failure-free. Left additionally contains child 2 as exactly the paper's Lemma-57 vestigial entry: retired, Inactive, empty table, no children. Registry cardinalities are left 4 versus right 3.
- A strengthened 27-action left variant activates child 2 before retirement, closes parent 1 **while child 2's episode is still open**, and only then leaves/unloads child 2. It also ends quiet/successful with child 2 vestigial and support `1,3,4`. Thus the issue is not confined to a never-activated child: a child episode may temporarily outlive its registering parent episode, then be deleted first in Theorem 73's maximal-episode induction.
- This is paper-legal and, indeed, is Lemma 72's stated normal situation: at the original endpoint every name in `R` is vestigial, while the deletion replay omits it. O-Remove is not part of the registration inverse and is not required.
- The repaired scanner correctly **discards the birth** of child 2 because parent 1 later `L-Unload`s. But `advanceRegistrationIndex` removes a current generation only on `ORemove`, not on retirement or parent closure. Consequently left `leftFinalGenerations` still contains `2@6` (or the corresponding shifted birth) while the delayed right trace has no current generation for raw 2.
- `CurrentEndpointRenaming` then reintroduces the round-8 overconstraint: `leftCurrentGenerationMapped` must send every last unremoved generation to a right current generation, and its inverse field makes this a bijection of current generation environments. Roots 1 and 3 are fixed, and surviving child 4 already consumes the remaining right child generation; injectivity leaves no image for the extra vestigial 2. The exact-domain `SystemEquivalentByRenaming` conclusion independently refuses the 4-versus-3 registries.
- Therefore these same-input executions cannot inhabit `SameOrchestrationModuloGenerated` and cannot cross the public Theorem-73 chain, solely because a schedule-dependent **deleted** registration was left vestigial rather than explicitly O-Removed. The 24/18 regression hid this by manually retiring **and removing** child 2 before the parent unload.
- **Severity: BLOCKER (unfaithful/over-strong theorem domain).** Surviving-tree matching must also project current endpoint coupling modulo vestigial generations proved deleted, and `ConfluenceResult` must compare final endpoints with each side's withdrawn/vestigial sets (analogous to `CanonicalEndpointRelation`), not exact renamed domains.

### 9. Deletion-boundary attack 4 — partial-deletion asymmetry

- For registration-tree matching itself, the design is symmetric: either trace may use `Discard*DeletedRegistration`, and only `Queue*`/`Match*` increments the count keyed by its exact activation stamp. Deleting E1 on the left and E2 on the right therefore leaves the first yield of each retained activation at position 0, regardless of how many other local activations closed.
- `RegistrationEventMatch` deliberately does not compare activation begin ordinals. That is faithful: after closing episodes are deleted, paper Theorem 73 compares the one surviving activation tree structurally; it does not identify that activation by its original schedule ordinal.
- Swapping the 24/18 construction's sides exercises the opposite discard direction, and the constructors are dual. No position or mapped-parent asymmetry was found.
- **PASS for the surviving-tree matcher, conditional on removed/bijected endpoint artifacts.** In the general paper case where E1/E2 leave unequal vestigial names, the new BLOCKER in item 8 still prevents the full package; partial deletion does not create a separate position bug.

### 10. Deletion-boundary attack 5 — recovery-path versus normal close

- Paper Definition 53 defines episode closure semantically as installed→not-installed, and Lemma 54(4) proves this occurs exactly at `L-Unload`. `L-Leave`, `L-Divert`, and `L-Raise` merely choose the path into `Unloading`; the accumulator executes at the later `L-Unload` in every case.
- The repair checks the actual later `LUnload parent` action. It therefore classifies normal leave/unload, diversion recovery, and raise recovery uniformly, as Lemma 72 does. Looking only for `L-Divert` or only for an explicit recovery tag would have been wrong; the implementation does neither.
- Checked transitions prevent an `L-Unload` from occurring outside an installed activation, and raw-name reuse cannot create a false positive without the original activation first unloading (O-Remove requires Inactive). The activation stamp supplies the opening boundary; the first subsequent unload of that raw live parent is its close.
- **PASS.** “No later L-Unload” distinguishes surviving versus closing episodes faithfully across all recovery paths.

### 11. Over-permissiveness hunt — can deletion disguise a different surviving tree?

- Every retained birth is consumed exactly once before `RegistrationCorrespondenceEnd`; every match fixes exact component, child generation, mapped immediate-parent generation, and activation-local position. The single global generation bijection is injective and also anchors every historical external root occurrence, so a surviving child cannot be mapped to a root or reassigned across root subtrees.
- Within one surviving activation, all births have the same no-later-unload status. Selectively declaring an earlier sibling deleted while retaining a later sibling is impossible; hence positions preserve the actual iterator order of the complete surviving activation, not a deletable subsequence chosen by the witness.
- A later raw-name `L-Unload` cannot be borrowed from an unrelated reuse episode: checked O-Remove/reuse requires the birth's currently stamped activation to unload first. Conversely, no matching path can declare a birth surviving if any same-parent unload remains in its suffix.
- An isolated relation could syntactically retain descendants of a discarded parent birth if that child episode stayed open, but the full theorem's registration-retirement provenance plus quiet/success premises force such a retired child to close; its descendants are then discarded too. This does not yield a full-premise bad acceptance.
- **PASS (no false admission found).** The repair still strongly distinguishes genuinely different surviving-tree component/order/parent structure. The discovered defect is the opposite: it refuses valid traces with unmatched vestigial deleted entries.

### 12. Requested prior-witness spot checks

**Probe:** `/tmp/dgamma-cp3-round9.AagB95/src/PriorSpotProbe.idr`; runtime output `[True, True, True, True, True, True]`.

- **Cross-parent permutation:** both runtime and full-correspondence checks remain `True`. Source inspection confirms the concrete relation still maps child generations `(2,4)→(2,5)` and `(3,5)→(3,4)` under their respective fixed parent generations; `crossParentPermutationTheorem73PremiseChain` still takes the literal public alias and all premises.
- **1-vs-2 fresh choice:** `freshChoiceCorrespondenceCheck=True`; the generated bijection still maps only the historical ordinal-2 births `1↔2`, leaves the later live root generation fixed, and its public theorem-chain wrapper remains exact.
- **Nine-action role-changing/self-canonical trace:** runtime, canonical replay, and proof-indexed trace values are all `True`. `roleChangingFullCanonicalScheduleStatementCheck` still packages every public canonical field, fixes raw endpoint withdrawals to `[]`, and fixes historical withdrawals to `[(1,2)]`; no round-9 index change regressed generation-stamped raw-role reuse.
- **Positive parent registration:** the independent proof projects `sourceBelongsToProgram` from the concrete exported `positiveParentRegistrationYield`; applying `emptyParentCannotRegisterGuard` to that same witness still makes a hypothetical empty parent program yield `Void`. The premise is substantive, not vacuous.
- **Identity deletion:** `/tmp/.../IdentityDeletionExpectedFailure.idr` is rejected exactly at `KeepAction`'s fifth argument: equality `?x=?x` cannot inhabit `Not (deletable action)` when every action is deletable. The mandatory deletion barrier remains structural.
- **PASS** for all requested historical spots.

### 13. Faithfulness adjudication of `retain iff no later L-Unload`

- For an event with `eventParentActivation = Just activation`, checked LTS states make `L-Begin` the unique opening and `L-Unload` the unique close. Hence a later `LUnload parent` exists iff that activation is a closing episode before the finite endpoint; absence means the final episode remains open. Raw-name reuse cannot break this equivalence because reuse requires the old activation to unload/remove first.
- Lemma 72 cannot delete every closing episode in an arbitrary order, but Theorem 73's maximal-closing induction eventually deletes **all** of them. Classifying all their births up front is therefore a faithful projection of the induction's final surviving registration tree, provided descendant closing episodes satisfy the public discipline/quiet hypotheses.
- The classifier correctly treats normal, diverted, and raised episodes alike and resets iterator position on each `L-Begin`. I find no classifier-level false deletion or false retention.
- **Classifier verdict: PASS. Overall Theorem-73 faithfulness: FAIL** because the subsequent current-endpoint and final-equivalence records do not quotient vestigial entries belonging to those correctly classified deleted births (item 8).

### 14. README/NOTES truthfulness audit

- Read `README.md` and all 869 lines of `NOTES.md` fully.
- **Status/debt labels otherwise PASS.** Theorem 73 is “submitted for round-9 review,” not called proved; constructive Lemma-72 replay, canonical sorting, general endpoint assembly, temporal induction, Progress ranking, and the eleven statement-only declarations remain listed. Section 3/CP2 status is consistent with accepted prior audits.
- **Surviving-tree description is locally accurate.** Docs correctly say activation stamps start at `L-Begin`, counts reset, discarded births need later `L-Unload`, and only retained births enter pending matching. They accurately describe the 24/18 actions, complete public chain, and upgraded complete removed-root candidate.
- **Three requested paper issues are preserved:** Lemma-68/O-Insert provenance, Lemma-72 selected-retirement proof-intent ambiguity, and Lemma-56 raw-name reuse ambiguity. Definition-32 and observer/partiality issues are also retained.
- **Over-approximation disclosure PASS.** README Definition 47 and NOTES explicitly state that the explicit host may license several fresh child names from one live tagged source head and explain why ranks/retirement preserve the limited support argument; it is not presented as literal one-yield semantics.
- **Documentation defect consequent on item 8 — `README.md` Theorem-73 row; `NOTES.md:628-735,806-869`: MAJOR.** The docs say discarded births “neither match nor consume positions” and present current endpoint names as an independent final step, but do not disclose that every unremoved discarded/vestigial birth is still forced through `CurrentEndpointRenaming` and exact `SystemEquivalentByRenaming`. The hardened regression's explicit early O-Remove masks this restriction. Status says the round-8 closing-episode defect has a complete regression and directs Next immediately to proof work, omitting a remaining proposition-shape blocker.
- The docs are cautious about acceptance, but the concrete semantic/debt description is incomplete and therefore not final-review truthful until vestigial endpoint quotienting is repaired or explicitly declared as a restriction.

### 15. Escape-hatch, hole, totality, and hygiene scans

- All **12/12** packaged `src/DGamma/*.idr` modules contain exactly one `%default total`.
- Anchored scans find zero `believe_me`, `assert_total`, postulate, `%unsafe`, `%foreign`, unsafe IO escape, `%default partial`/`covering`, partial/covering declaration, or named metavariable hole.
- Exactly **11** `TODO(proof)` comments remain: 3 in `Unified`, 3 in `Metatheory`, and 5 in `CP3`. They correspond to the documented statement-only theorem list; none is an accepted inhabitant.
- `git diff --check` passes. No staged or tracked changes exist; repository status remains only the pre-existing untracked `paper/`. Every probe and this authoritative report are outside the repository.
- **PASS.** No hidden proof/totality debt or review contamination found.

### 16. Runtime aggregates

- In a fresh archive, a review-only runner evaluated the eleven individual `DGamma.CalculusChecks` values plus `allRuleChecks`, the nine individual CP3 values plus `allCP3StatementChecks`.
- Output is **22 values, all `True`**:
  `[True, True, True, True, True, True, True, True, True, True, True, True, True, True, True, True, True, True, True, True, True, True]`.
- **PASS.** Committed runtime and correspondence assemblies execute at `c5ab667`; note that the runtime aggregate does not include the new vestigial endpoint attack.

### 17. Genuinely clean archive build

- Created a second untouched `git archive c5ab667` at `/tmp/dgamma-cp3-round9-build.UOyn0L`, with no probes or inherited TTC cache.
- Ran `idris2 --clean dgamma.ipkg && idris2 --build dgamma.ipkg` under Idris 2 0.8.0.
- **PASS: all 12/12 package modules rebuilt successfully.**

### 18. Typed eliminator for the vestigial-current blocker

**Probe:** `/tmp/dgamma-cp3-round9.AagB95/src/VestigialCurrentCouplingProbe.idr`; typechecks.

- Modeled the exact final generation environments of the 23/18 attack: left current names `{1,2,3,4}`, right `{1,3,4}`. The candidate carries a global `NameBijection`, fixed-point equations for live roots 1 and 3, and the forward current-generation obligations for left names 2 and 4—precisely the relevant `CurrentEndpointRenaming` fields.
- `targetIsOneThreeOrFour` proves any successful lookup in the right environment targets only 1, 3, or 4. Bijection injectivity plus fixed roots excludes 1 and 3 for either non-root source, so both left 2 and left 4 must map to right raw 4. `vestigialCurrentCandidateRejected` derives `2=4` by applying the recorded inverse law and eliminates it.
- This mechanically confirms the BLOCKER is not speculative and cannot be evaded by mapping vestigial raw 2 to another global Nat name. The exact current-generation coupling is impossible before the theorem result is reached.

## Round-8 finding disposition

| Round-8 finding | Round-9 disposition |
|---|---|
| **BLOCKER:** lifetime-global per-parent positions ignored activation boundaries | **FIXED.** Independent 24/18 reconstruction stamps each `L-Begin`, excludes the closed activation's birth, gives both retained births position 0, constructs the complete public same-input package, and crosses the literal theorem chain. |
| **BLOCKER:** every historical birth had to biject before canonical deletion | **FIXED in `RegistrationTraceCorrespondence`, but not end-to-end.** Closed-episode births can now be discarded and do not match/count. **Reopened downstream:** an unremoved discarded birth remains in `indexedLiveGenerations` and must still biject in `CurrentEndpointRenaming`; the paper-legal vestigial case remains excluded. |
| **MINOR:** removed-root negative guard was not a complete candidate | **FIXED.** Both committed and independent eliminators assume the full concrete `SameOrchestrationModuloGenerated` package and derive `Void` at exact root-occurrence coupling. |
| Round-8 documentation omitted both blockers | **Updated accurately for activation-local/surviving-tree matching, but incomplete for the new vestigial endpoint remnant.** |

## Whole-project final debt summary

### Honest declared/pre-approved proof or representation debt

- Definition 32 remains an explicit finite approximation; Lemma 38 is only the proved relational core. Lemma 35 and Theorems 40/42 remain statement-only.
- Section 4 retains disclosed finite static continuations, tagged/catalogued explicit registration (including one-head/many-name over-approximation), trace-anchored generated monoids, exact effect equality, and explicit dictionary alignment.
- Lemmas 54–57 are not fully packaged. Theorem 61/Corollary 62 and Theorem 64's recovery branch still need the temporal accumulator induction.
- Progress/Theorem 66 still needs unloading-chain no-deadlock and Equation-61 ranking. Lemma 71 lacks control applicability frames. Lemma 72 lacks checked deletion induction. Theorem 73 lacks constructive deletion, sorting, and general endpoint assembly.
- Exactly eleven statement-only `TODO(proof)` declarations remain, with no postulate or accepted hole. These declared debts are not the reason for rejection.

### New blocking proposition/fidelity debt

1. Project `CurrentEndpointRenaming` modulo generations classified by `DeletedClosingRegistration`; retirement/vestigiality, not only O-Remove, must be allowed to withdraw a deleted registration from cross-trace endpoint coupling.
2. Replace `ConfluenceResult.finalEndpointsEquivalent : SystemEquivalentByRenaming ... leftFinal rightFinal` with a relation carrying left/right withdrawn vestigial sets and comparing effects plus controls outside them, analogous to `CanonicalEndpointRelation`. Exact renamed-domain equivalence may remain as a proved special case.
3. Add a checked regression that **does not O-Remove** the deleted child; preferably activate it, close the parent first, then close the child, and verify quiet/success with the vestigial entry. The current 24/18 regression's early O-Remove is too strong to cover paper Lemma 72.
4. Update README/NOTES Status/Next and record a likely paper clarification: Lemma 57 gives `γ≈γ\n` for vestigial `n`, Lemma 72 gives `≃` only outside `R`, yet literal Theorem 73(2) says final states are related by both `≃` and `≈`. With schedule-dependent vestigial `R`, the `≃` domain clause needs an implicit “outside withdrawn names” qualification or the paper statement itself is false.

## Final findings

1. **BLOCKER — `src/DGamma/CP3.idr:1991-2023,2353-2417`:** discarded closing-episode births are removed from tree matching but remain “current” until O-Remove. `CurrentEndpointRenaming` requires every such unremoved generation to biject. Checked quiet/successful 23/18 and 27/18 same-input schedules with the same supported final tree but one left vestigial child are refused. A total typed cardinality eliminator proves no endpoint name bijection can satisfy the fields.
2. **BLOCKER — `src/DGamma/CP3.idr:2811-2830`:** `ConfluenceResult.finalEndpointsEquivalent` requires exact registry domains up to a raw-name bijection. It cannot state paper Lemma-72/Theorem-73 equivalence when either original endpoint contains a schedule-dependent vestigial deleted registration. Loosening only the premise would make the conclusion false.
3. **MAJOR regression gap — `src/DGamma/CP3StatementChecks.idr:1943-1948,2007-2034,3109-3178`:** the hardened pair explicitly O-Retires **and O-Removes** child 2 before parent unload. It thoroughly verifies activation reset/deleted-history matching but masks the paper-normal vestigial endpoint case.
4. **MAJOR documentation consequence — `README.md:128`; `NOTES.md:633-714,807-869`:** surviving-tree and current-endpoint descriptions omit that deleted-but-unremoved generations still have to biject; the debt/Next list incorrectly has no remaining proposition-shape work.
5. **VERIFIED FIX:** independent 24/18 reconstruction has old history rank 1-vs-0, new retained positions 0-vs-0, full same-input package, both quiet/successful supported endpoints, and exact public Theorem-73 premise chain.
6. **VERIFIED FIX:** complete removed-root candidate rejection derives `Void` from exact historical-root occurrence coupling, not endpoint constraints or a projection-only strawman.
7. **VERIFIED:** endpoint-before-close classification, fully nested deletion, partial-deletion position symmetry, and recovery/normal-unload classification introduce no separate defect; no pair with genuinely different surviving-tree structure was admitted.
8. **VERIFIED:** cross-parent, 1-vs-2, nine-action role-change, positive yielded source, empty-parent rejection, and identity-deletion barrier remain substantive; 22/22 runtime values are `True`; clean build 12/12; totality/escape-hatch scans pass.

# Final verdict: REJECT

The two round-8 core matching repairs are real and well tested, but project review cannot close. The public Theorem-73 boundary still refuses the paper's ordinary vestigial result of deleting a closing episode unless that child is additionally O-Removed, and its result type cannot express unequal withdrawn vestigial sets.

FINAL VERDICT: REJECT