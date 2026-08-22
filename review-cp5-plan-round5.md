# Theorem 73 Scoping Plan — Adversarial Review, Round 5

**Reviewed branch:** `cp5-thm73-scoping`  
**Reviewed commit:** `be29a1816261443e8e05465e2fd305d79ae1331a`  
**Immutable production baseline:** `34b21c9`  
**Prior reviewed revision:** `e3d8bd485f43d69ee46eb6aa9b925612b4c6fcb8`  
**Method:** all Idris probes run serially from an exact source copy under `/tmp/thm73-review5-probes/`; the repository is read-only except this report.

## Probe log (appended contemporaneously)

### Probe R5-00 — branch identity and initial worktree state

- **Command:** `git -C /Users/vyacheslavshebanov/Work/dgamma status --short --branch; git ... rev-parse HEAD; git ... branch --show-current; git ... ls-files 'review-cp5-plan-round*.md'`
- **Result:** branch is `cp5-thm73-scoping` at exact target `be29a18`. No staged/tracked modification is reported. Pre-existing untracked `paper/` remains; this mandated round-5 report did not exist before review.
- **Classification:** **note** — tracked/index baseline is clean; literal status is not empty because of pre-existing `paper/` and now this mandated report.

### Probe R5-01 — prior reports reconstructed

- **Command:** read `review-cp5-plan-round1.md` through `review-cp5-plan-round4.md` in full.
- **Result:** reconstructed the historical consumer inventory and the narrowing failure front. Round 4's decisive checked facts are: endpoint-membership-guarded full `SupportPath` transport is false with an unsupported withdrawn intermediary; exact inverse-right linearization can be false; scanner classification core is adequate; permuted bridge/replay coupling and complete O21 wrapper resisted tested detachments; exactly 25 research holes; release 207/207; immutable target blob `2c697e...`.
- **Classification:** **note** — round-5 attacks will re-derive rather than trust these claims.

### Probe R5-02 — production immutability and revision-5 change surface

- **Command:** `git diff --exit-code 34b21c9..be29a18 -- src dgamma.ipkg; git diff --stat/name-status e3d8bd4..be29a18; git log --oneline e3d8bd4..be29a18; git rev-parse be29a18:src/DGamma/CP3.idr; git diff --cached --name-only`
- **Result:** required production diff is empty. `CP3.idr` blob is exactly immutable `2c697e532e83989de8591fa6a4378747c6a501c0`. Revision 5 modifies only the plan, cross-trace spike, renaming/scanner spike, and adds the prior report; no staged files.
- **Classification:** **note** — the claimed O19/O20 and scanner changes are isolated to research/plan, as required.

### Probe R5-03 — actual redesign declarations and plan inspected

- **Command:** inspect full revision diff for `CP5ConfluenceCrossTraceSpike.idr` and `CP5ConfluenceRenamingCompositionSpike.idr`; line-number-read `THM73-PLAN.md`.
- **Result:** actual types remove all mapped path/comparability/left-linearization fields. O19 exports membership maps, mapped distinctness, and a pure adjacent actor permutation. O20 introduces exact block decomposition, one-step operational block replay, recursive operational actor replay, a deliberately noncanonical execution, and a replayed-left→right bridge. O21 now composes original schedule scanner capital with source→operational replay/endpoint and the target-indexed bridge. Scanner side/interleaving and same-name regression records are new complete definitions. Plan revision 5 documents 23 obligations and raw 70–124.
- **Classification:** **note** — this is declaration inventory only; producer sufficiency and theorem truth remain to be attacked.

### Probe R5-04 — immutable external probe trees

- **Command:** archive exact `be29a18` to `/tmp/thm73-review5-probes/release`; copy its 207 production Idris files plus exactly five research spikes to `/tmp/thm73-review5-probes/spikes/src`; hash both `CP3.idr` copies; check active Idris processes.
- **Result:** release tree has 207 Idris modules; spike tree 212. Both `CP3.idr` files hash to immutable blob `2c697e532e83989de8591fa6a4378747c6a501c0`. Exactly five research spikes were copied and no Idris process was active.
- **Classification:** **note** — all type probes below are external and serial.

### Probe R5-05 — local-diamond spike elaboration

- **Command:** `cd /tmp/thm73-review5-probes/spikes && rm -rf build && idris2 --source-dir src --check src/DGamma/CP5ConfluenceLocalDiamondSpike.idr`
- **Result:** passed 31/31 modules under Idris 2, exit 0. A/A, A/O, O/A, O/O and suffix/bundle interfaces remain API-valid.
- **Classification:** **note** — hard bodies remain research holes.

### Probe R5-06 — deletion-chain elaboration, invocation 1

- **Command:** `idris2 --source-dir src --check src/DGamma/CP5ConfluenceDeletionChainSpike.idr` (serial, 1800-second limit).
- **Result:** infrastructure failure: Idris was killed by signal 9 at module 94/165, exit 137, after warnings only and before target elaboration.
- **Classification:** **note** — inconclusive, not a type error. Verify cleanup and retry using the retained exact-source cache.

### Probe R5-07 — killed-process cleanup and cache state

- **Command:** `pgrep -fl '[i]dris2' || true; find .../build -name '*.ttc' | wc -l; tail deletion log`.
- **Result:** no Idris process survived. Exact-source cache contains 109 TTC files; log confirms only the kill at module 94, no Idris diagnostic.
- **Classification:** **note** — serialization preserved; retry is safe.

### Probe R5-08 — deletion-chain spike elaboration, invocation 2

- **Command:** retry the exact serial deletion-chain check with retained cache.
- **Result:** passed 165/165 modules, exit 0; diagnostics only established shadowing warnings.
- **Classification:** **note** — dependent deletion history and scanner-discard theorem interfaces elaborate.

### Probe R5-09 — canonical-sort spike elaboration

- **Command:** serial check of `CP5ConfluenceCanonicalSortSpike.idr` against exact copied sources.
- **Result:** passed 166/166 modules, exit 0. Simultaneous enriched schedule construction remains type-correct.
- **Classification:** **note**.

### Probe R5-10 — renaming/scanner/replayed-bridge spike elaboration

- **Command:** serial check of `CP5ConfluenceRenamingCompositionSpike.idr`.
- **Result:** passed 167/167 modules, exit 0. `ReplayedCanonicalEndpointBridge`, complete scanner-capital constructor, scanner sequence/regression, and the corrected O21 hole signature elaborate.
- **Classification:** **note** — named scanner inductions and O21 body remain unproved by design.

### Probe R5-11 — cross-trace operational replay spike elaboration

- **Command:** serial check of `CP5ConfluenceCrossTraceSpike.idr`.
- **Result:** passed 168/168 modules, exit 0. New pure and operational permutation families, four-fiber indexed regression, noncanonical execution/result, complete O21 wrapper, and outer assembly are API/index-valid.
- **Classification:** **note** — this does not prove the O20 hole is inhabitable.

### Probe R5-12 — local-consumer inventory reconstructed from types

- **Command:** inspect `TraceIndependent`, `LocalRelationalDiamond`, `OrchestrationSwapSafety`, all four diamond signatures, `AdjacentSwapResult`, `OperationalAdjacentBlockSwap`, and all occurrences of the new operational families.
- **Result:** historical capital is present upstream: full replay bundle includes independence/discipline; local cases require exact checked transitions, actor distinctness, early applicability for A/A and O/A, child/licensing-parent exclusions for mixed swaps, and generation/registration safety for O/O; suffix replay returns exact trace, correspondence, endpoint, external inputs, and next bundle. However, there is **no separately stated producer theorem** from one `AdjacentActorOrderSwap + sourceBlocks + sourcePremises` to `OperationalAdjacentBlockSwap`. The record itself carries only its outputs and no derivation/certificate linking those outputs to A/A, A/O, O/A, O/O transition swaps; all applicability/safety reconstruction is hidden inside the single `canonicalSchedulesConvergeSpike` hole.
- **Classification:** **major attack hypothesis** — O20 may be under-scoped or false for arbitrary pure permutation steps; concrete intermediate-state and licensing mutations follow.

### Probe R5-13 — arbitrary-certificate injection, invocation 1

- **Command:** check external `R5CertificatePollution.idr`, which prepends an arbitrary actor swap and its inverse to O19's certificate, rebuilds the public mapped record, calls O20, and extracts the forced first operational block swap.
- **Result:** probe stopped before dependent index checking because `SystemState` was not re-exported through the spike import; cascading “no declaration” errors followed.
- **Classification:** **note** — probe import defect. Add direct `DGamma.Calculus` and rerun.

### Probe R5-14 — arbitrary-certificate injection, invocation 2

- **Command:** rerun after direct calculus import.
- **Result:** all types elaborated; body reached only quantity discipline: erased `canonicalSchedulesConvergeSpike` cannot be called from an unrestricted helper.
- **Classification:** **note** — mark the orchestration helper quantity 0, matching the theorem, and rerun.

### Probe R5-15 — arbitrary-certificate injection, invocation 3

- **Command:** rerun quantity-correct helper.
- **Result:** call reached the intended exact operational certificate, but an opaque cross-function `replaceMappedCertificate` hid the definitional equality between its stored certificate and the prepended `ActorPermutationStep`; first-step extraction could not reduce it.
- **Classification:** **note** — construct `MkMappedCanonicalSupportOrders` transparently inside the helper and rerun.

### Probe R5-16 — arbitrary-certificate injection, invocation 4

- **Command:** rerun with transparent constructor in a `let`.
- **Result:** Idris still kept the local mapped record projection opaque at the dependent theorem result, so exact first-constructor reduction failed; no safety premise failed.
- **Classification:** **note** — pattern-match the input mapped record and construct/call in a branch so the stored certificate reduces definitionally.

### Probe R5-17 — arbitrary-certificate injection, invocation 5

- **Command:** rerun after pattern-matching the input mapped record.
- **Result:** dependent projection of the local polluted record remains opaque across the O20 result; first-step extraction still cannot reduce it. This is elaboration opacity, not a rejection of certificate pollution.
- **Classification:** **note** — expose the exact stored-certificate equality in a dependent producer result, then rewrite the operational replay before extraction.

### Probe R5-18 — arbitrary-certificate injection, invocation 6

- **Command:** check dependent result exposing polluted certificate equality.
- **Result:** the local sigma witness was still a `let`-bound record, so `Refl` could not reduce its projection; downstream rewrite therefore also remained inconclusive.
- **Classification:** **note** — inline the record constructor in both sigma witness and O20 call; fix rewrite orientation after equality elaborates.

### Probe R5-19 — arbitrary-certificate injection, invocation 7

- **Command:** inline polluted mapped constructor and check.
- **Result:** dependent polluted producer now elaborates through the exact call to `canonicalSchedulesConvergeSpike`; only the optional final convenience rewrite/extractor remained opaque. Thus O20's public theorem demonstrably accepts an O19 record whose certificate is prefixed by **any** caller-supplied adjacent swap and its inverse, while retaining every membership/distinctness field and final actor target.
- **Classification:** **major** — `canonicalSchedulesConvergeSpike` is universal over publicly constructible `MappedCanonicalSupportOrders`, so O20 must operationalize arbitrary redundant/malicious swap steps, not merely a carefully chosen safe list permutation. Remove the convenience extractor and retain the successful dependent convergence producer as the checked regression.

### Probe R5-20 — arbitrary-certificate injection, conclusive producer

- **Command:** check reduced `R5CertificatePollution.idr` containing complete `polluteCertificate`, mapped-record reconstruction, operational first-step eliminator, and dependent `pollutedMappedConvergence`.
- **Result:** passed 169/169 modules. A caller may prepend any reversible adjacent actor swap loop to O19's certificate and O20 is still required by its current type to return a convergence result indexed by exactly that polluted certificate.
- **Classification:** **major**, potentially blocker when combined with a checked unsafe parent/child swap. The intended “O19 producer chooses safe swaps” argument is not enforced because O20 accepts arbitrary public mapped records.

### Probe R5-21 — four-fiber revision-5 positive model, invocation 1

- **Command:** adapt/re-derive the round-4 four-fiber state model in external `R5FourFiberPositive.idr`; retain real `Lower→Middle→Upper`, accepted withdrawal, refuted inverse-right linearization, and construct the replacement two-swap pure actor certificate.
- **Result:** all model/certificate declarations elaborated; only final aggregate helper violated quantity discipline by using erased path/endpoint proofs in an unrestricted body.
- **Classification:** **note** — mark aggregate helper quantity 0 and rerun.

### Probe R5-22 — four-fiber revision-5 positive model passes

- **Command:** quantity-correct serial check of `R5FourFiberPositive.idr`.
- **Result:** passed 169/169. The checked static model simultaneously carries the genuine original path, accepted `CanonicalEndpointRelation` withdrawal, proof that the inverse-right order cannot linearize the left path, and a replacement `CertifiedActorPermutation` to that exact actor target.
- **Classification:** **note** — option (b) removes the round-4 *field contradiction* at the static actor-list boundary.

### Probe R5-23 — wrong-trace bridge detachment

- **Command:** expected-failure check `R5WrongTraceBridgeNegative.idr`, retyping `convergenceBridge` to an arbitrary trace/final.
- **Result:** rejected for the intended dependent index: Idris cannot unify `permutedLeftFinal (permutedLeftExecution convergence)` with `otherFinal`.
- **Classification:** **note** — bridge remains tied to the exact noncanonical operational trace.

### Probe R5-24 — stale endpoint quotient detachment

- **Command:** expected-failure `R5StaleQuotientNegative.idr`, using one execution's composed endpoint at a second execution's target.
- **Result:** rejected: hidden target states remain value-dependent (`first.permutedLeftFinal` versus `second.permutedLeftFinal`).
- **Classification:** **note** — aggregate quotient cannot be substituted across executions.

### Probe R5-25 — mixed schedule substitution

- **Command:** expected-failure `R5MixedScheduleNegative.idr`, feeding a convergence indexed by `leftCapital` to O21 with another `otherLeft` capital.
- **Result:** rejected on exact record-value index (`leftCapital` versus `otherLeft`).
- **Classification:** **note** — original O21 composition cannot mix canonical schedules.

### Probe R5-26 — complete published-boundary pipeline

- **Command:** check external `R5FullPipeline.idr`: per side delete-all → shape/order/sort → minimal support/accounting → enriched canonical capital; then O19 → O20 noncanonical execution/bridge → scanner/O21 → outer constructor.
- **Result:** passed 169/169. The final `ConfluenceResult` uses `canonicalSchedule leftCapital` and `canonicalSchedule rightCapital`, not the noncanonical intermediary. No bridge/scanner premise is accepted externally.
- **Classification:** **note** — public-result schedule retention is correct at the boundary. All four local transposition bodies and the new operational expansion remain hidden inside named holes; this wrapper cannot validate their applicability.

### Probe R5-27 — exact concrete scanner ordinal projections

- **Command:** check `R5ScannerOrdinalPositive.idr`, specializing the regression to same raw name at left births 6/18 and right births 9/14 and projecting all four final deleted memberships.
- **Result:** passed 168/168. The record's outputs are indexed by full `RegistrationGeneration`, not raw name alone.
- **Classification:** **note** — positive output typing distinguishes the four requested ordinals, conditional on a regression value.

### Probe R5-28 — wrong-generation conflation rejected

- **Command:** expected-failure `R5ScannerWrongGenerationNegative.idr`, using the exact later `(raw,18)` membership where `(raw,6)` is required.
- **Result:** rejected on the birth-ordinal component despite identical raw names.
- **Classification:** **note** — the regression output cannot conflate same-name generations.

### Probe R5-29 — hole/escape/reachability inventory

- **Command:** enumerate named-hole identifiers; scan production/research for `believe_me`, `assert_total`, `%default partial`, declaration-form postulates; scan production/ipkg for research reachability.
- **Result:** exactly **25 unique named research holes**: canonical 6, cross-trace 2, deletion 7, local 8, renaming 2. No forbidden production escape, no non-hole research escape, and no research reachability from `src/`/`dgamma.ipkg`. A simple `DGamma.*` line count reported 206 and excludes the package's nonmatching entry; the authoritative package build will verify 207.
- **Classification:** **note** — plan's hole count is reconciled.

### Probe R5-30 — exact external release package build

- **Command:** seed `/tmp/.../release/build` with byte-identical production TTC cache from the serial spike checks, then run `idris2 --build dgamma.ipkg` in the exact archived release tree.
- **Result:** passed through **207/207** package modules, exit 0. Research/external probes were not package modules.
- **Classification:** **note** — release buildability and research isolation pass.

### Probe R5-31 — estimate arithmetic

- **Command:** independently sum phase rows and enumerate upper bounds for overlap deductions 0,1,2,3,4.
- **Result:** raw rows are exactly 70–124. An overlap of 0–4 makes the upper bound range from 124 down to 120; the conservative envelope is **70–124**, not 70–120. The advertised 120 assumes the maximum four-shift overlap, contradicting “0–4”.
- **Classification:** **minor/major planning defect** — either commit to and justify exactly four upper-end shifts of overlap, or advertise 70–124. This is independent of the operational-certificate gap.

### Probe R5-32 — scanner regression/interleaving attack

- **Command:** grep all research/plan references and concrete ordinal terms; inspect `scannerSideSequence`/regression body; check `R5WeakInterleaving.idr` against the exact `BeforeIn` predicate.
- **Result:** no concrete 6/18/9/14 fixture exists in the branch artifacts. `scannerSideSequence` records only side, conflating skip, discard, queue, and match constructors. `sameRawNameScannerRegression` stores a global interleaving proof but does not tie any of the four target generations to the interleaved positions. The checked witness shows the exact predicate accepts `[L,R,L,L,L,R,R]`: an unrelated alternating prefix may be followed by all hypothetical target left deletions and then all right deletions.
- **Classification:** **major** — exact ordinal output typing is good, but the claimed *interleaved same-name deletion* regression is weaker than advertised and no concrete scanner/index-update fixture is retained. Enrich the observable sequence with constructor kind and exact discarded generation (or supply the actual concrete correspondence regression), then reorder target discard steps and prove exact final lists.

### Probe R5-33 — moved unsupported intermediary mutation

- **Command:** extend `R5FourFiberPositive.idr` with registry order `[Lower, Alternate, Middle, Upper]`, re-prove the exact two-edge path and middle unsupportedness, and reuse the exact replacement actor target.
- **Result:** passed 169/169. Moving the omitted intermediary's registry position does not reintroduce a pure O19 contradiction.
- **Classification:** **note/non-finding** — expected under option (b); actor certificates do not inspect registry positions.

### Probe R5-34 — two-intermediary mutation, invocation 1

- **Command:** first check of external five-fiber/two-unsupported-intermediate model.
- **Result:** probe construction issues before the intended mutation: unconstrained numeric literals in `Bind`/actor-swap constructors inferred `Integer`, upper dependency view was incomplete, and a removed-endpoint generation helper was not coverage-complete. These caused cascading lookup failures.
- **Classification:** **note** — annotate `Nat`, provide the upper view, and narrow this mutation to the requested path/absence/pure-target test rather than duplicating the already checked accepted-withdrawal proof.

### Probe R5-35 — two-intermediary mutation, invocation 2

- **Command:** rerun after initial `Nat` annotations/narrowing.
- **Result:** remaining failures are still probe-literal inference: uniqueness proof signatures and actor-list indices themselves were inferred as `Integer`, poisoning context/list lookups. No path/actor relation has failed.
- **Classification:** **note** — explicitly annotate every numeric list type as `List Nat` and rerun.

### Probe R5-36 — two unsupported intermediaries pass

- **Command:** final serial check of `R5TwoIntermediatePositive.idr` with five fibers: active supported endpoints, two retired/inactive/empty intermediates omitted on the right, exact three-edge path, and the same two-step pure actor target.
- **Result:** passed 169/169. Both intermediates are definitionally unsupported/absent; the path and pure target coexist.
- **Classification:** **note/non-finding** — multiple omitted intermediates do not break O19 option (b). This remains a static producer-shape test, not an operational O20 proof.

### Probe R5-37 — withdrawn licensing-parent mutation, invocation 1

- **Command:** mutate the four-fiber model so `Upper` is `ChildOf Middle`, retain accepted withdrawal/path/pure target, and test endpoint well-formedness.
- **Result:** all path, accepted `CanonicalEndpointRelation`, and actor-target fields elaborated. Direct reduction of the composite `registryWellFormed` Bool did not normalize to `False`, leaving only the proposed non-WF witness unresolved.
- **Classification:** **note** — use the proved `wellFormedAbsentHasNoChild` production lemma plus the concrete child pointer to refute `registryWellFormed = True` propositionally.

### Probe R5-38 — withdrawn licensing-parent mutation disposition

- **Command:** final check after deriving non-well-formedness from `wellFormedAbsentHasNoChild` and concrete `hasChild`.
- **Result:** passed 169/169. The immutable `CanonicalEndpointRelation` alone admits withdrawing `Middle` while a retained `Upper` still has `ChildOf Middle`; path and pure actor target coexist. But production `ReplayInvariantBundle` cannot admit the right endpoint: `registryWellFormed = True` leads to `Void` because an absent raw parent still has a child.
- **Classification:** **note/non-finding for the real pipeline** — this mutation is correctly excluded by the full recursive bundle, not by O19. It also confirms the generic indexed regression's `IndependentCanonicalSchedule` premise matters; endpoint-only fixtures are insufficient.

### Probe R5-39 — exact recursive operational threading

- **Command:** check `R5OperationalThreadingPositive.idr`, constructing a one-step `OperationalActorPermutation` whose terminal trace/blocks/bundle are exactly the preceding `OperationalAdjacentBlockSwap` outputs.
- **Result:** passed 169/169. The recursive family itself enforces exact next trace, block decomposition, and full bundle.
- **Classification:** **note/positive** — round-5 fixes recursive threading. The unresolved issue is producing each `OperationalAdjacentBlockSwap` from local diamonds/safety for the selected certificate, not passing its outputs onward.

### Probe R5-40 — concrete parent/child certificate pollution, invocation 1

- **Command:** extend the pollution probe with concrete `[parent,child] → [child,parent] → [parent,child]` pure certificate.
- **Result:** forward swap elaborated; the inline reverse distinctness proof was malformed and failed before testing the certificate.
- **Classification:** **note** — provide a direct `Not (1 = 0)` lemma and rerun.

### Probe R5-41 — concrete parent/child pure loop passes

- **Command:** final check after direct reverse distinctness lemma.
- **Result:** passed 169/169. `CertifiedActorPermutation Nat [0,1] [0,1]` accepts a parent/child swap-and-return loop because its only local condition is `0 ≠ 1`; it carries none of O/A's generated-child or licensing-parent exclusions.
- **Classification:** **blocker evidence when combined with R5-20** — arbitrary public mapped certificates flow into O20, and a concrete certificate form can demand the exact class of swap whose local diamond intentionally rejects licensing dependence. O20 must not quantify over arbitrary public pure certificates.

### Probe R5-42 — exact O/A licensing-safety contradiction

- **Command:** check `R5ParentChildSafetyContradiction.idr`, deriving `Void` from the exact O/A insertion-exclusion premise when `OInsert child (ChildOf parent)` is immediately followed by `LBegin child`.
- **Result:** passed 32/32. The checked theorem uses the actual `Transition` action indices and proves the local O/A side condition is impossible for the parent/child block boundary.
- **Classification:** **blocker** with R5-20/R5-41. The new pure certificate permits this parent/child actor swap loop; O20 universally accepts caller-polluted mapped records; but the advertised A/O/O/A/A/A/O/O realization cannot supply its own exact O/A safety premise for this boundary. The option-(b) theorem signature is false/under-constrained unless mapped certificates are sealed or every step is safety-certified.

### Probe R5-43 — accepted-index vestigial pipeline, invocation 1

- **Command:** check `R5IndexedVestigialPipeline.idr`, removing `mapped` as an external premise by calling O19 directly from `sameInputs + left/right enriched capitals`, then feeding path first/rest, precise accepted vestigial generation, and right absence to the complete regression.
- **Result:** reached only a transitive-import normalization issue: dependent lookup implementation `DGamma.Coeffects.lookupBinding` was not in scope.
- **Classification:** **note** — import `DGamma.Coeffects` directly and rerun.

### Probe R5-44 — accepted-index vestigial producer chain passes

- **Command:** rerun with direct coeffects import.
- **Result:** passed 169/169. At the abstract accepted indices, no `mapped` premise is needed: the wrapper derives it through O19 and the complete regression consumes enriched schedules, `sameInputs`, exact deleted generation, path first/rest, and right absence.
- **Classification:** **note/positive boundary result**. This validates abstract producer/consumer indices, but it does not instantiate the concrete four-fiber state with reachable traces/bundles; O19 is still a hole and O20 is not exercised by this regression.

### Probe R5-45 — four-fiber “real pipeline” audit

- **Command:** compare the checked concrete model (R5-22/R5-33/R5-36/R5-38) with the exact inputs/output of `intermediateVestigialProducerRegression` and the accepted-index wrapper R5-44; grep for any concrete trace/capital/O20 fixture.
- **Result:** the claimed regression is split into two disjoint artifacts: (1) a static endpoint/path model can construct a pure actor certificate, and (2) a bespoke generic helper packages a certificate when real `sameInputs`, enriched capitals, a scanner-classified vestigial, and O19's mapped result are already available. No concrete four/five-fiber trace inhabits `CanonicalizationPremises`/`IndependentCanonicalSchedule`/accepted scanner capital, and the regression stops at the pure certificate—it never calls `canonicalSchedulesConvergeSpike` or constructs `OperationalActorPermutation`.
- **Classification:** **major** — revision 5 does not provide the advertised concrete end-to-end producer regression. Retain one external module that builds or reuses an actual reachable checked trace fixture and runs O19 **and O20**, or explicitly downgrade the evidence to separate static/interface checks.

### Probe R5-46 — moved registration/tag capital through O20

- **Command:** inventory every `OperationalAdjacentBlockSwap`/`AdjacentSwapResult` occurrence, every downstream `LocatedGeneratedRegistration`, and the exact `RelationalReplayCorrespondence` payload.
- **Result:** `AdjacentSwapResult` exposes local action/tag branch preservation, but `OperationalAdjacentBlockSwap` contains no `AdjacentSwapResult` derivation and no action-occurrence/registration-occurrence correspondence. Its only replay correspondence maps effect generators/stages with equal executable maps/outcomes; an origin may be an iterator or unrelated actual generator and carries no preserved OInsert child/parent/component equation. Yet the final `ReplayedCanonicalEndpointBridge` requires every generated birth in the operational target to map to a precise right generated birth. No intermediate producer/composition theorem for that capital is stated.
- **Classification:** **major** — the historical moved-tag/outcome capital is dropped before the generated-birth bridge consumer. Add a transition/action occurrence permutation correspondence to each operational step and its recursive composition (or store the actual finite `AdjacentSwapResult` derivation), then derive `replayedGeneratedBirthMatched` from it. Hiding this inside O20's single hole defeats the claimed dependency scoping.

### Probe R5-47 — final repository hygiene before closure

- **Command:** verify HEAD/branch, status, staged/tracked diffs, target/baseline production diffs, immutable CP3 blob, and active Idris processes.
- **Result:** still exact `be29a18` on `cp5-thm73-scoping`; no staged files, no tracked worktree diff, both production diffs empty, CP3 blob `2c697e532e83989de8591fa6a4378747c6a501c0`, no Idris process. Untracked paths are pre-existing `paper/` and this mandated report.
- **Classification:** **note** — tracked/index hygiene passes; literal clean status is impossible without deleting pre-existing/requested untracked artifacts, which this review does not do.

## Revision-5 claimed-fix disposition

| # | Claimed fix | Checked disposition |
|---:|---|---|
| 1 | O19 transports only renamed actor membership plus pure permutation; O20 supplies operational safety | **Path weakening itself is sound at the static boundary, but the O19→O20 interface is not.** R5-20 proves callers can inject any swap-and-inverse loop into the public mapped record. R5-41 pure-certifies a parent/child loop; R5-42 proves the exact O/A child exclusion for that block boundary implies `Void`. O20 universally consumes the polluted record. |
| 2 | Recursive operational replay, noncanonical target, exact bridge/O21 coupling | **Partly addressed.** R5-39 confirms exact next trace/blocks/bundle threading. R5-23–25 reject wrong-trace, stale-quotient, and mixed-schedule detachments; R5-26 confirms the public result uses the original schedules. But no one-step producer/derivation is stated, and generated-registration occurrence capital is lost before the bridge (R5-46). |
| 3 | Four-fiber blocker now passes positively through the real pipeline | **Only partly true.** The static model and its moved/two-intermediate variants accept the pure actor target; the licensing-parent mutation is excluded by the full well-formed bundle. The accepted-index wrapper composes abstractly. No single concrete reachable fixture inhabits the enriched traces/scanner and O20; the bespoke regression stops at O19's pure certificate. |
| 4 | Same-name scanner regression with interleaving and concrete ordinals | **Partial.** Full-generation output indices reject raw-name conflation (R5-27–28). But the branch contains no concrete 6/18/9/14 scanner fixture, only conditional projections. Side-only interleaving forgets constructor kind/generation and accepts unrelated alternating prefixes followed by clumped target deletions (R5-32). |
| 5 | 70–120 from raw 70–124 minus 0–4 overlap | **Arithmetic not conservative.** A 0–4 deduction yields possible uppers 124–120. The envelope is 70–124; 120 assumes exactly four shifts of overlap. |

## Historical consumer inventory re-check

1. **Deletion chain / ClosingFreeReduction:** retained trace, full replay bundle, same external inputs, typed withdrawals, endpoint and registration accounting still feed the one-trace producer. R5-26 checks the complete boundary chain.
2. **Moved tags/outcomes and independence:** the local diamonds retain action/tag/branch fields; `RelationalReplayCorrespondence` retains generator-map and iterator-outcome transport; every recursive bundle retains both independence fields. The defect is that O20 does not retain an action/registration-occurrence permutation derived from those local results.
3. **All four local orientations:** A/A, A/O, O/A, and O/O signatures elaborate. R5-42 checks that their safety premises are substantive, not automatically derivable from actor distinctness.
4. **Canonical sorting recursion:** the initial one-trace sorting/enriched-schedule interface still composes. `canonicalActorBlockDecomposition` supplies the exact O20 source blocks.
5. **Cross-trace matching / O19:** actor-set membership and a pure target certificate are sufficient for finite-list matching, including one/two omitted path intermediates. They are not sufficient as a universally consumable operational certificate.
6. **O20 recursion:** exact intermediate trace/block/bundle threading is enforced once a step is supplied. No theorem states how to produce one step from the current blocks/bundle, and public certificate pollution can demand an unsafe step.
7. **O21 / renaming composition:** scanner capital remains indexed by the original schedules; replay quotient and bridge are indexed by the exact noncanonical target; wrong substitutions fail. The generated-birth bridge needs occurrence capital absent from the operational step/result.
8. **Final `ConfluenceResult`:** R5-26 confirms complete outer assembly uses the original valid left/right schedules and the immutable accepted generation/current renamings.

## Findings

1. **blocker — arbitrary public O19 certificates make O20's theorem over-universal** (`research/DGamma/CP5ConfluenceCrossTraceSpike.idr:15-32,134-180,369-391`). `MappedCanonicalSupportOrders` is publicly constructible, and `canonicalSchedulesConvergeSpike` quantifies over every value. R5-20 gives a complete dependent producer that preserves all membership/distinctness/target fields while prefixing any swap and its inverse; O20 accepts the polluted value. R5-41 constructs a concrete parent/child loop, and R5-42 proves the exact O/A generated-child safety condition is impossible for `OInsert child (ChildOf parent)` followed by `LBegin child`. The intended answer “O19 chooses only swaps whose safety O20 can recompute” is therefore not represented by the type.
2. **major — no exact one-step producer or local-diamond derivation is scoped** (`...CrossTraceSpike.idr:62-93`). `OperationalAdjacentBlockSwap` merely asserts a target trace/blocks/correspondence/endpoint/bundle/inputs. No theorem consumes the adjacent actor swap, extracts the two actor blocks, establishes every early transition/applicability/child/licensing/O-O premise at the current intermediate state, invokes finite `AdjacentSwapResult`s, and returns this record. The single top-level O20 hole hides the central expanded proof obligation the redesign was supposed to expose.
3. **major — local moved-action/registration evidence is erased before the generated-birth bridge** (`...LocalDiamondSpike.idr:205-310`; `...CrossTraceSpike.idr:68-93`; `...RenamingCompositionSpike.idr:157-164`). The operational step retains only effect-generator/iterator correspondence, not transition/action occurrence correspondence. That relation cannot identify an OInsert's child, parent, component, or ordinal, while the final bridge requires a precise `LocatedGeneratedRegistration` match for every replayed birth. State and compose action/registration occurrence capital.
4. **major — the advertised four-fiber “real pipeline” regression is two disjoint tests** (`...CrossTraceSpike.idr:187-285`). Static accepted endpoints show the old path contradiction is gone, and a generic wrapper composes when all actual capitals plus O19 are assumed. No concrete reachable four/five-fiber trace constructs those capitals/scanner and runs O20; the regression's output is only the pure actor certificate. This is not the claimed end-to-end operational regression.
5. **major — scanner interleaving regression is weaker than advertised** (`...RenamingCompositionSpike.idr:261-382`). Exact generation memberships are correctly indexed and wrong-ordinal substitution fails. But `scannerSideSequence` erases skip/discard/queue/match and generation identity; global `L…R` plus `R…L` does not show the four target discards are interleaved. No concrete 6/18/9/14 final-index fixture exists in the branch, and outputs are memberships rather than exact final deleted-list equalities/no-spurious-generation facts.
6. **minor/major estimate defect — 70–120 assumes maximal overlap** (`THM73-PLAN.md:178-194`). Raw rows are 70–124. “0–4 overlap” has conservative upper 124, not 120. The still-missing safe-certificate, step producer, and occurrence correspondence also mean the grade table is not yet an authorization estimate.

## Positive results / non-findings

- Full-path/support-comparability transport is genuinely absent; the round-4 contradiction cannot be reconstructed as an O19 field.
- Concrete one-intermediate, moved-position, and two-intermediate models all coexist with the replacement pure target. The licensing-parent mutation is excluded by `ReplayInvariantBundle` well-formedness.
- `OperationalActorPermutation` exactly threads each returned trace, block decomposition, and full bundle into the next step.
- Wrong-trace bridge, stale quotient, and mixed canonical-schedule substitutions are rejected by exact indices.
- The complete published-boundary pipeline elaborates and retains the original valid schedules in `ConfluenceResult`.
- Concrete generation indices 6/18 and 9/14 project distinctly; using `(raw,18)` as `(raw,6)` is rejected.
- All five research spikes elaborate serially; exact release build passes 207/207.
- Immutable CP3 blob, production source, escape-hatch isolation, reachability, tracked worktree, and index hygiene all pass.

## Residual risks

- All 25 hard research theorem bodies remain named holes; type-level scoping does not establish theorem truth.
- Even after sealing the certificate, it remains unproved that a safe actor permutation always exists for two accepted schedules when their full support relations differ through withdrawn intermediates.
- O/A and O/O applicability at actual intermediate replay states remains the highest mathematical gate.
- The scanner occurrence/ordinal induction is still a hole and lacks the demanded concrete same-name reuse fixture.
- The concrete static endpoint models are not themselves reachability proofs.
- The literal worktree contains pre-existing untracked `paper/` plus this required report; no tracked/staged file is dirty.

## Estimate assessment

O19 as finite unique-list matching can plausibly be **M–L**. O20 is correctly labeled **XL** directionally, but its actual sub-obligations are not all stated: safe certificate selection, one-step block expansion at every intermediate state, action/registration occurrence composition, and bridge production. O21 remains XL.

The table's honest arithmetic is **70–124 before new repairs**. Because the blocker adds interface/probe work and may force a safe-permutation redesign, no proof-grind range is authorized. After corrected interfaces elaborate, a provisional **75–130** is more credible; re-estimate from the first complete operational block swap and concrete scanner regression.

## Exact changes required for round 6

1. **Remove universal certificate pollution.** Do not let O20 accept an arbitrary publicly constructible `MappedCanonicalSupportOrders`. Merge certificate choice with operational realization, seal the mapped constructor/certificate behind O19, or index every list step by exact operational safety. Add the R5 swap+inverse pollution probe as a required negative test.
2. **State an exact one-step operational producer.** Its inputs must be one adjacent actor swap, current exact trace/block decomposition/full bundle, and all evidence derivable from them; its output must include the finite A/A+A/O+O/A+O/O `AdjacentSwapResult` derivation. Prove/probe that a parent/child licensing boundary is rejected before invoking O20.
3. **Carry action/registration occurrence correspondence.** Each step and recursive fold must map target transitions/generated births back to source with action/tag/child/parent/component/ordinal equalities. Use that capital to construct `replayedGeneratedBirthMatched`; do not rely on effect-map correspondence.
4. **Make the four-fiber regression genuinely operational or describe it honestly.** A single fixture must use reachable checked traces/full bundles, accepted scanner-deleted vestigial birth, real path, O19 selection, O20 replay, bridge, and O21. If that is not yet constructible because bodies are holes, label the existing artifacts as separate static and abstract interface tests.
5. **Strengthen the scanner regression.** Record scanner event kind and exact generation, tie the four targeted discards to interleaved positions, and retain a concrete correspondence with same-name births 6/18 and 9/14 plus exact final index/deleted lists. Reorder target discard steps across sides and recheck exact lists; retain the wrong-generation negative test.
6. **Fix the estimate.** Use 70–124 if overlap is genuinely 0–4, or document a mandatory exact four-shift reuse argument. Re-estimate upward after the safe-certificate/occurrence redesign (provisionally 75–130).
7. **Re-run all closure probes.** Preserve moved/two-intermediate/licensing-parent mutations, exact operational threading, all three detachment negatives, complete pipeline, 25-hole reconciliation, 207/207 build, immutable blob, and release isolation.

## Verdict

**REJECT.** Revision 5 soundly removes the false cross-endpoint path transport and improves noncanonical trace coupling, but the replacement O19/O20 boundary is itself unsafe: public pure certificates can be polluted with locally impossible parent/child swaps, and O20 promises to operationalize every such value. The missing one-step derivation and registration-occurrence capital are scoping defects, not ordinary hole implementation work.

**Final verdict: REJECT**
