# Theorem 73 Scoping Plan — Adversarial Review, Round 4

**Reviewed branch:** `cp5-thm73-scoping`  
**Reviewed commit:** `e3d8bd485f43d69ee46eb6aa9b925612b4c6fcb8`  
**Immutable production baseline:** `34b21c9`  
**Interface comparison baseline:** `560cd07`  
**Method:** all Idris probes are built serially from an exact source copy under `/tmp/thm73-review4-probes/`; the repository is read-only except this report.

## Probe log (appended contemporaneously)

### Probe R4-00 — branch identity and initial worktree state

- **Command:** `cd /Users/vyacheslavshebanov/Work/dgamma && printf 'branch=%s\ncommit=%s\n' "$(git branch --show-current)" "$(git rev-parse HEAD)" && git status --short --branch`
- **Result:** branch and commit match the review target. Worktree reports pre-existing untracked `paper/` (`?? paper/`).
- **Classification:** **note** — tracked branch content is not yet shown dirty, but the literal “branch worktree clean” hygiene condition is not met because `paper/` is untracked. This review will not modify it.

### Probe R4-01 — round-3 rejection basis reconstructed

- **Command:** `wc -l review-cp5-plan-round{1,2,3}.md THM73-PLAN.md && sed -n '1,260p' review-cp5-plan-round3.md`
- **Result:** round 3 rejected five concrete issues: left-operational state/name mismatch, uncoupled post-permutation result, absent scanner-capital producer, under-estimate, and misleading/under-coupled deleted-generation classification. Its required round-4 probes and exact interface directions are now the review checklist.
- **Classification:** **note**.

### Probe R4-02 — rounds 1–2 and revision-4 plan cross-check

- **Command:** `cat review-cp5-plan-round1.md; cat review-cp5-plan-round2.md; cat THM73-PLAN.md` (the first combined output was pagination-truncated, so round 1 was also read directly in full).
- **Result:** reconstructed all earlier consumer requirements: exact original-endpoint schedule indices; generic replay and full invariant bundle; all four local orientations; support-restricted order transport; enriched one-trace production; typed deletion/scanner linkage; fixed-bijection O21. Revision 4 expressly claims concrete type-level closures for all round-3 issues and 65–110 shifts.
- **Classification:** **note**.

### Probe R4-03 — exact revision-4 change surface

- **Command:** `git diff --stat 560cd07..e3d8bd4; git diff --name-status 560cd07..e3d8bd4; git log --oneline 560cd07..e3d8bd4`
- **Result:** only the plan, three research spikes (deletion chain, renaming composition, cross-trace), and the committed round-3 report changed. Local-diamond and canonical-sort interfaces did not change. Four focused commits correspond to classification, scanner producer, convergence/permutation coupling, and plan rewrite.
- **Classification:** **note**.

### Probe R4-04 — changed-interface textual diff

- **Command:** `git diff --unified=120 560cd07..e3d8bd4 -- research/DGamma/CP5Confluence{DeletionChain,RenamingComposition,CrossTrace}Spike.idr`
- **Result:** actual declarations match the advertised change surface: membership-guarded forward/backward comparability and a left-state permutation; enriched permuted capital and exact-index bridge; scanner discard declarations plus a complete-looking constructor; occurrence + same-parent unload classification. This is only a textual inventory; subsequent probes test producer and consumer indices.
- **Classification:** **note**.

### Probe R4-05 — production immutability before external copy

- **Command:** `git diff --exit-code 34b21c9..e3d8bd4 -- src dgamma.ipkg; git diff --exit-code e3d8bd4 -- src dgamma.ipkg; git diff --cached --exit-code`
- **Result:** all three checks pass empty. Production package source is byte-identical across the required baseline range, the live production paths have no worktree edits, and the index is empty.
- **Classification:** **note**.

### Probe R4-06 — immutable external trees created

- **Command:** archive `e3d8bd4` into `/tmp/thm73-review4-probes/release`; copy its 207-file `src/` into `/tmp/thm73-review4-probes/spikes/src/`; copy exactly the five research spikes beside it; compare `CP3.idr` SHA-1.
- **Result:** release copy contains 207 Idris source files; spike tree contains exactly five `CP5Confluence*Spike.idr` additions; release and spike copies of immutable `CP3.idr` both hash to `d6b9d3c1885908827fb0960813988cd445647922`.
- **Classification:** **note**.

### Probe R4-07 — external-copy delta inspected

- **Command:** `git diff --no-index release/src spikes/src` (captured), then inspect first 80 lines.
- **Result:** the delta consists of added research-spike modules under the copied `src/DGamma/`; no production-file modifications are present. (`git diff --no-index` renders additions as full patches, so the earlier filename-only grep was not meaningful.)
- **Classification:** **note**.

### Probe R4-08 — current declaration indices inspected

- **Command:** line-numbered reads of all changed declaration regions in the three research spikes.
- **Result:** confirmed exact indices used by later probes. Notable scope risks to attack: (i) the permutation result is coupled to target order and bridge, but no field explicitly relates the replay correspondence to the particular `leftOperationalPermutation` derivation; (ii) the composed endpoint is endpoint-indexed but not propositionally identified as the fold of adjacent quotients; (iii) scanner completeness rests entirely on two named-hole correspondence inductions.
- **Classification:** **note** — these are attack hypotheses, not yet findings.

### Probe R4-09 — immutable scanner and theorem target definitions inspected

- **Command:** line-numbered reads of `CP3.idr` occurrence/generation, registration index/scanner constructors, canonical records, and `confluenceTheorem`.
- **Result:** immutable target remains the accepted function type at lines 3785–3810. `LocatedGeneratedRegistration` carries a dependent prefix/suffix and ordinal; scanner discard adds exactly `MkRegistrationGeneration child leftOrdinal`; every queued/matched branch carries `SurvivingRegistration` with `NoParentUnload` on the same constructor suffix. This makes the proposed occurrence/same-parent-close contradiction plausible, but the ordinal alignment must be proved through arbitrary interleaved left/right scanner constructors.
- **Classification:** **note**.

### Probe R4-10 — full accepted scanner constructor space inspected

- **Command:** line-numbered read of all `RegistrationTraceCorrespondence` constructors and final-index projections.
- **Result:** every left generated birth is consumed by exactly one of discard, queue, or pending-match; the latter two require `SurvivingRegistration`. Symmetric right constructors have the same shape. Deleted lists are carried monotonically in `RegistrationIndexState`, but a proof still needs preservation of membership through every later `advance*` case. No alternative constructor silently skips a generated registration.
- **Classification:** **note**.

### Probe R4-11 — enriched schedule classifier availability

- **Command:** inspect `IndependentCanonicalSchedule` and its complete simultaneous constructor; grep all classifier projections.
- **Result:** each enriched schedule carries a total function from its exact canonical endpoint withdrawn list to a classification on the original trace. Therefore applying the scanner producer to `permutedLeftCapital` is index-correct in principle and does not require its withdrawn list to equal the pre-permutation capital's list.
- **Classification:** **note**.

### Probe R4-12 — Idris environment / serialization preflight

- **Command:** `idris2 --version; pgrep -fl '[i]dris2' || true`
- **Result:** Idris 2 v0.8.0 is installed; no Idris process was active. All following checks run synchronously and serially.
- **Classification:** **note**.

### Probe R4-13 — local-diamond spike elaboration

- **Command:** `cd /tmp/thm73-review4-probes/spikes && rm -rf build && idris2 --source-dir src --check src/DGamma/CP5ConfluenceLocalDiamondSpike.idr`
- **Result:** passed, 31/31 modules. This retains all A/A, A/O, O/A, O/O declaration surfaces and the bundle-preserving suffix consumer.
- **Classification:** **note**.

### Probe R4-14 — deletion-chain spike elaboration, invocation 1

- **Command:** `idris2 --source-dir src --check src/DGamma/CP5ConfluenceDeletionChainSpike.idr` (600-second synchronous limit).
- **Result:** harness timed out before returning a result. This is **inconclusive**, not a type failure. The next probe first verifies no process survived, inspects the log, and retries with a longer limit.
- **Classification:** **note**.

### Probe R4-15 — timed-out elaboration cleanup check

- **Command:** `pgrep -fl '[i]dris2' || true; wc -l /tmp/r4-deletion.log; tail -n 20 /tmp/r4-deletion.log`
- **Result:** no Idris process survived; the interrupted check had reached module 94/165 with warnings only. Serialization is preserved.
- **Classification:** **note**.

### Probe R4-16 — deletion-chain spike elaboration, invocation 2

- **Command:** same check as R4-14, retried serially with an 1800-second limit and retained cache.
- **Result:** passed, 165/165 modules. The new classification record and exact left/right scanner-discard theorem signatures elaborate.
- **Classification:** **note** — both scanner induction bodies remain named research holes.

### Probe R4-17 — canonical-sort spike elaboration

- **Command:** `idris2 --source-dir src --check src/DGamma/CP5ConfluenceCanonicalSortSpike.idr`
- **Result:** passed, 166/166 modules. The complete simultaneous `IndependentCanonicalSchedule` constructor remains accepted.
- **Classification:** **note**.

### Probe R4-18 — renaming/scanner spike elaboration

- **Command:** `idris2 --source-dir src --check src/DGamma/CP5ConfluenceRenamingCompositionSpike.idr`
- **Result:** passed, 167/167 modules. In particular, Idris accepts the complete body of `acceptedDeletionScannerCapitalSpike`; its only hard dependencies are the two explicit named-hole scanner inductions.
- **Classification:** **note**.

### Probe R4-19 — cross-trace spike elaboration and complete O21 wrapper

- **Command:** `idris2 --source-dir src --check src/DGamma/CP5ConfluenceCrossTraceSpike.idr`
- **Result:** passed, 168/168 modules. The `originalEndpointsConvergeSpike` body is complete and total at elaboration, constructs scanner capital for `permutedLeftCapital`, and consumes `convergenceBridge` at that same schedule index.
- **Classification:** **note**.

### Probe R4-20 — exact left-state order consumers

- **Command:** check external `R4LeftOperationalPositive.idr`, projecting the exact left-state permutation, inverse-mapped linearization, and backward supported comparability at their consumer indices.
- **Result:** passed, 169/169 modules. The round-3 mismatch is fixed at the abstract order-consumer boundary: source order is `supportOrder leftSchedule`, target is `map renameBackward (supportOrder rightSchedule)`, and the state is exactly `leftFinal`.
- **Classification:** **note**.

### Probe R4-21 — operational replay primitive inventory

- **Command:** inspect `AdjacentSwapResult`, `adjacentSwapSuffixSpike`, `SortedClosingFreeTrace`, and sorting theorem signatures.
- **Result:** the operational primitive swaps *adjacent transitions* given a source-sensitive diamond and full bundle; order permutation swaps *adjacent actor names*. There is no public theorem directly converting one `IncomparableAdjacentOrderSwap` into a finite sequence of transition swaps. That block-expansion induction is intentionally inside named-hole O20; the revised interface can only be tested at its input and enriched-result boundaries, not by a complete external operational replay implementation.
- **Classification:** **note / residual risk**.

### Probe R4-22 — intermediate-vestigial path threat identified

- **Command:** inspect accepted support relation and the existing asymmetric vestigial fixture (`CP3VestigialChecks`); the trailing grep found no pre-written `SupportPath` witness and returned 1 after the read.
- **Result:** membership guards constrain only path endpoints, not intermediate nodes. `SupportPath` permits arbitrary `SupportEdge` intermediates, and precedence edges are defined for any present fibers, not only supported ones. Therefore a path between two supported names can in principle traverse an unsupported vestigial fiber that is absent cross-trace. This can resurrect the round-2 contradiction unless an upstream invariant rules such paths out; no such premise appears in `MappedCanonicalSupportOrders`.
- **Classification:** **major attack hypothesis** pending a concrete checked model.

### Probe R4-23 — coupled convergence consumers and final assembly

- **Command:** check external `R4ConvergenceCouplingPositive.idr`, projecting the exact target order/bridge and composing convergence → scanner-producing O21 → `ConfluenceResult` using the permuted left schedule.
- **Result:** passed, 169/169 modules. The final wrapper has a complete body, takes no scanner or bridge premise, and constructs `ConfluenceResult.leftCanonical` from `permutedLeftCapital`, preserving the endpoint used by O21.
- **Classification:** **note**.

### Probe R4-24 — detached pre-permutation bridge rejection

- **Command:** check expected-failure external `R4DetachedBridgeNegative.idr`, which retypes `convergenceBridge` against `canonicalSchedule leftCapital`.
- **Result:** rejected for the intended exact reason: Idris cannot solve `convergence.permutedLeftCapital` versus `leftCapital`. The bridge cannot detach to the pre-permutation schedule without additional equality evidence.
- **Classification:** **note** (successful negative test).

### Probe R4-25 — scanner consumers, invocation 1

- **Command:** check external `R4ScannerProducerConsumers.idr` with left/right erased membership consumers and an unrestricted accepted-correspondence projection.
- **Result:** stopped only on quantity discipline in the third helper: erased `acceptedDeletionScannerCapitalSpike` is inaccessible from an unrestricted body. The first two quantity-0 membership consumers were accepted before this diagnostic. Mark the correspondence helper quantity 0 and rerun.
- **Classification:** **note** — probe declaration error, not an interface defect.

### Probe R4-26 — scanner producer exact external consumers

- **Command:** rerun `R4ScannerProducerConsumers.idr` with all proof consumers at quantity 0.
- **Result:** passed, 168/168 modules. Both left and right withdrawal-to-accepted-deleted-list functions and the exact accepted scanner correspondence are projected directly from `sameInputs + leftCapital + rightCapital`; no scanner premise is accepted externally.
- **Classification:** **note**.

### Probe R4-27 — scanner raw-name/ordinal fixture inventory

- **Command:** inspect existing accepted `CP3VestigialChecks` correspondence and raw-name/generation fixtures.
- **Result:** the concrete 27/18 correspondence explicitly discards generation `(2,6)`, retains `(4,23)`, interleaves both trace scans, and keeps the deleted generation at the final index. It validates the intended constructor behavior, but no existing production fixture reuses the **same generated raw name** at two birth ordinals. Thus generic raw-name-reuse proof risk remains; the exact classification equality to `RegistrationGeneration` is the only interface-level ordinal guard.
- **Classification:** **minor residual risk**, not a checked counterexample.

### Probe R4-28 — complete research producer/consumer pipeline

- **Command:** check external `R4FullPipeline.idr`, composing both sides through delete-all → closing-free shape/order/sort → support transport/accounting → enriched schedules → mapped matching → enriched convergence → scanner-producing O21 → `ConfluenceResult`.
- **Result:** passed, 169/169 modules. Every published research boundary composes at exact endpoints/namespaces from two initial `CanonicalizationPremises` and accepted `sameInputs`. A/A+A/O+O/A+O/O block execution remains internal to the named-hole sorting/convergence producers, as designed; the wrapper does not establish those bodies.
- **Classification:** **note**.

### Probe R4-29 — source-sensitive O/A consumer retained

- **Command:** check the round-3 external O-then-A application against revision-4 sources.
- **Result:** passed, 32/32 modules. Exact pre-source early activation, action/tag equalities, actor/child/licensing-parent exclusions, well-formedness, and independence still feed `orchestrationActivationDiamondSpike`.
- **Classification:** **note**.

### Probe R4-30 — one-trace vestigial producer/consumer variant

- **Command:** check adapted round-3 `R4VestigialSimultaneous.idr` against revision 4.
- **Result:** passed, 167/167 modules. An explicit accepted original-present/reduced-absent retired/clean child does not obstruct the complete simultaneous enriched-schedule constructor when the minimal support transport is supplied.
- **Classification:** **note**.

### Probe R4-31 — asymmetric mapped vestigial variant

- **Command:** check `R4MappedVestigialVariant.idr`, combining a left vestigial endpoint and absent renamed right fiber with the revised exact left-state permutation consumer.
- **Result:** passed, 169/169 modules. The record shape itself does not exclude the accepted asymmetric vestigial endpoint case and no right-state operational field is required.
- **Classification:** **note**.

### Probe R4-32 — unrestricted comparability negative, invocation 1

- **Command:** check expected-failure `R4UnrestrictedComparabilityNegative.idr` with overly implicit record indices.
- **Result:** inconclusive: the signature failed auto-implicit dependent `value` binding and then produced a cascading accessibility error before reaching the intended missing-membership mismatch. Rewrite with all state/schedule parameters explicit, matching the positive probe.
- **Classification:** **note**.

### Probe R4-33 — unrestricted transport cannot be reconstructed directly

- **Command:** rerun fully explicit expected-failure `R4UnrestrictedComparabilityNegative.idr` omitting both support-order memberships.
- **Result:** rejected at the first missing guard: Idris tries to unify `SupportPath ... lower upper` with `Elem lower (supportOrder leftSchedule)`. The old unrestricted endpoint application is unavailable.
- **Classification:** **note** (successful negative test). This does not address unsupported *intermediate* path nodes.

### Probe R4-34 — intermediate-vestigial countermodel, invocation 1

- **Command:** check initial concrete four-fiber state model with supported endpoints and an unsupported path intermediate.
- **Result:** probe failed before model checking because `the (DecEq N) %search` was parenthesized incorrectly in `SupportPath`/`SupportEdge`, and lowercase global states were auto-generalized in signatures. No semantic premise was tested. Disable auto-implicit and pass both `DecEq` instances explicitly.
- **Classification:** **note**.

### Probe R4-35 — intermediate-vestigial countermodel, invocation 2

- **Command:** retry after explicit-instance edits with `%auto_implicit off`.
- **Result:** Idris 2 v0.8.0 rejected that directive spelling before declarations. Replace it with `%autoImplicit false`; still no model field has been tested.
- **Classification:** **note**.

### Probe R4-36 — intermediate-vestigial countermodel, invocation 3

- **Command:** retry with `%autoImplicit false`.
- **Result:** this directive spelling is also unsupported by the installed Idris parser. Remove the directive and fully qualify lowercase global states in every type signature.
- **Classification:** **note**.

### Probe R4-37 — intermediate-vestigial countermodel, invocation 4

- **Command:** retry after fully qualifying global states.
- **Result:** reached the model. Two elaboration issues remain: dependent `lookupFiber` needs explicit key/value/world/error parameters in the standalone absence theorem, and constructor proof patterns force provider variables to concrete global fibers. Replace forced variables with wildcards and add type arguments.
- **Classification:** **note**.

### Probe R4-38 — checked intermediate-vestigial comparability countermodel

- **Command:** check corrected `R4IntermediateVestigialCountermodel.idr`.
- **Result:** passed, 8/8 modules. Concrete finite states have supported `Lower` and `Upper` on both sides; left has a retired/inactive/empty, unsupported `Middle`, right omits it; left has `Lower → Middle → Upper`; right has no path from `Lower` at all. Both guarded endpoint memberships are inhabited, and `guardedTransportContradiction` proves that the exact revised forward-comparability shape implies `Void` on this model.
- **Classification:** **blocker** — endpoint-only membership guards do **not** prevent the round-2 vestigial-path contradiction when an unsupported vestigial is an intermediate node. Revision 4's producer theorem has no premise excluding such intermediates. The plan's claimed producer inhabitability is therefore unverified and the stated general comparability field is over-strong unless a new closure lemma/invariant rules this model out.

### Probe R4-39 — accepted endpoint refinement, invocation 1

- **Command:** extend the static countermodel with a concrete `CanonicalEndpointRelation` permitting withdrawal of the middle fiber.
- **Result:** stopped on a missing direct `DGamma.Metatheory` import for `EffectStateRelated` and the same lowercase-state auto-generalization in newly appended types. Add the import and fully qualify states; no endpoint field has yet failed semantically.
- **Classification:** **note**.

### Probe R4-40 — accepted endpoint admits the intermediate countermodel

- **Command:** recheck extended `R4IntermediateVestigialCountermodel.idr` after direct import/index fixes.
- **Result:** passed, 8/8 modules. `acceptedCanonicalEndpointAllowsIntermediate` is a complete `CanonicalEndpointRelation leftState rightState`: effects agree because the removed table is empty, controls agree outside `[Middle]`, and `Middle` is an accepted retired/inactive/empty original-present/right-absent withdrawn name with exact generation metadata. Thus the one-trace accepted endpoint family does not rule out the checked guarded-comparability countermodel.
- **Classification:** **blocker**, strengthening R4-38. A cross-trace theorem must use a support relation restricted at **every node/edge** or prove a new invariant that all intermediates of supported-endpoint paths are supported; endpoint guards alone are false.

### Probe R4-41 — unrelated replay trace rejection

- **Command:** check expected-failure `R4UnrelatedReplayNegative.idr`, retyping the stored source→target correspondence to an arbitrary enriched left capital.
- **Result:** rejected for the intended reason: `convergence.permutedLeftCapital` cannot unify with `unrelatedCapital`. Together with R4-24, both replay and bridge are coupled to the same exact permuted capital.
- **Classification:** **note** (successful negative test).

### Probe R4-42 — classification discard core, invocation 1

- **Command:** check a complete generic proof that same-parent close contradicts the scanner's `SurvivingRegistration` branch at the located suffix.
- **Result:** recursive `ActionOccurs`/`NoParentUnload` contradiction elaborates, but the branch wrapper needs an explicit lemma reducing `eventParent (registrationEventAt ... index ...)` through the opaque index argument. This is a small index-normalization obligation, not evidence of insufficiency. Add it by pattern matching `RegistrationIndexState`.
- **Classification:** **note**.

### Probe R4-43 — classification discard core, invocation 2

- **Command:** retry with explicit `registrationEventParentAt` and a rewrite.
- **Result:** Idris reports the rewrite changes nothing because the local `noUnload` has already normalized to `NoParentUnload (deletedParent classification) ...`. The original failure was inference at the call site. Give `noUnload` that exact annotation and call the contradiction directly.
- **Classification:** **note**.

### Probe R4-44 — classification discard core, invocation 3

- **Command:** retry with an exact typed local and no rewrite.
- **Result:** direct assignment still does not unfold `registrationEventAt` through an abstract index. Use `replace` with the explicit parent equality (rather than rewrite syntax) to transport `NoParentUnload` to the stored parent.
- **Classification:** **note**.

### Probe R4-45 — classification really eliminates scanner survival

- **Command:** check corrected complete `R4ClassificationDiscardCore.idr`.
- **Result:** passed, 166/166 modules. A structural proof shows `ActionOccurs (LUnload parent)` contradicts `NoParentUnload parent` on the exact suffix; after a one-line `registrationEventAt` parent normalization, every queue/match `SurvivingRegistration` at the classified occurrence is impossible. The classification's occurrence + same-parent close fields are sufficient for the scanner branch dichotomy.
- **Classification:** **note**. Remaining scanner work is the named-hole correspondence/ordinal induction and deleted-list membership transport, not a missing classification field.

### Probe R4-46 — exact research hole and complete-body inventory

- **Command:** grep named holes across all five spikes; line-number the scanner producer and post-permutation O21 wrapper bodies.
- **Result:** exactly 25 named research holes, matching the plan. Neither `acceptedDeletionScannerCapitalSpike` nor `originalEndpointsConvergeSpike` is among them; both are complete constructor/composition bodies. The hard scanner discard inductions and O21 endpoint theorem remain explicit holes.
- **Classification:** **note**.

### Probe R4-47 — production escape scan and research isolation

- **Command:** scan `src/**/*.idr` for named holes, `believe_me`, `assert_total`, `%default partial`, declaration-form `postulate`; scan `src/` and `dgamma.ipkg` for research/CP5 spike reachability; count package modules.
- **Result:** zero forbidden production hits, zero research reachability hits, and exactly 207 package modules. The 25 named holes are isolated outside the release graph.
- **Classification:** **note**.

### Probe R4-48 — research escape scan and immutable theorem target

- **Command:** scan `research/` for non-hole escape hatches; exact diff `34b21c9..e3d8bd4 -- src/DGamma/CP3.idr`; hash target blob.
- **Result:** no `believe_me`, `assert_total`, `%default partial`, or postulate declarations in research; `CP3.idr` is unchanged from the immutable baseline and hashes to blob `2c697e532e83989de8591fa6a4378747c6a501c0`.
- **Classification:** **note**.

### Probe R4-49 — exact release package build, invocation 1

- **Command:** `cd /tmp/thm73-review4-probes/release && rm -rf build && idris2 --build dgamma.ipkg` (serial, 1800-second limit).
- **Result:** failed operationally with exit 137 / `Killed: 9`, not an Idris diagnostic. The next probe verifies no process survived and inspects cache/log progress before a cache-assisted retry.
- **Classification:** **note** — infrastructure/resource failure, package result inconclusive.

### Probe R4-50 — killed build cleanup/progress

- **Command:** inspect process list, log, and TTC count after R4-49.
- **Result:** no Idris process survived. The killed run produced only 10 TTC files and no type error (single kill line). Reuse the already serially generated 168-module cache from the byte-identical production source in the spike tree, then run the exact release package command to completion.
- **Classification:** **note**.

### Probe R4-51 — exact external package build, invocation 2

- **Command:** seed the release tree with the serially generated cache from the byte-identical spike-tree production sources, then run `cd /tmp/thm73-review4-probes/release && idris2 --build dgamma.ipkg`.
- **Result:** passed through 207/207 package modules; exit 0. The seed contained compiled production dependencies plus external probes, but `dgamma.ipkg` selected only the exact archived release source graph.
- **Classification:** **note**.

### Probe R4-52 — target linearization countermodel, invocation 1

- **Command:** extend the intermediate model with a proof that right order `[Alternate, Upper, Lower]` cannot linearize the left state.
- **Result:** the `BeforeIn` impossibility proof elaborates; the final call hit only lowercase `leftState` auto-generalization. Qualify that state and rerun.
- **Classification:** **note**.

### Probe R4-53 — exact left-target linearization is also refuted

- **Command:** recheck extended countermodel with `inverseMappedRightOrderCannotLinearizeLeft`.
- **Result:** passed, 8/8 modules. The left path forces `Lower` before `Upper`; therefore `LinearizesSupport leftState [Alternate, Upper, Lower]` implies an impossible `BeforeIn`. This attacks not only the forward path field but the exact `backwardMappedRightOrderLinearizesLeft` capital needed to derive the operational permutation.
- **Classification:** **blocker** — a right linear extension can legally order a pair differently when its only left comparability runs through an omitted unsupported vestigial. O19's current exact output is not producer-suppliable in all accepted endpoint cases.

### Probe R4-54 — estimate inventory, invocation 1

- **Command:** script phase ranges, hole count, and spike LOC from `THM73-PLAN.md`/research.
- **Result:** 25 holes and 1,654 spike LOC. The parser found 48–90 across non-bold phase rows but skipped bold phase G, so its phase sum is incomplete. Add G=18–30 explicitly before assessing the advertised total.
- **Classification:** **note**.

### Probe R4-55 — estimate arithmetic and defensibility

- **Command:** inspect all eight phase rows and sum their bands.
- **Result:** phase rows sum to 66–120; advertised 65–110 assumes 1–10 shifts of reuse/overlap. The requested grade changes are present (O2=M–L, O18=S, O19/O20/O21=XL, G=18–30). With the O19 interface now refuted, 65–110 is not defensible as a ready-to-grind estimate; provisional post-redesign planning should be at least about 70–120 and re-estimated after a corrected supported-relation producer probe.
- **Classification:** **major**.

### Probe R4-56 — obsolete field/comment removal

- **Command:** grep current changed spikes for `mappedLeftOrderLinearizesRight`, `mappedOrderPermutation`, `deletedEvent`, and the old “scanner-shaped event” phrase.
- **Result:** all are absent. The unused right-state operational outputs and misleading classification fields/comments were actually removed.
- **Classification:** **note**.

### Probe R4-57 — final repository state before report closure

- **Command:** `git status --short --branch; git diff --cached --name-only; git diff --name-only; git rev-parse HEAD`
- **Result:** HEAD remains exact `e3d8bd485f43d69ee46eb6aa9b925612b4c6fcb8`; no staged files and no tracked worktree changes. Untracked paths are the pre-existing `paper/` and this mandated report.
- **Classification:** **note** — tracked/index hygiene passes; literal worktree-clean status does not because of those two required/pre-existing untracked paths.

## Revision-4 claimed-fix disposition

| # | Claimed fix | Checked disposition |
|---:|---|---|
| 1 | Membership-guarded comparability both ways; exact left-state permutation; right-state fields removed | **Not sound as stated.** The positive consumer now fits exactly and old right fields are gone, but endpoint-only guards do not guard `SupportPath` intermediates. R4-38/R4-40/R4-53 give a checked countermodel admitted by `CanonicalEndpointRelation`; the exact left linearization/permutation target can be impossible. |
| 2 | Enriched `permutedLeftCapital`, exact target order, correspondence, quotient, exact-index bridge; complete O21 wrapper | **Addressed at the interface boundary.** Exact projections and complete final assembly pass. Detached bridge and unrelated replay projections fail on `permutedLeftCapital` as intended. |
| 3 | Complete scanner-capital producer from `sameInputs` + enriched schedules; no external scanner premise | **Addressed at the scoped boundary.** The producer body is complete and both left/right external membership consumers pass without scanner premises. Its two scanner inductions remain explicit research holes, as the plan says. |
| 4 | Exact occurrence + generation + same-parent close; exact scanner induction signatures; misleading fields removed | **Addressed.** Old fields/comments are gone. A complete external core proof shows the close evidence eliminates every scanner surviving/queued/matched branch at the exact suffix. |
| 5 | Revision-4 map and 65–110 estimate with corrected grades | **Textual changes present, estimate not defensible after the new blocker.** Phase rows sum to 66–120 before claimed overlap. |

## End-to-end producer/consumer attack

1. **Deletion chain → closing-free reduction:** exact trace, endpoint, registration accounting, replay bundle, and typed classification indices compose.
2. **Closing-free shape/order → sorting:** exact named producers compose; A/A, A/O, O/A, and O/O remain hard named-hole internals. The separate O/A source-sensitive consumer passes.
3. **Sorting → enriched one-trace schedules:** exact simultaneous producer/consumer composition passes, including the original-present/reduced-absent vestigial variant.
4. **Cross-trace support matching → left operational sorting:** the abstract consumer indices now fit, but the **producer is false in the advertised generality**. An unsupported withdrawn intermediate can create a left `SupportPath` between supported endpoints that has no right counterpart; the exact inverse-right target order need not linearize `leftFinal`.
5. **Post-permutation convergence:** exact target order, replay, endpoint quotient, full enriched capital, and target-indexed bridge share indices. Detached bridge/replay attacks are rejected.
6. **Typed histories → scanner:** complete producer body projects the accepted correspondence and invokes the exact left/right discard inductions. Both external membership consumers take no scanner premise.
7. **Scanner + bridge → O21 → `ConfluenceResult`:** the complete wrapper passes and uses the permuted left schedule consistently.
8. **Whole wrapper:** `R4FullPipeline.idr` composes every published research boundary from two `CanonicalizationPremises` plus accepted `sameInputs` to the immutable `ConfluenceResult`.

The pipeline therefore elaborates only because `canonicalSupportOrdersMatchSpike` is a named hole. R4-38/R4-40/R4-53 show that this hole's current result type is not producer-suppliable in all accepted vestigial shapes.

## Findings

1. **blocker — `research/DGamma/CP5ConfluenceCrossTraceSpike.idr:86-105`: endpoint membership does not make full `SupportPath` transport vestigial-safe.** `SupportPath` permits unsupported intermediates. The checked four-fiber model has supported endpoints on both sides, a left path through a retired/inactive/empty unsupported middle fiber, and the middle fiber absent on the right. `guardedTransportContradiction` refutes the exact forward-comparability field despite both endpoint memberships. A complete `CanonicalEndpointRelation` admits the withdrawal. The same model proves the inverse-right target order may fail `LinearizesSupport leftFinal`, so the exact operational permutation is not generally derivable.
2. **major — `THM73-PLAN.md:188-205`: 65–110 is not ready for authorization.** The table itself totals 66–120 before overlap, and O19 now requires a relation/sorting redesign rather than the claimed localized producer proof. A provisional post-repair range of roughly **70–120** is more honest, followed by re-estimation after a reachable intermediate-vestigial regression passes.

## Positive results / non-findings

- The round-3 left/right state and raw-name namespace mismatch is fixed at the consumer index.
- `CanonicalConvergenceResult` prevents both tested detachments and carries the full permuted schedule capital.
- `originalEndpointsConvergeSpike` is a complete total body and consumes the exact permuted capital plus its bridge; it accepts no scanner/bridge premise from callers.
- `acceptedDeletionScannerCapitalSpike` is a complete total constructor body. Both exact accepted deleted-list consumers pass without a scanner premise.
- The new classification is sufficient to contradict `SurvivingRegistration.NoParentUnload`; no event/index field is missing for that branch elimination.
- Both vestigial interface variants and the O/A application remain accepted.

## Residual risks

- All 25 hard theorem bodies remain named holes by design; type elaboration is not proof.
- The full scanner occurrence/ordinal induction is still a hole. Existing concrete accepted fixtures distinguish birth ordinals but do not reuse the same generated raw name at two births; add that regression before considering O21 low-risk.
- `RelationalReplayCorrespondence` is one-way (each replay generator/stage has a source origin). The enriched target/bridge coupling is adequate for the current consumer, but the operational proof still must show its actual swap fold constructs every advertised field.
- The literal worktree is not clean because of pre-existing untracked `paper/` and the mandated report; tracked files and index are clean.

## Estimate assessment

The requested grade edits are present and individually plausible: O2=M–L, O18=S, O19/O20/O21=XL, and phase G=18–30. Nevertheless, **65–110 is not defensible for the current interfaces** because O19's core output is refuted. After redesign and a checked producer-side regression, use about **70–120 provisionally**, then recalibrate O19/O20 and phase G from the new proof shape.

## Hygiene

- `git diff --exit-code 34b21c9..e3d8bd4 -- src dgamma.ipkg`: empty.
- Immutable `CP3.idr`/`confluenceTheorem`: unchanged; blob `2c697e532e83989de8591fa6a4378747c6a501c0`.
- Production forbidden-source scan: zero named holes, `believe_me`, `assert_total`, postulate declarations, or `%default partial`.
- Research non-hole escape scan: zero hits; exactly 25 intentional named holes.
- Research reachability from `src/`/`dgamma.ipkg`: zero hits.
- All five spikes elaborate serially.
- Exact external package build: 207/207 modules pass (after a resource-killed clean attempt, using the byte-identical serial cache).
- No staged files and no tracked worktree changes.

## Exact changes required for round 5

1. **Redesign O19's relation/certificate; endpoint guards are insufficient.** Do not transport unrestricted `SupportPath` merely because its endpoints are members. Either:
   - prove from the *full accepted/replay premises* that every intermediate of a supported-endpoint path is supported (and refute the checked model with an explicit missing invariant), or
   - replace full-path incomparability with the actual local block-swappability relation needed by the diamond proof and choose a target/sorting strategy that does not require the inverse-right order to linearize the left full `SupportPath` relation.
2. **Add the concrete intermediate-vestigial producer regression.** It must include an accepted/reachable deleted-generation endpoint (or a proof that such a reachable trace is impossible), supported endpoints, an unsupported withdrawn intermediary, and the exact operational target. A field-level vestigial argument that never uses the path is not sufficient.
3. **Re-run exact consumers after redesign.** The left operational trace must still receive a certificate at its real state/name namespace, and the enriched target schedule, replay, quotient, scanner, bridge, O21, and outer result must remain coupled.
4. **Add a same-raw-name/multiple-birth scanner regression.** Exercise both left and right discard inductions through interleaved scanner steps and show the precise birth ordinal—not another generation with the same raw name—enters the final deleted list.
5. **Re-estimate from the corrected O19/O20 shape.** Use approximately 70–120 provisionally; state phase totals and any overlap deduction explicitly.

## Verdict

**REJECT.** Revision 4 genuinely fixes the round-3 consumer index, bridge coupling, scanner-producer boundary, and classification branch evidence. But its top producer claim is still false: membership guards on path endpoints do not exclude unsupported vestigial intermediates, and the exact inverse-right target order need not linearize the left endpoint. Proof work must not start against this O19 interface.

**Final verdict: REJECT**
