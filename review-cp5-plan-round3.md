# Checkpoint 5 Theorem 73 Scoping — Independent Adversarial Review, Round 3

Target: branch `cp5-thm73-scoping` at `560cd070cd5d54b4c0621f4e31ea4b6746bf8944`.

## Probe log and findings

### Probe 1 — target identity and worktree baseline
- **note:** Confirmed branch `cp5-thm73-scoping` and exact target commit `560cd07`.
- **note:** Worktree baseline has only pre-existing untracked `paper/`; `review-cp5-plan-round3.md` did not exist before this review.

### Probe 2 — revision shape
- **note:** The target contains six research-spike changes plus `THM73-PLAN.md` and both prior reports. No production-tree change is shown in the overall stat; the dedicated hygiene probe below checks this exactly.
- **note:** Revision-3 work is split across commits `f9b8285` through `560cd07`, making the claimed additions directly inspectable.

### Probe 3 — round-2 rejection basis reconstructed
- **note:** The eight mandatory changes are: add source-sensitive O/A; remove both false unrestricted path-map interfaces while retaining consumer strength; jointly produce schedule/correspondence/full bundle/independence; retain typed deletion classification into accepted scanner sets; feed full bundles through cross-trace swaps; strengthen O21 with scanner links; and reclose/re-estimate. The review will test actual declarations and external consumers rather than the plan narrative.

### Probe 4 — round-1 consumer requirements reconstructed
- **note:** The weakened revision-3 support interfaces must still solve the original-endpoint schedule indices (`LinearizesSupport` and `CanonicalInputPlacement`) and must still certify that cross-trace block orders are linear extensions of one transported supported partial order with an adjacent-incomparable permutation. Merely deleting the refuted projections is insufficient.
- **note:** The enriched package must retain all swap-recursion premises, not just canonical independence, and O21 must classify original-present unmatched current generations against the exact accepted same-input scanners.

### Probe 5 — actual local-transposition interfaces
- **note:** `research/DGamma/CP5ConfluenceLocalDiamondSpike.idr:356-380` now states a source-sensitive O/A diamond with an actual early activation checked at the pre-orchestration source, action/tag equality, actor inequality, and insertion child/licensing-parent exclusions. `adjacentSwapSuffixSpike` remains generic over a `LocalRelationalDiamond`, so an O/A result can feed the same suffix consumer.
- **residual risk:** Integration into a sorting/permutation recursion is still only via named-hole consumers; later probes must verify the sorting capital can select all four cases rather than merely declaring O/A in isolation.

### Probe 6 — deletion-classification declarations and accepted scanner target
- **note:** `DeletedGenerationClassification` is no longer a plain history: at `...DeletionChainSpike.idr:91-110` it ties a generation to a `LocatedGeneratedRegistration`, exact event child/parent/component/generation equalities, and `DeletedClosingRegistration` on the occurrence suffix. `ClosingFreeReduction:203-214` retains a dependent list and equality of its projected generations to `endpointWithdrawnGenerations`.
- **residual risk:** The accepted endpoint obligations use `leftDeletedGenerations`/`rightDeletedGenerations` produced by `RegistrationCorrespondenceByGeneration`, not the classification list directly. A separate proof must show each retained classification is exactly consumed as a scanner discard and therefore appears in the accepted deleted index. This linkage must be found in O21's actual inputs/record fields.

### Probe 7 — classification adequacy against the accepted scanner
- **major:** `DeletedGenerationClassification` is total only over the reduction's asserted withdrawn list, not intrinsically over an accepted `RegistrationTraceCorrespondence`. The accepted discard constructor (`src/DGamma/CP3.idr:2654-2669`) needs `DeletedClosingRegistration (registrationEventAt ordinal index child parent component) rest`. The new record (`...DeletionChainSpike.idr:97-110`) instead stores an independently chosen `deletedEvent` and equalities only for child, parent, component, and generation. It does **not** equate `deletedEvent` with the scanner's `registrationEventAt`, nor equate its `eventParentActivation`/`eventChildPosition` to scanner state. Consequently the record by itself cannot be used to select `DiscardLeftDeletedRegistration`; an arbitrary event with matching four fields can carry unrelated activation/position metadata.
- **residual risk:** The cumulative type does require one classification for each list entry whose projection equals `endpointWithdrawnGenerations`, so cumulative list coverage itself is strong. The missing event/index coupling may be repaired by a separate scanner-membership theorem if O21 directly carries the exact result; the next probes inspect whether that stronger capital exists.

### Probe 8 — occurrence metadata check
- **note:** `LocatedGeneratedRegistration`/`registrationGeneration` records only the dependent trace occurrence and `(child, ordinal)` (`src/DGamma/CP3.idr:2124ff,2148ff`); it does not definitionally expose the `RegistrationIndexState` used by `registrationEventAt`. Thus the event/index concern in Probe 7 is real rather than a hidden definitional equality.

### Probe 9 — weakened one-trace support transport and simultaneous package
- **note:** Both refuted unrestricted `SupportPath` projections are gone from `CanonicalSupportTransport` (`...CanonicalSortSpike.idr:80-99`). The replacement retains exactly: pointwise support truth, reduced→original `LinearizesSupport`, and reduced→original `CanonicalInputPlacement`.
- **note:** Round-1 consumer strength is preserved: the complete `assembleIndependentCanonicalSchedule` implementation (`:297-322`) feeds `linearizationToOriginal` and `inputPlacementToOriginal` directly into the immutable `MkCanonicalSchedule`, composes reduction and sorting replay correspondences, and packages the full `ReplayInvariantBundle`, both independence witnesses, and withdrawn-generation classifier in the same transparent definition.
- **residual risk:** These direct higher-level transport fields avoid the old vestigial target contradiction, but their derivability from only `CanonicalEndpointRelation` + `CanonicalRegistrationCorrespondence` remains a named hole (`canonicalSupportTransportSpike`). A concrete vestigial probe must verify the interface itself no longer entails the forbidden target lookup.

### Probe 10 — weakened cross-trace order capital and operational convergence
- **note:** The false unrestricted mapped path fields are gone. `MappedCanonicalSupportOrders` (`...CrossTraceSpike.idr:61-89`) now gives support-order membership maps, injectivity, a proof that the renamed left order linearizes the **right original endpoint**, and a certified adjacent-incomparable permutation in that right endpoint. This is sufficient for the abstract linear-extension consumer that motivated round 1.
- **blocker:** It is not indexed for the operational consumer actually declared. `CanonicalConvergenceResult.permutedLeftTrace` replays the **left canonical trace** (`:137-140`), whose actors/order are left names, but `mappedOrderPermutation` transforms `map renameForward leftOrder` to `rightOrder` and certifies support/incomparability at `rightFinal` (`:83-89`). There is no trace/state renaming operation or inverse-transported permutation making those right-name/right-state swaps applicable to the left canonical trace.
- **blocker:** `CanonicalConvergenceResult` drops the post-permutation schedule/order/block evidence entirely. It returns an arbitrary replayed left trace and full generic bundle, but no proof that its block order is the mapped/right order, no `CanonicalSchedule`/block decomposition for it, and no relation tying `permutedLeftTrace` or `permutedLeftFinal` to `convergenceBridge`. The bridge field is independently stated directly between the original two schedules (`:143-145`). Thus the named-hole convergence producer can ignore its alleged operational sorting output, and the full producer/consumer transposition pipeline remains under-strength despite carrying bundles.

### Probe 11 — immutable external probe tree
- **note:** Created `/tmp/thm73-review3-probes/` from the exact `560cd07` `src/` archive plus all five revision-3 research modules. No Idris process was running. All elaboration probes below use this external tree, one process at a time.

### Probe 12 — local-diamond spike elaboration
- **note:** `idris2 --source-dir src --check ...CP5ConfluenceLocalDiamondSpike.idr` passed in the external tree (31-module closure), including the new O/A declaration and generic adjacent-suffix consumer. This validates API/index compatibility, not the named-hole theorem.

### Probe 13 — deletion-chain spike elaboration
- **note:** The revised deletion-chain spike passes sequential elaboration (165-module closure). The dependent history/classification and exact cumulative endpoint indices are accepted. This confirms type shape only; all constructors that establish total classification remain named-hole obligations.

### Probe 14 — canonical-sort/simultaneous-package spike elaboration
- **note:** The canonical-sort spike passes. In particular, Idris accepts the complete body of `assembleIndependentCanonicalSchedule`; schedule endpoint, composed replay correspondence, full bundle, and classifier all align definitionally in-module.

### Probe 15 — renaming/scanner-capital spike elaboration
- **note:** The renaming-composition spike passes, including `AcceptedDeletionScannerCapital` and the corrected O21 signature. Exact scanner deleted-set membership is now an explicit input to O21, so the final consumer no longer has to derive membership from a plain history at the opaque boundary.

### Probe 16 — cross-trace spike elaboration
- **note:** The cross-trace spike passes, including the weakened `MappedCanonicalSupportOrders`, full-bundle convergence record, O21 wrapper, and complete outer `ConfluenceResult` constructor. This does not cure the semantic/index under-strength in Probe 10 because the affected convergence theorem is a named hole and its result omits the necessary coupling fields.

### Probe 17 — removed-projection negative probe, invocation 1
- **note:** The first expected-failure probe also lacked a direct `DGamma.CP3` import, so `SupportPath` itself was out of scope alongside the two old projections. This invocation is inconclusive about projection removal; rerun with the defining module imported directly.

### Probe 18 — removed-projection negative probe, invocation 2
- **note:** With CP3 imported, Idris now reports `supportPathToReduced` undefined (suggesting only the accepted `supportPathsOrdered` theorem), but hidden `SystemState` indices and auto-implicit value coupling still make the combined probe noisy. Also, this Idris check emitted errors while returning zero before the shell's expected-failure assertion, so the next probe uses explicit binders/imports and greps exact diagnostics rather than trusting exit status alone.

### Probe 19 — removed-projection negative probe, conclusive
- **note:** A fully explicit external module reaches both bodies and gets exact undefined-name errors for `supportPathToReduced` and `mappedSupportPathForward`. The two round-2-unsound projections are conclusively absent from the revised APIs.

### Probe 20 — weakened-interface positive consumers
- **note:** A hole-free external module projects the exact original-endpoint `LinearizesSupport` and `CanonicalInputPlacement` needed by `CanonicalSchedule`, plus the right-endpoint mapped linearization and certified permutation needed by the abstract order theorem. It elaborates. Therefore the weak fix did not reintroduce round-1 under-strength at those *abstract* consumer boundaries.
- **residual risk:** The operational left-trace mismatch/drop identified in Probe 10 is downstream of these successful abstract consumers.

### Probe 21 — vestigial simultaneous-package variant, invocation 1
- **note:** The first explicit vestigial wrapper stopped on dependent `lookupFiber` inference and unqualified cross-module accessibility for `assembleIndependentCanonicalSchedule`; no schedule/replay endpoint mismatch was reached. Add explicit lookup parameters and fully qualify the producer, as in the round-2 namespace probes.

### Probe 22 — vestigial simultaneous-package variant passes
- **note:** The corrected hole-free wrapper adds the exact accepted vestigial shape—withdrawn-name membership, original `Just fiber`, retired, lifecycle uninstalled, empty table, reduced `Nothing`—and still constructs the simultaneous `IndependentCanonicalSchedule` by the real complete producer. It elaborates. The old opaque endpoint mismatch and unrestricted-path contradiction do not recur merely from admitting this endpoint case.
- **residual risk:** As expected for a plan spike, the wrapper receives `CanonicalSupportTransport`; it does not prove the named-hole transport producer from the vestigial endpoint. Derivability remains future proof work, but the revised interface itself no longer excludes this accepted case.

### Probe 23 — cumulative classification producer capital
- **note:** Each `DeletionChainStep` retains the full public `DeletionResult`, whose three `GenerationActionSubsequence` witnesses (`src/DGamma/CP3.idr:3676-3686`) can in principle lift later-survivor occurrences back through prior deletions during recursive return. The cumulative classification therefore is not obviously impossible solely because `RelationalReplayCorrespondence` lacks action origins.
- **major:** The spike/plan names no theorem transporting `DeletedGenerationClassification` through a preceding `GenerationActionSubsequence`, and the current classification's freely chosen event still lacks exact scanner-index metadata (Probe 7). `deleteAllClosingEpisodesSpike` hides both substantial obligations under one hole. This is an estimate/scope omission even if the richer `DeletionResult` makes the lift provable.

### Probe 24 — maximal-selection and cumulative-transport plan cross-check
- **note:** `DeletableClosingEpisode`'s `selectedNoDependentClose` and `selectedChildrenHaveNoEpisode` match the support/parent-maximal negative premises consumed by D72; `THM73-PLAN.md:141-145` explicitly scopes occurrence/generation maximal selection (O8), enriched one-step classification (O9), and classification/ordinal transport across replayed traces as Lemma-72-scale work (O11). This corrects Probe 23's tentative “unnamed theorem” concern at the plan level.
- **note:** Generic replay-correspondence composition need not itself encode maximality: maximal selection is upstream in O8/`DeletionChainStep`, while the complete structural composition correctly preserves every target generator map and iterator outcome through arbitrary deletion→sorting chains. No composition-orientation defect found.
- **residual risk:** Probe 7's exact `registrationEventAt` index-coupling issue is still not called out by O9/O11 and remains substantive.

### Probe 25 — O/A positive application, invocation 1
- **note:** The external O/A wrapper omitted a direct `DGamma.Metatheory` import, leaving `TraceIndependent` out of scope and causing a cascading accessibility diagnostic. Add the direct import before judging theorem usability.

### Probe 26 — O/A positive application passes
- **note:** The corrected hole-free external wrapper applies `orchestrationActivationDiamondSpike` in the exact O-then-A source orientation and elaborates. Its insertion conditions cover both the generated child and licensing parent; `earlyRight` supplies checked pre-insertion applicability. Round-2 O/A omission is fixed at the local theorem/consumer signature boundary.

### Probe 27 — operational permutation producer→consumer mismatch
- **blocker:** The external negative probe asks for exactly the permutation usable to replay the left canonical trace: `leftFinal`, raw `supportOrder leftSchedule`, target `map renameBackward rightOrder`. Projecting `mappedOrderPermutation` fails at the state index first: actual is `rightFinal`, with renamed-left→right orders. This concretely validates Probe 10's end-to-end index mismatch; the abstract mapped order cannot drive the declared left-trace replay.

### Probe 28 — classification concern refined
- **note:** On closer constructor analysis, the missing full event equality is not by itself fatal to deriving scanner deleted-set membership. At the located original registration, an accepted scanner branch must either discard or supply `SurvivingRegistration`; the classification's same-parent `ActionOccurs (LUnload parent)` on the exact `afterRegistration` suffix contradicts the latter's `NoParentUnload`. Scanner state supplies its own activation metadata. Thus Probe 7 is downgraded from a demonstrated major defect to a **residual proof risk/documentation mismatch**: the stored arbitrary `deletedEvent` is stronger-looking but not exactly scanner-indexed, and the induction tying occurrence ordinal to scanner state is still unstated.

### Probe 29 — scanner producer inventory
- **major:** `AcceptedDeletionScannerCapital` has consumers but no producer theorem in the research interfaces. The only references are its record declaration and arguments to `canonicalSchedulesToOriginalEndpointSpike` / `originalEndpointsConvergeSpike`; no `acceptedDeletionScannerCapitalSpike : ... -> AcceptedDeletionScannerCapital ...` is stated. `THM73-PLAN.md:154` assigns construction to O21 in prose, but the executable producer/consumer pipeline cannot currently be typechecked end to end without assuming scanner capital as a new input. Add the exact producer signature from `sameInputs` + two enriched capitals (and whatever trace correspondence induction capital is genuinely needed).

### Probe 30 — downstream pipeline with scanner input
- **note:** A hole-free external wrapper composes enriched left/right schedules → mapped orders → canonical convergence → O21 → complete `ConfluenceResult` when `AcceptedDeletionScannerCapital` is supplied as an external premise. All public indices, including the fixed accepted current-name bijection, align. The only explicit producer-boundary omission exposed here is scanner construction; the operational soundness gap remains hidden inside the named-hole convergence theorem (Probes 10/27).

### Probe 31 — full one-trace producer pipeline
- **note:** A hole-free external orchestration wrapper elaborates the exact chain: `deleteAllClosingEpisodesSpike` → closing-free shape → support order → sorting → minimal support transport → orchestration accounting → `independentCanonicalScheduleSpike`. This confirms no weak→strong→weak index regression from deletion through the enriched canonical package.
- **note:** A/A+A/O+O/A+O/O execution remains encapsulated by the named-hole sorting theorem; local O/A is type-consumable (Probe 26), but the downstream cross-trace operational permutation is still mismatched (Probe 27).

### Probe 32 — deletion-classification consumer, invocation 1
- **note:** The consumer probe lacked the direct deletion-chain import and exact generated record-projection namespaces. It failed on scope before testing indices. Add the defining import/qualifiers and rerun.

### Probe 33 — deletion-classification/scanner consumer passes
- **note:** The corrected hole-free helper proves that every left schedule withdrawal yields both a `DeletedGenerationClassification` at the exact original trace and membership in the accepted `leftDeletedGenerations`; the symmetric right fields have identical indices. Thus classification coverage is total over **schedule withdrawals** once `AcceptedDeletionScannerCapital` exists.
- **residual risk:** The capital's construction remains unstated as an interface (Probe 29), and no reverse equality says every accepted scanner deletion is a schedule withdrawal. The latter is not needed for the four endpoint cases, but should not be described as total classification over all accepted-history deletions.

### Probe 34 — estimate calibration inventory
- **note:** Revision 3 has 14 simple `= ?...` named-hole bodies across 1,534 research-spike LOC; this count excludes complete composition/assembly functions and may miss multiline formatting. The phase bands sum mechanically to 60–112 before claimed overlap, while the advertised total is 60–100.

### Probe 35 — exact named-hole inventory
- **note:** A full identifier scan finds **24** named research holes (not 14; Probe 34's simple pattern missed multiline bodies): canonical 6, cross-trace 3, deletion 5, local 8, renaming 2. All are intentionally research-only, but the work estimate must cover these large theorem bodies plus missing scanner/operational interfaces.

### Probe 36 — production-tree and index immutability
- **note:** Exact required command `git diff --exit-code 34b21c9..560cd07 -- src dgamma.ipkg` passes empty. The git index is also empty; no staged files.

### Probe 37 — research reachability
- **note:** `research/` and all five `CP5Confluence*Spike` modules are unreachable from `dgamma.ipkg` and every production Idris import/reference under `src/`.

### Probe 38 — branch/main source hole and escape scan
- **note:** Both target-branch and local `main` `src/**/*.idr` are clean under actual named-hole, `believe_me`, `assert_total`, and declaration-form `postulate` patterns. Research holes remain isolated as intended.

### Probe 39 — exact release package build
- **note:** `idris2 --build dgamma.ipkg` passes all 207 production modules in the external exact tree. Diagnostics are only established lowercase-shadowing warnings. Research modules were not built.

### Probe 40 — mapped-order vestigial endpoint variant
- **note:** A second hole-free variant combines `MappedCanonicalSupportOrders` with a full accepted left `VestigialEndpointGeneration` and absence of its renamed right endpoint fiber, then projects the certified supported-order permutation. It elaborates. The weakened mapped interface no longer rules out the exact asymmetric vestigial case refuted in round 2.

### Probe 41 — 60–100 estimate review
- **major:** **60–100 is not defensible for the interfaces as currently stated**, because O19/O20's operational permutation type must be redesigned and the exact scanner-capital producer is absent. After those corrections, a provisional **65–110** is more credible. The plan's own phase table totals 60–112 before overlap; revision-3 has 24 holes, and O6/O9/O11/O17/O21 remain Lemma-72-scale risks.
- **grade outliers:** O2 is plausibly **M–L**, not a full L, because correspondence composition is proved and transformation lifting is structural. O18 is genuinely **S** assembly given O11/O16/O17 outputs (the full constructor is proved), rather than S–M. O19 must be **XL**, not L–XL, after adding an inverse-renamed left-state operational permutation and two-sided comparability transport. O20 stays **XL** but must explicitly construct post-permutation block/schedule capital and connect it to the right schedule; current grade text omits that output. O21 remains **XL** but needs a separately elaborated scanner producer; phase G should be widened from 12–23 to roughly **18–30**. O13 and O22 grades are reasonable.

### Probe 42 — final repository state
- **note:** No staged or tracked worktree changes. The only untracked paths are the pre-existing `paper/` and this mandated `review-cp5-plan-round3.md`; all probe modules remain outside the repository under `/tmp/thm73-review3-probes/`.

## Verification of the eight round-2 required changes

| # | Status | Actual type-level result |
|---:|---|---|
| 1 | **addressed** | Source-sensitive O/A is stated at `research/DGamma/CP5ConfluenceLocalDiamondSpike.idr:356-380`, its early activation/action/tag/child/parent premises are explicit, and a complete external application passes (Probe 26). |
| 2 | **addressed** | `CanonicalSupportTransport` no longer exports arbitrary paths; its direct linearization and placement fields feed the immutable schedule constructor, and both ordinary and vestigial simultaneous-package consumers pass (Probes 19–22). |
| 3 | **partially addressed; downstream blocker** | `MappedCanonicalSupportOrders` no longer exports arbitrary paths, and an asymmetric vestigial variant passes. Its direct right linearization/permutation is adequate abstractly, but is indexed at `rightFinal` over right names and cannot execute the declared replay of the left canonical trace (Probes 10, 20, 27, 40). This is the round-3 weak→strong→weak regression. |
| 4 | **addressed** | `composeRelationalReplayCorrespondence` is a complete proof, and `assembleIndependentCanonicalSchedule` simultaneously constructs the schedule, exact composed correspondence, full canonical bundle, and both independence values without the opaque endpoint mismatch (Probes 14, 22, 31). |
| 5 | **partially addressed** | Plain history is replaced by dependent original-trace classifications covering every schedule withdrawal. Exact accepted deleted-set membership exists in `AcceptedDeletionScannerCapital`, but there is no stated producer from the two typed histories/capitals (Probes 29, 33). |
| 6 | **partially addressed; downstream blocker** | Both enriched schedules expose full canonical `ReplayInvariantBundle`s and the convergence output returns a full final bundle. However the operational result drops target-order/block/schedule coupling and can return a bridge unrelated to its arbitrary `permutedLeftTrace` (Probe 10). Bundle fields are present; the missing capital is the proof that those bundles belong to the certified block permutation. |
| 7 | **partially addressed** | O21 consumes exact `RegistrationTraceCorrespondence`, both scanner deleted-set memberships, both classifications, enriched schedules, and the fixed canonical bridge. Downstream assembly passes when scanner capital is assumed, but the scanner-capital producer boundary is absent (Probes 29–30). |
| 8 | **not addressed adequately** | Grades O2/O13/O18 were corrected and O20/O21 expanded, but the newly exposed O19/O20 repair and missing scanner producer make 60–100 too low/unsupported. Use 65–110 provisionally after corrected spikes (Probe 41). |

## End-to-end producer/consumer attack

1. **Deletion chain → closing-free reduction:** exact trace/bundle/replay/endpoint/typed-history indices elaborate. The plan correctly assigns maximal selection to O8 and cumulative ordinal/classification transport to O11.
2. **Reduction → canonicalization/sorting:** a complete external orchestration wrapper composes deletion, shape, support order, sorting, minimal support transport, accounting, and enriched one-trace production. It passes.
3. **A/A + A/O + O/O + O/A transpositions:** all four source-sensitive theorem signatures exist; O/A is externally callable. The proof bodies and sorting recursion remain named holes as expected.
4. **Cross-trace matching → operational sorting:** **fails.** The certified permutation lives at the right original endpoint and over renamed-left/right names, while the convergence result replays the left canonical trace. The exact external left-operational consumer fails at `rightFinal` versus `leftFinal`; no inverse transported incomparability capital exists.
5. **Post-permutation convergence:** **under-specified.** The result carries no exact target block order/schedule and no endpoint quotient connecting its replayed endpoint to the canonical bridge, so the operational trace can be ignored by the producer hole.
6. **Typed histories → accepted scanner:** **pipeline gap.** The record shape is strong enough for O21, but no producer signature connects the two enriched capitals to it.
7. **Scanner + bridge → original equivalence → `ConfluenceResult`:** passes exactly when scanner capital is supplied. The generated registration tree and fixed current bijection are definitionally the accepted `sameInputs` projections.

## Revision-3 novelty attacks

### Deleted-generation classification

Coverage is exact for every schedule withdrawal, and the original `DeletionResult` subsequence evidence makes cumulative lifting plausible. The classification is not a total partition of every accepted-history generated birth, nor is such a partition required by O21. Its independently chosen `deletedEvent` is not definitionally the scanner's `registrationEventAt`; this is a minor clarity/proof-risk issue rather than a checked counterexample, because same-parent unload evidence can eliminate the scanner's surviving branch. Round 4 should nevertheless spike the actual membership induction rather than relying on this argument.

### Replay-correspondence composition

The complete proof has the right orientations: generator maps compose source→middle→target; iterator outcomes compose target→middle→source to match the record equation. It is sufficient for arbitrary `TraceEffectTransformation` lifting. Maximal-episode selection is correctly orthogonal and upstream in O8; composition need not encode it.

### Full canonical bundle threading

No field of `ReplayInvariantBundle` itself is dropped between enriched canonical input and final replay bundle. The defect is outside that record: the convergence package does not prove that the replayed trace/bundle realizes the certified target order or connects to the returned bridge. Thus “full bundle carried” is true but insufficient.

## Findings

1. **blocker — `research/DGamma/CP5ConfluenceCrossTraceSpike.idr:83-89,118-169`: operational permutation namespace/state mismatch.** Right-endpoint renamed orders cannot drive left-canonical-trace adjacent swaps; the checked negative probe fails on `rightFinal` versus `leftFinal`.
2. **blocker — `research/DGamma/CP5ConfluenceCrossTraceSpike.idr:118-145`: post-permutation evidence is uncoupled.** `permutedLeftTrace` has no target-order/block/schedule proof or endpoint relation to `convergenceBridge`, allowing the operational sorting output to be ignored.
3. **major — `research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr:172-243`: missing scanner-capital producer.** The record and consumer are exact, but no theorem constructs it from `sameInputs` and the two enriched histories/capitals.
4. **major — `THM73-PLAN.md:159-175`: estimate under-rates the corrected cross-trace work.** O19 must be XL and phase G widened; 65–110 is more credible after interface repair.
5. **minor — `research/DGamma/CP5ConfluenceDeletionChainSpike.idr:91-110`: classification comment/type mismatch.** `deletedEvent` is described as scanner-shaped but is not equated to the scanner event/index. Either tighten it or state/probe the weaker membership induction it is intended to support.

## Residual risks

- All 24 hard research theorem bodies remain named holes by design; elaboration validates scoping, not theorem truth.
- O/A and O/O applicability may still fail during proof despite adequate signatures.
- `canonicalSupportTransportSpike` remains a high-risk derivability gate; the new interface admits vestigials but its producer is unproved.
- Scanner membership induction across raw-name reuse/ordinals is not yet spiked.
- Any public statement repair invalidates the estimate.

## Estimate

Current plan: **not attested at 60–100**. After the exact round-4 interface corrections below, use **65–110 shifts provisionally**, re-estimating after O4, O9, O15, O19/O20, and scanner-capital production. O2 should be M–L, O18 S, O19 XL, O20 XL with explicit post-permutation schedule capital, and O21 XL with an explicit producer. Phase G should be approximately 18–30 shifts.

## Hygiene

- Exact `git diff 34b21c9..560cd07 -- src dgamma.ipkg`: empty.
- Exact external package build: 207/207 modules pass.
- All five research spikes elaborate sequentially.
- Branch and `main` production source scans find no named holes, `believe_me`, `assert_total`, or postulate declarations.
- Research spikes are unreachable from `src/` and `dgamma.ipkg`.
- No staged/tracked review changes; probes are outside the repository.

## Exact changes required for round 4

1. **Add a left-operational permutation output.** `MappedCanonicalSupportOrders` (or a companion) must expose a `CertifiedIncomparablePermutation` at `leftFinal`, from `supportOrder leftSchedule` to `map (renameBackward renaming) (supportOrder rightSchedule)`, with left-state supportedness/incomparability. State the two-sided supported comparability transport needed to derive it. Keep the current right-order theorem only if a real consumer uses it.
2. **Couple operational replay to its target canonical structure.** Strengthen `CanonicalConvergenceResult` with exact target-order block decomposition (preferably an enriched/permuted `CanonicalSchedule`), composed replay endpoint quotient, and a bridge derived from that permuted endpoint to the right schedule. The result type must make it impossible to choose an unrelated `permutedLeftTrace` and independent `convergenceBridge`.
3. **State and elaborate the scanner producer.** Add `acceptedDeletionScannerCapitalSpike` from exact `sameInputs`, left/right `IndependentCanonicalSchedule`s, and any explicitly necessary induction capital. Prove in an external consumer that every schedule withdrawal projects to accepted left/right deleted-set membership without taking the capital as a premise.
4. **Clarify/tighten deletion classification.** Either index its event by a one-trace registration scan/`registrationEventAt`, or add the exact theorem showing that its located occurrence + same-parent close evidence forces the accepted correspondence's discard branch. Update the “scanner-shaped event” claim accordingly.
5. **Re-run the complete pipeline probes and re-estimate.** Make the left-operational permutation negative probe pass positively, add a non-ignorable post-permutation schedule/bridge assembly probe, retain both vestigial variants and O/A application, and use approximately 65–110 with O19=XL and phase G=18–30 until those gates are proved.

## Verdict

**REJECT.** Revision 3 genuinely removes both uninhabitable path projections, preserves the one-trace schedule consumers, proves simultaneous schedule/replay/bundle assembly, adds O/A, and threads exact accepted scanner membership into O21. However, the corrected mapped-order capital is in the right endpoint/name space while the declared convergence replays the left canonical trace, and the convergence result does not couple that replay to any target order or to its bridge. Together with the absent scanner-capital producer, the advertised producer/consumer path still cannot be checked end to end. These are renewed interface-strength defects, not merely unfilled proof bodies.
