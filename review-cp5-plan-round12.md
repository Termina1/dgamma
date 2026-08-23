# Theorem 73 Plan — Round 12 Retirement Review

Scope: revision-12 retirement decomposition only, branch `cp5-thm73-scoping` at `a28b8dea9d9c1efd1019d48184dbe1b37137f0df`.

## Probe log

### Probe 0 — mandatory protected-tree and immutable-statement gate

Commands:

- `git diff --exit-code 34b21c9..a28b8de -- src dgamma.ipkg`
- `git rev-parse a28b8de:src/DGamma/CP3.idr`
- `git rev-parse HEAD`; `git branch --show-current`; `git rev-parse cp5-thm73-scoping`

Result: **PASS**. The protected diff is empty. The CP3 blob is exactly `2c697e532e83989de8591fa6a4378747c6a501c0`. HEAD and branch tip are exactly `a28b8dea9d9c1efd1019d48184dbe1b37137f0df` on `cp5-thm73-scoping`.

Workspace note: `paper/` was already untracked at review start. This review will not touch it.

Finding: **note** — the mandatory gate passes; review may proceed.

### Probe 1 — retirement delta and governing artifacts

Inspected `git show --stat` for `829205a`/`a28b8de`, the complete `git diff c01128e..a28b8de`, and located `THM73-PLAN.md`, `research-tests/cp5-hole-interface-baseline.json`, and `research-tests/O1-INTERFACE-REPAIR-AUDIT.md`.

Result: the code delta at `829205a` deletes exactly the 36-line `CoupledComposedModuloVestigialEndpoint` record and the 31-line `composeModuloVestigialEndpointSpike` declaration/hole from `research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr`. `a28b8de` changes only plan/audit accounting artifacts. The protected `src/` tree and package manifest are untouched. The baseline removes exactly the retired hole entry. The audit itself was added between the audited baseline and retirement.

Finding: **note** — the implementation retirement is narrow and matches the stated decomposition change; orphanhood and coverage still require independent semantic verification below.

### Probe 2 — exact retired-name use inventory, pre- and post-retirement

Ran revision-qualified exact searches for `CoupledComposedModuloVestigialEndpoint`, its constructor, and `composeModuloVestigialEndpointSpike` at both `c01128e` and `a28b8de`, first repository-wide and then restricted to tracked Idris modules under `research/`, `src/`, `tests/`, and `research-tests/`.

Result at `c01128e`: in Idris code, every occurrence is self-contained in `research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr`: record declaration (`:58`), constructor declaration (`:74`), theorem signature (`:1771`, output occurrence `:1792`), and hole body (`:1796`). There is no call site, pattern match, constructor application, field projection through the record type, or other code consumer. Other tracked occurrences are only the baseline signature and historical review prose.

Result at `a28b8de`: there are no occurrences in any tracked Idris code root. Remaining repository-wide occurrences are historical review prose and the retirement audit only.

Finding: **note** — the audit's zero-call-site and zero-output-consumer claim is independently confirmed by revision-qualified tracked-tree searches.

### Probe 3 — raw-premise producer inventory

Ran revision-qualified Idris searches at `c01128e` and `a28b8de` for the raw relation type, both of its constructors, and constructors of `RegistrationCorrespondenceByGeneration`, `CurrentEndpointRenaming`, and `SameOrchestrationModuloGenerated`.

Result: `MkEndpointFiberRelatedModuloVestigial` and `MkSystemEquivalentByRenamingModuloVestigial` occur only at their declarations in `src/DGamma/CP3.idr:3044,3091`; there is no checked constructor application anywhere under `research/`, `src/`, `tests/`, or `research-tests/`. The other mentions of the raw type are theorem inputs/outputs or check signatures, not constructions. The accepted-wrapper construction sites match the audit's five fixture families in `src/DGamma/CP3StatementChecks.idr` and `src/DGamma/CP3VestigialChecks.idr`, plus the private registration-only composition at `research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr` (now `:1587`). None constructs the raw modulo-vestigial system relation.

Finding: **note** — the audit's claim that no genuine checked producer emits even one complete raw pairwise relation, much less a composable pair, is confirmed. The fixture inventory also matches actual constructor sites.

### Probe 4 — authoritative live-hole reconciliation

Parsed `research-tests/cp5-hole-interface-baseline.json`, tested each baseline hole name against its current module, and independently enumerated literal named `_rhs` holes in the five spike modules.

Result: the post-retirement manifest has 31 entries: 25 remain live and six are filled. The live split is exactly 6 canonical-sort / 4 cross-trace / 8 deletion-chain / 6 local-diamond / 1 renaming-O21. The only live renaming hole is `replayedCanonicalToOriginalEndpointSpike_rhs`. No untracked named hole was found in those modules.

Finding: **note** — the revision-12 25-hole accounting is mechanically correct. This list is the basis for the implicit-need trace below.

### Probe 5 — immutable target and direct top-level consumer chain

Inspected `src/DGamma/CP3.idr:2774–3101,3747–3812`, `research/DGamma/CP5ConfluenceCrossTraceSpike.idr:1007–1179`, and the surviving helper prelude.

Result: immutable `ConfluenceResult` requires exactly one outer `RegistrationCorrespondenceByGeneration`, one coupled `CurrentEndpointRenaming`, and one final `SystemEquivalentByRenamingModuloVestigial`; `confluenceTheorem` fixes all three renamings/correspondence to projections of the single input `sameInputs`. `confluenceResultFromCanonicalCapital` is already a hole-free direct `MkConfluenceResult` assembly. `originalEndpointsConvergeSpike` is also hole-free and delegates once to O21's `replayedCanonicalToOriginalEndpointSpike`, passing the outer `sameInputs` authority plus O18/O20 heterogeneous capital. It neither accepts nor composes two raw modulo-vestigial relations.

Finding: **note** — no generic pairwise endpoint-relation composition is present at the immutable result boundary or its two immediate consumers.

### Probe 6 — heterogeneous capital interfaces and O21 scanner sources

Inspected the complete definitions of `CanonicalEndpointRelation`/`CanonicalSchedule` (`src/DGamma/CP3.idr:3208–3264`), `RelationalReplayEndpoint` (`research/DGamma/CP5ConfluenceLocalDiamondSpike.idr:461–477`), `IndependentCanonicalSchedule` and its sealed projections (`research/DGamma/CP5ConfluenceCanonicalSortSpike.idr:566–746`), `ReplayedCanonicalEndpointBridge`, `AcceptedDeletionScannerCapital`, and the exact O21 signature (`research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr:1738–1878,2264–2294`), plus the scanner-induction signatures in `research/DGamma/CP5ConfluenceDeletionChainSpike.idr:151–213`.

Result: the actual chain carries four deliberately different relations:

1. original ↔ canonical via each schedule's `CanonicalEndpointRelation`;
2. canonical-left → replayed-left via `RelationalReplayEndpoint`;
3. replayed-left → canonical-right via `ReplayedCanonicalEndpointBridge` fixed to the outer current bijection; and
4. canonical-right ↔ original-right via the right schedule's `CanonicalEndpointRelation`.

The only registration/current authority at the output index is the single outer `sameInputs`. `AcceptedDeletionScannerCapital` links each one-trace withdrawn generation directly into that outer scanner's deleted lists. Its producer delegates to the two still-live scanner induction obligations; neither produces a raw modulo relation. `IndependentCanonicalSchedule` seals canonical endpoint, authenticated registration map, occurrence map, and deleted-generation classification to one producer chain.

Finding: **note** — the remaining interfaces provide a direct heterogeneous proof route to O21 and do not form, request, or expose two adjacent raw `SystemEquivalentByRenamingModuloVestigial` values.

### Probe 7 — all 25 live signatures scanned for implicit raw-relation dependencies

Mechanically scanned every live baseline signature for the retired names and for the relevant endpoint relation types.

Result: none of the 25 signatures mentions either retired name. Exactly one live hole mentions `SystemEquivalentByRenamingModuloVestigial`: `replayedCanonicalToOriginalEndpointSpike`, as its final output. That signature receives `RelationalReplayEndpoint` and `ReplayedCanonicalEndpointBridge` instead of raw pairwise modulo relations. No live hole accepts a raw modulo relation as input. `canonicalSupportTransportSpike` mentions only the unrelated one-trace `CanonicalEndpointRelation`.

Finding: **note** — there is no interface-level implicit need for generic raw endpoint transitivity anywhere in the 25-hole set. Any such use could only be an optional implementation tactic inside O21, not a required producer/consumer edge.

### Probe 8 — isolated Idris probe workspace

Created `/tmp/thm73-review12-probes/` and copied `src/`, `research/`, and the package file there. Confirmed `Idris 2, version 0.8.0`. No repository source/test/plan/manifest file was modified.

Finding: **note** — all subsequent typechecking experiments run only against the isolated copy, one Idris process at a time.

### Probe 9 — positive Idris witness for direct heterogeneous effect composition

Created `/tmp/thm73-review12-probes/all/DGamma/Review12DirectEffects.idr`. It proves, from exactly the left/right canonical endpoint relations, the relational replay endpoint, and the replay-to-right bridge, the two effect fields required by the final outer relation:

- `worldState leftFinal = worldState rightFinal`; and
- the renamed pointwise table lookup equality at the outer `currentNameBijection`.

The proof composes the left canonical effect relation, replay endpoint, bridge, and symmetric right canonical effect relation directly. It never constructs or consumes a raw pairwise `SystemEquivalentByRenamingModuloVestigial`.

Validation: `idris2 --source-dir all --check all/DGamma/Review12DirectEffects.idr` **PASS** (Idris 2 0.8.0). The first isolated package bootstrap was host-killed (exit 137) and its single mandated serial retry timed out after 1200s; I then used a combined source tree wholly under `/tmp`, retried one host-killed source check once, corrected only probe-local elaboration issues, and obtained the clean passing check above.

Finding: **note** — O21's effect half is constructively reachable through the sealed heterogeneous chain without generic raw-relation transitivity.

### Probe 10 — positive Idris witness for direct non-vestigial control composition

Created `/tmp/thm73-review12-probes/all/DGamma/Review12DirectControls.idr`. It proves reusable algebra for composing:

- exact `FiberControlMaybeRelated` segments (canonical deletion and relational replay),
- one renamed `MaybeFiberRelatedBy` segment (the replay bridge), and
- the symmetric exact right-canonical segment,

into the final `MaybeFiberRelatedBy` non-vestigial disposition under the one outer name bijection. The proof structurally composes parent, retirement, lifecycle iterator/accumulator/view/outcome evidence; it does not involve a raw modulo-vestigial system relation.

Validation: `idris2 --source-dir all --check all/DGamma/Review12DirectControls.idr` **PASS**.

Finding: **note** — O21's exact/non-vestigial control branch is constructively composable from the heterogeneous interfaces, again without generic raw-relation transitivity.

### Probe 11 — exact immutable-statement assembly from the 25-hole pipeline

Created `/tmp/thm73-review12-probes/all/DGamma/Review12FullCoverage.idr` with:

1. a hole-free constructor of `ReplayInvariantBundle`/`CanonicalizationPremises` from the exact immutable theorem premises, using checked production lemmas for preservation, provenance/ranks, precedence/support well-foundedness, and Lemma 70; and
2. `review12ConfluenceCoverage : confluenceTheorem name key value world error`, whose body runs the left/right deletion, shape, ordering, sorting, transport, accounting, O18 capital, O19 matching/permutation, O20 convergence, O21 endpoint, and O22 direct result assembly.

The module imports the post-retirement spike set. It contains no additional hole and no retired-name reference.

Validation: `idris2 --source-dir all --check all/DGamma/Review12FullCoverage.idr` **PASS** against Idris 2 0.8.0.

Finding: **note** — this is a concrete typechecked coverage witness that the exact immutable `confluenceTheorem` type remains derivable from the surviving pipeline, conditional only on filling the 25 declared holes. Retirement removed no final-assembly dependency.

### Probe 12 — closure scan for undeclared proof debt

Ran a revision-qualified scan across all tracked Idris roots for named `_rhs` holes and checked all three positive `/tmp` probe modules for holes and retired-name references.

Result: exactly 25 tracked named holes exist at `a28b8de`, matching the baseline/live split. The positive effect, control, and full-coverage probe modules contain no holes. The full-coverage probe contains neither retired name.

Finding: **note** — the coverage witness is conditional on precisely the advertised 25 obligations, not on a hidden replacement transitivity hole.

### Probe 13 — revision-12 documentation reconciliation

Inspected the final release-boundary text in `THM73-PLAN.md:416–432` against the revision-12 accounting above it.

Finding: **minor** — `THM73-PLAN.md:418,425,432` remains stale: it calls for an “External round-11 review,” requires the superseded `148–257` arithmetic, and says the theorem remains unproved “after revision 11.” These should say round 12, `148–249 total / 139–240 implementation remaining` (or the chosen exact release wording), and revision 12. This is documentation/estimate-only; it does not affect orphanhood, inhabitation, or immutable-statement coverage.

### Probe 14 — semantic inspection of every non-declaration raw-type mention

Inspected the remaining raw-type mentions identified in Probe 3: `src/DGamma/CP3VestigialChecks.idr:1160,2009`, `src/DGamma/CP3StatementChecks.idr:3805`, `research-tests/DGamma/R6MixedScheduleNegative.idr:28`, and `research-tests/DGamma/R6OuterSchedulesPositive.idr:21`.

Result: the vestigial checks project `finalEndpointsEquivalent` from an externally supplied `confluenceTheorem` claim; the CP3 statement check is a projection guard from an already-built `ConfluenceResult`; the positive research test accepts the final relation as an input to O22; and the negative test attempts a deliberately ill-indexed O21 call. None constructs a raw relation or supplies a pair to a compositor.

Finding: **note** — semantic inspection, not just constructor-name counting, confirms the producer inventory and orphan claim.

### Probe 15 — retired output-record projection inventory

Searched tracked Idris code at both `c01128e` and `a28b8de` for every field of `CoupledComposedModuloVestigialEndpoint` (`composedRegistrations`, `composedNameBijection`, both coupling equalities, `composedCurrentEndpoint`, and `composedEndpointRelation`).

Result: at `c01128e` all occurrences are confined to the field declarations inside the record itself (`research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr:75–88`); at `a28b8de` there are none.

Finding: **note** — zero output-record consumers is independently confirmed even when searching projection names rather than the record/function names.

## Findings

1. **minor** — `THM73-PLAN.md:418,425,432`: the revision-12 release boundary retains round-11 labels and superseded `148–257` arithmetic. Documentation-only correction required.
2. **note** — `research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr` at `c01128e`: the retired theorem, output record, constructor, and every output projection had no call site or consumer; post-retirement no tracked Idris occurrence remains.
3. **note** — `src/DGamma/CP3StatementChecks.idr` and `src/DGamma/CP3VestigialChecks.idr`: all genuine accepted-wrapper producers stop at `SameOrchestrationModuloGenerated`; no code constructs a raw modulo-vestigial relation.
4. **note** — `research/DGamma/CP5ConfluenceCrossTraceSpike.idr:1118–1179` and `research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr:2264–2294`: the actual final chain consumes heterogeneous O18/O20/O21 capital and one outer registration/current authority, never two raw pairwise relations.
5. **note** — `/tmp/thm73-review12-probes/all/DGamma/Review12FullCoverage.idr`: a hole-free exact `confluenceTheorem` assembly typechecks against the surviving 25-hole pipeline.

No blocker or major finding was identified.

## Answers to the three review questions

### 1. Orphanhood

**Yes.** At `c01128e`, the retired declaration and record are self-contained definitions with no calls, constructor applications, or projection consumers. No checked module produces their two-raw-relation premise package: there is no application of either raw relation constructor anywhere. The five accepted fixture families construct only registration/current/`SameOrchestrationModuloGenerated` authority. At `a28b8de`, retired names and projection tokens are absent from all tracked Idris code.

### 2. Implicit need

**No.** None of the 25 live interfaces accepts a raw `SystemEquivalentByRenamingModuloVestigial`; only O21 returns the final one. O18 carries one-trace canonical endpoint relations, O20 carries a relational replay endpoint plus a fixed replay-to-right bridge, `originalEndpointsConvergeSpike` delegates directly to O21, and O22 packages its result. Positive Idris probes typecheck direct effect composition and direct non-vestigial control composition through those heterogeneous relations. The sealed chain does not need to compose two raw modulo-vestigial values to reach the immutable output.

### 3. Coverage

**Yes.** The protected production diff is empty and the CP3 blob is exact. The isolated `review12ConfluenceCoverage : confluenceTheorem name key value world error` typechecks and uses exactly the post-retirement pipeline, with no extra hole or retired helper. Thus the immutable statement remains fully derivable in principle once the advertised 25 obligations are filled.

## Residual risks

- O21's vestigial case analysis and its two accepted-scanner induction dependencies remain genuine members of the 25-hole proof debt. This review establishes that they use the sealed outer authority rather than generic raw transitivity; it does not claim those proofs are already complete.
- The complete tracked runner was not rerun in the repository because the review was read-only and the isolated package bootstrap was host-killed then timed out on its one retry. The combined `/tmp` source graph nevertheless compiled through all 172 dependencies needed by the exact coverage witness, and all three targeted probe modules passed.
- A pre-existing untracked `paper/` directory remains untouched.

## Required change

Update `THM73-PLAN.md:418,425,432` to revision-12 review/release wording and current budget arithmetic. No code/interface restoration is required.

## Verdict

ACCEPT-WITH-CHANGES
