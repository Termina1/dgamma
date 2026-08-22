# Theorem 73 (Confluence) — CP5 scoping plan, revision 2

Branch: `cp5-thm73-scoping`  
Round-1 review: `review-cp5-plan-round1.md` (**REJECT**, twelve required
changes)
Scope: research interfaces and planning only. No proof implementation starts in
this branch.

The accepted statements and every file under `src/` are immutable in this
revision. Files under `research/DGamma/` contain deliberate named holes, are not
listed in `dgamma.ipkg`, must never merge unchanged to `main`, and exist only to
check that the revised dependency interfaces elaborate against the release API.

## Executive estimate

The provisional budget is **50–90 engineering shifts**. The previous 24–50
range and 34-shift recommendation are withdrawn. The new lower bound assumes
that the shared RAR generator/stage correspondence works for deletion and swaps,
that O/O transposition has no countermodel, and that original→reduced support
transport follows from the accepted endpoint controls. The upper end allows
Lemma-72-scale work in generic independence transport, suffix replay,
cumulative exact-generation accounting, support-index transport, canonical
sorting, and vestigial endpoint composition.

This range remains provisional until five early gates elaborate as proofs rather
than hole-bearing interfaces:

1. generic RAR independence transport;
2. source-sensitive yielded O-Insert/O-Insert transposition;
3. complete recursive premise re-establishment after one D72 replay;
4. original→reduced support/input-placement transport; and
5. exact canonical-schedule-to-original endpoint composition.

The final `ConfluenceResult` constructor remains small. The critical path is the
proof-producing replay/correspondence capital connecting every preceding stage.

## 1. Accepted statement surface

`confluenceTheorem` remains the accepted two-trace finite-host statement.
`SameOrchestrationModuloGenerated` is fixed capital and continues to package the
historical generation bijection, external-root correspondence, generated
registration tree, and current endpoint renaming. Deriving that package from
bare paper orchestration remains optional post-Theorem-73 Lemma-56 debt.

No CP3 statement repair is proposed. The round-1 failures were internal
interface gaps:

- deletion discarded exact external/generated orchestration evidence;
- local diamonds discarded tags and iterator-stage correspondence;
- there was no O/O diamond;
- deletion and swap recursion did not return the premises consumed next;
- sorting facts were indexed at the reduced endpoint while
  `CanonicalSchedule` requires the original endpoint;
- cross-trace convergence omitted independence and support-path comparability;
- the old renaming spike consumed relations canonicalization did not produce;
  and
- its endpoint renaming was not coupled to the composed bijection.

## 2. Revised checked interface pipeline

The following research types now make stage boundaries explicit.

| Producer | Exact output | Consumer |
|---|---|---|
| Any relational deletion/suffix/swap replay | `RelationalReplayCorrespondence source replayed` (actual/yielded generators and iterator stages with map/outcome preservation) | generic `traceIndependentAfterRelationalReplaySpike`; deletion, sorting, and cross-trace wrappers |
| Any recursive replay state | `ReplayInvariantBundle trace` (alignment, discipline, empty/well-formed start, endpoint well-formedness, totality, quiet/no-failure, independence, provenance, protocol/parent ranks, `PrecedenceAcyclic`, `SupportWellFounded`, `SupportMatchesActive`) | next deletion selector, adjacent swap, Lemmas 68/70, support ordering |
| A/A, A/O, or O/O local commute | `LocalRelationalDiamond` with moved action **and tag** equations plus activation/orchestration branch reconstruction | `AdjacentSwapResult` |
| Adjacent pair plus suffix replay | `AdjacentSwapResult` with replayed checked trace, full correspondence, same external inputs, endpoint relation, and next `ReplayInvariantBundle` | repeated sorting/block permutation |
| Delete-all recursion | `ClosingFreeReduction` with same external inputs, replay correspondence, exact withdrawn history, cumulative endpoint, and `CanonicalRegistrationCorrespondence` indexed by the endpoint list | closing-free shape, support transport, sorting, one-trace assembly |
| Closing-free sorting | `SortedClosingFreeTrace` with full recursive premises, replay correspondence, external input witness, blocks/coverage/input placement, no-withdrawal endpoint, and registration tree | full one-trace orchestration accounting and schedule assembly |
| Original→reduced endpoint proof | `CanonicalSupportTransport` covering support truth, both `SupportPath` directions, parent lookup, `LinearizesSupport`, and `CanonicalInputPlacement` | exact `oneTraceCanonicalScheduleSpike` |
| Deletion+sorting accounting | `OneTraceOrchestrationAccounting` with composed endpoint, `SameExternalOrchestration`, and exact retained/deleted generated registration accounting | exact `CanonicalSchedule original` constructor |
| One-trace canonicalization | `IndependentCanonicalSchedule` carrying public schedule, original independence, replay correspondence, and canonical independence | mapped support orders and cross-trace transpositions |
| Mapped support proof | `MappedCanonicalSupportOrders` with membership, support-path preservation/reflection, and `CertifiedIncomparablePermutation` | canonical block convergence |
| Cross-trace canonical matching | `CanonicalEndpointBridge` propositionally fixed to the accepted current-name bijection | exact original-endpoint composition |
| Canonical schedules + bridge + accepted original renaming | `SystemEquivalentByRenamingModuloVestigial` at the two **original** finals | `ConfluenceResult` |

Two ordinary algebra helpers remain fully proved in research:
`composeGenerationBijection` and `composeNameBijection`.

### 2.1 Round-1 negative probes

The review's negative probes are addressed at their type boundary:

- the former tag probe could not derive a moved L-Iter/L-Finish tag from action
  equality; `LocalRelationalDiamond` now exposes `movedRightTag` and
  `movedLeftTag`, while replay correspondence separately preserves iterator
  stage outcomes;
- the former support-index probe could not use a `LinearizesSupport` proof at
  `reducedFinal` where `CanonicalSchedule` demands `originalFinal`;
  `CanonicalSupportTransport.linearizationToOriginal` and
  `inputPlacementToOriginal` now feed an exact
  `oneTraceCanonicalScheduleSpike` returning `CanonicalSchedule original`.

Elaboration of these interfaces does not prove the transports; it proves that a
successful implementation will produce exactly the immutable release types.

## 3. Proof obligations in dependency order

There are **23 obligations total: 22 proof obligations plus O23
validation/release work**. Difficulty grades are S (small), M (bounded), L
(large), and XL (Lemma-72-scale/critical). Grades are not one-shift estimates;
several share the same replay case analysis, which is why their critical-path
budget is smaller than summing them independently.

| ID | Concrete obligation and produced capital | Depends on | Grade and justification |
|---|---|---|---|
| **O1** | Prove trace/list measure algebra; `SameExternalOrchestration` reflexivity/transitivity/full deletion+sorting composition; `RelationalReplayEndpoint` reflexivity/transitivity; retain proved name/generation bijection composition. | accepted CP3/RAR | **M.** Elementary propositions, but dependent `Transitions` endpoints and quotient composition require deliberate rewrites. |
| **O2** | Prove generic `RelationalReplayCorrespondence` lifting from generators to all finite `TraceEffectTransformation`s and inhabit `traceIndependentAfterRelationalReplaySpike` for both Definition-60 fields. | O1, RAR, effect respect | **XL.** Must preserve actual, continuation, yielded inverse, iterator outcome, and arbitrary composition maps at replay-created source states. This is the first hard gate. |
| **O3** | Prove activation/activation local diamonds for L-Begin and L-Advance tags L-Iter/L-Finish, returning exact moved tags/branches and relational endpoint capital. | O2, L71 quotient | **L–XL.** Nine tag pairs plus control applicability and failure-aware iterator outcomes. |
| **O4** | Prove activation/orchestration diamonds for root/internal insert, retire, and remove with early applicability and parent-license conditions. | O2–O3, registration discipline | **L–XL.** O-Insert freshness and parent-yield licensing are source-state sensitive. |
| **O5** | Prove orchestration/orchestration diamonds, especially two yielded O-Inserts, using early checked firing, exact generation scan, freshness, distinct children, parent licensing, and registration-position discipline. | O1–O2, GEN | **XL gate.** A concrete countermodel invalidates current Path-A block swapping and forces algorithm redesign. |
| **O6** | Implement `AdjacentSwapResult`: splice each local diamond, replay the untouched suffix, compose quotient endpoints, and return same external inputs, generic correspondence, and a complete next `ReplayInvariantBundle`. | O1–O5, RAR | **XL.** This is the operational Lemma-71 bridge; it repeats exhaustive action replay and must preserve all recursion capital. |
| **O7** | Build executable occurrence-indexed episode scanners/classifiers for closed and interleaved-open episodes, including exact begin ordinals and open-episode uniqueness. | GEN, existing located episodes | **L.** Finite scan is executable, but dependent decompositions and raw-name reissue make certificates expensive. |
| **O8** | Select a support/parent-maximal closing episode; derive `NoDependentClosingEpisode`, exact registered generations, outside-selected evidence, and `NoRegisteredEpisode`. | O7, Lemmas 68/70 capital | **XL.** Maximality ranges over occurrence-indexed activations and exact generations, not raw names. |
| **O9** | Enrich the internal D72 call/fold—not the public `DeletionResult`—to return deletion replay correspondence, same external inputs, exact per-step canonical registration/endpoint evidence, strict decrease, and every next recursive premise including `ReachedFromEmpty`/`PrecedenceAcyclic` capital. | O2, O8, checked D72 | **XL.** This resolves the rejected universal-public-result mismatch and may require changes across the internal Lemma-72 fold modules when implementation begins. |
| **O10** | Prove strict `traceLength` decrease and define well-founded delete-all recursion over `ClosingStepChoice`. | O7–O9 | **L.** Measure is simple; dependent recursive result and selector recomputation are not. |
| **O11** | Compose per-step external-input, replay, endpoint, and generated-registration evidence into `ClosingFreeReduction`; flatten exact withdrawn-generation history definitionally to the cumulative endpoint index. | O1, O9–O10 | **XL.** Live generation environments change per iteration; raw-name reuse makes cumulative accounting Lemma-72-scale. |
| **O12** | Derive `ClosingFreeTraceShape`: exactly one begin ordinal for each final supported actor and no lifecycle occurrence for unsupported actors; prove closing-free quiet/no-failure excludes L-Divert/L-Raise/L-Leave/L-Unload from canonical blocks. | O7, O11, Lemma 70 | **L–XL gate.** A retained non-paper activation tag is a statement/algorithm obstruction, not a supervisor preference. |
| **O13** | At every survivor, reconstruct exact `ReachedFromEmpty`, provenance, protocol ranks, parent-rank increase, `PrecedenceAcyclic`, `SupportWellFounded`, and `SupportMatchesActive` from the shared bundle; invoke Lemmas 68/70 without index adapters. | O9, accepted support proofs | **L.** Individual theorems exist; the risk is exact replayed-trace and endpoint indexing. |
| **O14** | Construct finite duplicate-free `SupportOrderingCapital`/`LinearizesSupport` from current registry entries and ranked support paths. | O13, CP4Support | **M–L.** Topological order is finite; tie order and membership/uniqueness certificates are dependent. |
| **O15** | Prove `CanonicalSupportTransport` from original to closing-free endpoint: withdrawn unsupportedness, `isSupported` equality, both `SupportPath` maps, parent lookup, linearization, and input-placement transport. | O11, O13–O14 | **XL gate.** The round-1 probe proved this is substantive; endpoint relations are not definitional equality. |
| **O16** | Move root inputs before lifecycle while preserving their exact relative order; compose `SameExternalOrchestration`; account for retained/deleted generated registrations and place every surviving generated child birth before its block. | O1, O4–O6, O11 | **L–XL.** Root retire/remove and generated events obey different placement rules. |
| **O17** | Sort closing-free trace by repeatedly consuming `AdjacentSwapResult`; move yielded O-Inserts with actor blocks; preserve all recursive premises and construct blocks, order, coverage, reduced-index input placement, endpoint, and registration tree. | O5–O6, O12–O16 | **XL.** Repeated relational suffix replay and O/O crossings make this likely Lemma-72-scale or larger. |
| **O18** | Compose deletion and sorting into `OneTraceOrchestrationAccounting`, apply support transport, and inhabit exact accepted `CanonicalSchedule original`, including original discipline and definitionally identical withdrawn endpoint/registration lists. | O11, O15–O17 | **L–XL.** Mostly assembly only after all transports exist, but ordinal/generation composition may surface index debt. |
| **O19** | Through accepted current renaming, preserve/reflect support membership and paths; construct a certified adjacent-incomparable permutation from mapped left order to right order. | O13–O15, accepted same-input package | **XL.** Vestigials must be excluded from support and two orders must linearize the same transported partial order. |
| **O20** | Carry original and canonical independence in `IndependentCanonicalSchedule`; execute O19's certified block transpositions and produce `CanonicalEndpointBridge` with the accepted current bijection fixed by equality. | O2–O6, O18–O19 | **XL.** Every cross-trace swap is operational and replay-created, so generic independence is required again. |
| **O21** | Prove `canonicalSchedulesToOriginalEndpointSpike`: consume exactly two schedules, their canonical endpoint/registration fields, the canonical bridge, and accepted original generation/current renamings; classify four vestigial endpoint cases and return the exact original-final equivalence. Prove generic composed-current coupling as supporting algebra. | O1, O11, O18–O20 | **XL.** Scanner composition, vestigial union, and exact ambient/table/control transport form the final major gate. |
| **O22** | Assemble both schedules and O21 equivalence into `ConfluenceResult`, then inhabit immutable `confluenceTheorem`. | O18, O21 | **S.** `confluenceResultFromCanonicalCapital` is already a checked complete constructor. |
| **O23** | Add regressions/countermodels, sequential Idris checks, adversarial interface reviews, package validation, documentation, and a release-only branch excluding all research holes. | O1–O22 | **M–L.** Validation is routine but multiple XL boundaries require independent review; cold-build debt remains separately paused. |

## 4. Dependency phases and provisional budget

The following are **critical-path bands**, not independent additive contracts.
RAR case work created in one phase is reused in later phases, while adversarial
review can overlap documentation and bounded algebra. They are calibrated to
the round-1 50–90 recommendation.

| Phase | Obligations | Critical work | Provisional band |
|---|---|---|---:|
| A | O1–O2 | replay algebra and generic independence | 6–12 |
| B | O3–O6 | A/A, A/O, O/O diamonds and suffix replay | 8–14 |
| C | O7–O9 | scanners, maximal selection, enriched D72 step | 6–12 |
| D | O10–O11 | recursion and cumulative exact-generation accounting | 7–14 |
| E | O12–O15 | closing-free shape, Lemma-68/70 capital, support order/transport | 6–12 |
| F | O16–O18 | input/generated accounting and one-trace canonical sorting | 8–15 |
| G | O19–O21 | mapped orders, independent canonical convergence, endpoint composition | 10–18 |
| H | O22–O23 | outer theorem, regression/review/release validation | 2–5 |

Raw phase maxima overlap in shared replay infrastructure; plan **50–90 total**,
not the arithmetic sum. Re-estimate after O2, O5, O9, O15, and O21. A gate that
requires a public statement change invalidates the range.

## 5. Mathematical gates and architecture decisions

The previous plan incorrectly described prove-or-refute obligations as
“supervisor decisions.” They are now explicit gates:

| Gate | Pass criterion | Failure consequence |
|---|---|---|
| **G1 generic independence** | O2 transports both Definition-60 fields from `RelationalReplayCorrespondence`. | Choose between enriching RAR/D72 internal witnesses further or abandoning replay-based Path A for a direct canonical evaluator. Public premise changes require a new statement review. |
| **G2 O/O transposition** | Every source-sensitive yielded insertion pair either commutes with checked freshness/licensing or is never required by the certified sorting algorithm. | Redesign canonical sorting/block representation; do not weaken freshness or registration discipline. |
| **G3 activation-tag elimination** | O12 proves every retained supported open episode uses only L-Begin/L-Iter/L-Finish plus yielded registration. | Produce counterexample and trigger canonical-statement/algorithm re-review. |
| **G4 support-index transport** | O15 converts reduced endpoint support order and placement to exact original endpoint indices. | Strengthen internal endpoint transport; if impossible, request public `CanonicalSchedule` statement re-review. |
| **G5 vestigial composition** | O21 consumes actual schedule fields and fixed accepted renaming to return exact original-final equivalence. | Strengthen internal scanner/composition records; public record repair only after counterexample and approval. |

Actual architecture choices requiring supervisor approval after a failed gate:

1. continue enriched relational replay versus switch to a direct/canonical
   evaluator;
2. keep Path-A sorting versus choose an algorithm avoiding unsafe O/O crossings;
3. introduce additional internal reduction/schedule witnesses versus reopen a
   public statement; and
4. allocate another Lemma-72-scale budget after the next estimate gate.

The fixed accepted `SameOrchestrationModuloGenerated` decision remains resolved.
Bare-input Lemma 56 and the registered cold-build module split remain separate,
unreleased debt.

## 6. Round-1 required-change closure matrix

| # | Required change | Revision-2 response |
|---:|---|---|
| 1 | 23-count and 50–90 estimate | Corrected above; O1–O22 proof, O23 validation; old range withdrawn. |
| 2 | Strengthen `ClosingFreeReduction` | Added same external inputs, generic replay correspondence, deletion history alignment, cumulative endpoint, and exact canonical registration accounting. |
| 3 | Generic replay independence/internal D72 companion | Added `RelationalReplayCorrespondence`, generic transport spike, and enriched `DeletionChainStep`; deletion instantiation now requires the companion rather than claiming public-result universality. |
| 4 | Full recursive premise re-establishment | Added shared `ReplayInvariantBundle` including alignment, discipline, totality, quiet/no-failure, reached-from-empty ingredients, provenance/ranks, both acyclicity results, support equality, and independence. |
| 5 | Tags/outcomes and checked adjacent suffix result | Added moved tag/branch fields, iterator-stage outcome correspondence, quotient endpoint algebra, and `AdjacentSwapResult` with complete next premises. |
| 6 | O/O diamonds | Added source-sensitive `OrchestrationSwapSafety` and `orchestrationOrchestrationDiamondSpike`, including generation scan/freshness/licensing conditions; G2 blocks Path A on counterexamples. |
| 7 | Original→reduced support transport/exact schedule constructor | Added `CanonicalSupportTransport`, strengthened sorted output, orchestration accounting, and exact `oneTraceCanonicalScheduleSpike`. |
| 8 | Mapped paths/comparability and certified swaps | Added support-path forward/backward fields and `CertifiedIncomparablePermutation` of adjacent incomparable swaps. |
| 9 | Cross-trace independence | Added `IndependentCanonicalSchedule` carrying both original and transported canonical independence; convergence consumes it explicitly. |
| 10 | Exact renaming composition interface and coupling | Added `CanonicalEndpointBridge`, `canonicalSchedulesToOriginalEndpointSpike`, and `CoupledComposedModuloVestigialEndpoint.composedCurrentUsesBijection`. |
| 11 | External/generated accounting algebra | Added external reflexive/transitive spikes, per-deletion/sorting witnesses, `OneTraceOrchestrationAccounting`, and exact generated correspondence indexed by the composed endpoint list. |
| 12 | Mathematical gates/real decisions | Section 5 now has pass/fail criteria and explicit architecture escalation choices. |

## 7. Validation protocol and release boundary

During revision 2, each of the five modified spike modules must be elaborated
one Idris process at a time against an exact copy of `src/`. Hole-bearing
research checks establish API/index compatibility only. Release package checks
must continue to build only `src/`; no `research/CP5*` module may enter
`dgamma.ipkg`.

Before proof implementation is authorized, round-2 adversarial review must
verify:

- every producer record supplies the next consumer's exact indices;
- no stage infers independence, external inputs, registration accounting, or
  support transport from endpoint relatedness alone;
- O/O conditions cover yielded insertions in `ActorLifecycleOnly` blocks;
- canonical/current bijections are propositionally coupled; and
- the exact accepted `CanonicalSchedule` and original-final
  `SystemEquivalentByRenamingModuloVestigial` types are returned.

An eventual release must recreate accepted interfaces as total, hole-free
`src/DGamma/CP5*` modules, pass sequential targeted checks, adversarial review,
full package validation, escape-hatch scans, and exclude all research artifacts.
Theorem 73 remains unproved after this scoping revision by design.
