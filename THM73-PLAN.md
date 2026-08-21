# Theorem 73 (Confluence) — CP5 scoping plan

Branch: `cp5-thm73-scoping`  
Scope: research only. No proof implementation in this shift. The accepted public
statements in `src/DGamma/CP3.idr` remain immutable, and the registered
validation-debt split remains paused.

The files under `research/DGamma/` are deliberately non-release spike modules.
They contain named holes, are not listed in `dgamma.ipkg`, and must never merge
to `main`. Their purpose is to establish that the proposed intermediate types
elaborate against the current release-clean API.

## Executive estimate

Recommended planning budget: **34 engineering shifts**, with an honest range of
**24–50 shifts**. The lower end assumes that the Lemma-72 relational replay
machinery generalizes cleanly to independence transport and adjacent swaps. The
upper end covers one internal-interface strengthening (without changing the
public theorem) and the full 8-action replay/canonical sorting case explosion.
A public statement repair would invalidate this estimate and requires a new
supervisor decision; no such repair is currently recommended.

The critical path is not the final `ConfluenceResult` constructor. It is:

1. preserving trace-indexed `TraceIndependent` across each relational deletion;
2. selecting a maximal closing episode and re-establishing every Lemma-72
   premise on the replayed survivor;
3. turning Lemma 71's effect quotient into operational adjacent swaps and then
   replaying the suffix relationally; and
4. composing generation/current-name renamings with the union of exact
   vestigial classifications.

## 1. Statement analysis

### 1.1 Paper theorem

Paper Theorem 73 has two conclusions under a single quiet, failure-free,
pairwise-independent, total trace:

1. **Canonical form.** Delete every closing episode, move orchestration to its
   legal canonical positions, and make the remaining open episodes contiguous
   in a linearization of support/precedence.
2. **Confluence.** Any two traces with the same orchestration inputs reduce to
   equivalent canonical endpoints after fresh-name renaming.

The paper relies on Lemmas 68–72 and informally invokes Lemma 56 for the
fresh-name tree bijection. Its proof uses three inductions: closing-episode
deletion, orchestration movement, and support-ordered episode sorting.

### 1.2 Accepted CP3 specialization

`confluenceTheorem` is a two-trace finite-host statement. Each side carries the
same repaired premises already accepted for CP4: aligned dictionaries,
registration discipline, totality on actual trace boundaries, quiet/no-failure,
and corrected trace independence. `SameOrchestrationModuloGenerated` supplies
the fixed finite-host version of paper Lemma 56.

| Accepted machinery | Readiness | Analysis |
|---|---|---|
| `RegistrationGenerationBijection` | statement-ready; executable identity; composition proved in spike | Correctly separates repeated births of one raw name. It is the historical renaming, not the current endpoint name map. |
| `ExternalRootBirthCorrespondence` | statement-ready | Couples exact external-root birth ordinals and preserves external input order. It is intentionally stronger than a raw action-list equality. |
| `DeletedClosingRegistration` | statement-ready | Classifies a generated birth in a parent activation that later unloads. Its current evidence is sufficient as an accepted scanner premise, though deriving it during repeated deletion is nontrivial. |
| `RegistrationTraceCorrespondence` / `RegistrationCorrespondenceByGeneration` | statement-ready | Handles parent-local positions, cross-parent interleaving, surviving births, and discarded closing births. Constructors are available; general construction and composition are missing. |
| `VestigialEndpointGeneration` | statement-ready; executable checker | Gives the exact Lemma-57 endpoint shape and discarded-generation stamp. The missing theorem is that every unmatched current discarded birth satisfies the checker. |
| `CurrentEndpointRenaming` | statement-ready | Separates current raw-name bijection from historical generation renaming and permits omission only through full vestigial evidence. In the accepted theorem it is bundled in `sameInputs`. |
| `SystemEquivalentByRenamingModuloVestigial` | statement-ready | Precisely states exact ambient/table equivalence under renaming and full control equivalence except for trace-derived vestigials. Reflexive examples exist; transitivity/composition is absent. |
| `CanonicalRegistrationCorrespondence` | statement-ready | Correctly validates every retained generated birth and exact-generation withdrawal inside a one-trace canonical reduction. Construction/composition is absent. |
| `CanonicalSchedule` | statement-ready | Contains root-input placement, support linearization, one block per supported actor, block order, lifecycle coverage, endpoint withdrawal, and registration accounting. No constructor theorem exists. |
| `ConfluenceResult` | statement-ready | Outer assembly is already sufficient. `confluenceResultFromCanonicalCapital` in the cross-trace spike is a complete checked constructor proof. |

### 1.3 Fixed premise decision and optional paper-strength debt

Supervisor decision for this plan: **keep `SameOrchestrationModuloGenerated` as
fixed accepted capital; do not change the statement**. It already bundles the
generation bijection, `RegistrationCorrespondenceByGeneration`, and
`CurrentEndpointRenaming`. Therefore Theorem 73 need not derive paper Lemma 56
from bare same-orchestration inputs.

Named optional strengthening debt, also registered in `NOTES.md`:

> **Paper Lemma 56 derivation — bundled structural premise.** Mechanize the
> generation bijection, registration correspondence, and current endpoint
> renaming from bare same-orchestration inputs after Theorem 73. This restores
> the paper's stronger input surface but does not gate confluence.

This finite-host deviation belongs in the eventual errata/clarifications
letter.

### 1.4 Missing statement-level intermediates

No public CP3 result type currently needs repair, but these internal interfaces
are missing:

- relational local diamonds for paper activation/activation and
  activation/orchestration transpositions;
- `TraceIndependent` preservation for newly replayed survivor transitions;
- a finite maximal-closing selector producing all Lemma-72 local premises;
- cumulative exact-generation deletion/withdrawal composition;
- extraction of one interleaved open episode for every final supported actor;
- a finite `LinearizesSupport` constructor;
- block-bubbling/suffix-replay and sorting results;
- registration-correspondence and vestigial-aware endpoint composition; and
- cross-trace matching of canonical support orders and episode blocks.

## 2. Proof obligations in dependency order

Capital abbreviations used below:

- **D72** — checked `deletionTheoremProof`, `DeletionResult`, exact generation
  filtering, post-close fold, and withdrawal join.
- **RAR** — `RelationalActionReplayer` and its exhaustive eight-action
  `replayRelatedAction` dispatcher.
- **GEN** — generation stamping/scanners, exact reissue discipline,
  `RegistrationTraceCorrespondence`, and vestigial checker.
- **L71Q** — `activationEffectTransposition`, selected-effect transposition,
  recovery/quotient relations, and ordered relational boundaries.

Difficulty: S (small), M (bounded), L (large), XL (critical/multi-shift).

| ID | Concrete obligation | Reusable capital | Grade | Specific risk |
|---|---|---|---|---|
| O1 | Add internal trace/list algebra: `traceLength`, append lengths, action-count decrease, relation reflexivity/transitivity, and ordinary name/generation bijection composition. | GEN, L71Q | S–M | Proof-bearing `Transitions` indices can make otherwise elementary append rewrites expensive. |
| O2 | Prove **TraceIndependent preservation under relational replay**: every actual, continuation, and yielded generator of `survivingTrace result` corresponds to a respectful generator/transformation in the original independent universe. | D72, RAR, GEN, L71Q | **XL** | Occurrence restriction is insufficient: replay creates new transitions with new source states. This gates every Path-A iteration after the first. The public `DeletionResult` may need a stronger internal companion witness, but no public change. |
| O3 | Prove paper Lemma-71(1) local diamonds for L-Begin and L-Advance tagged L-Iter/L-Finish at distinct actors, given early applicability of the second step. | RAR, L71Q, actual effect frames | **XL** | Effect commutation is available only up to `EffectStateRelated`; control edits and exact branch/outcome preservation require per-tag dispatch. |
| O4 | Prove Lemma-71(2) activation/orchestration diamonds, including child O-Insert's foreign-parent condition, root inputs, O-Retire, and O-Remove. | RAR, L71Q, registration discipline | L–XL | O-Insert freshness/parent-yield guards are source-sensitive; moving a generated insertion across the licensing parent would be unsound. |
| O5 | Generalize local diamonds to an adjacent-swap result that replays the untouched suffix relationally and preserves discipline/well-formedness. | RAR, L71Q, O3–O4 | XL | Raw state equality is unavailable because tables and accumulators are functions. Every splice must carry ordered controls/effects and rebuild a checked suffix. |
| O6 | Build an executable located-episode scanner/classifier over finite `Transitions`, including open/closed activation boundaries and exact ordinals. | GEN, existing `LocatedClosedEpisode`, `episodes` snapshot helper | L | Current executable `episodes` groups snapshot logs but does not return indexed located episode proofs. |
| O7 | Select a support/parent-maximal closing episode when one exists. Derive `NoDependentClosingEpisode` and show every child registered during it has no open or closing episode. | D72, GEN, Lemmas 68/70, registration ranks | **XL** | Maximality ranges over occurrence-indexed episodes, not just endpoint names; raw-name reissue must not merge activations. |
| O8 | Construct `RegisteredGenerationsDuring`, start scan, outside-selected proof, and `NoRegisteredEpisode` for the selected maximum. | D72, GEN, O6–O7 | L | Generated children may be retired/removed/reissued; all negative evidence must use exact generations and activation-local positions. |
| O9 | Apply D72 once and prove strict `traceLength` decrease. | D72, GEN | S–M | The center filter must expose that both selected boundaries are genuinely removed, not merely related. |
| O10 | Re-establish aligned transitions, registration discipline, initial invariants, quiet/no-failure, totality, and O2 independence on the survivor. | D72, RAR, GEN, O2 | **XL** | Quiet/no-failure and totality are endpoint/control properties under a relation with withdrawn names; they are not direct list restrictions. |
| O11 | Define well-founded delete-all recursion on `traceLength`; accumulate exact withdrawn generations/raw endpoint names. | D72, GEN, O9–O10 | L | The recursive trace has new states, so located episodes and scanners must be rebuilt rather than transported by equality. |
| O12 | Compose `DeletionResult` boundaries into one `CanonicalEndpointRelation` and one `CanonicalRegistrationCorrespondence` from original to closing-free trace. | D72, GEN, L71Q | **XL** | Outside-generation controls use different live environments at each stage; proving vestigial/raw-name union is the central generation-reuse hazard. |
| O13 | From closing-free + quiet + no-failure + Lemma 70, extract exactly one interleaved open episode for every supported actor and no lifecycle step for unsupported actors. | GEN, Lemmas 68/70, installed-trace lemmas | L–XL | There is no located open-episode scanner; L-Divert/L-Raise/L-Leave/L-Unload must be excluded before using only paper activation tags. |
| O14 | Construct a duplicate-free `LinearizesSupport` list by sorting finite current registry names by protocol rank and proving every `SupportPath` ordered. | GEN, Lemma 68, `CP4Support` rank proofs | M–L | Same-rank incomparable names need stable tie-breaking without assuming an order on `name`; registry order can be used only after proving uniqueness/completeness. |
| O15 | Move root orchestration before lifecycle while preserving relative external order; keep generated orchestration after its matched registration. | RAR, O4–O5, registration correspondence | L | `RootInputsBeforeLifecycle` includes root retire/remove as well as births; moving them must not cross surviving lifecycle at the same actor. |
| O16 | Bubble each minimal supported actor's open episode into a contiguous block, including yielded child O-Inserts; recurse over the remaining support list. | RAR, L71Q, O3–O5, O13–O15 | **XL** | Each adjacent swap changes source states and requires relational suffix replay. Parent-generated O-Inserts travel with the block but cannot cross their own licensing step. |
| O17 | Build `LocatedOpenEpisodeBlock`, `BlockBefore`, lifecycle coverage, input placement, no-withdrawal sorting endpoint, and sorting registration correspondence. | RAR, GEN, O16 | L | Dependent decomposition equations and exact registration occurrence accounting dominate elaboration size. |
| O18 | Compose O11–O12 deletion with O17 sorting into one `CanonicalSchedule` for each original trace. | D72, GEN, L71Q | L–XL | `CanonicalRegistrationCorrespondence` composition must preserve exact original birth ordinals while the sorted trace has different ordinals. |
| O19 | Transport support membership and support paths through accepted `CurrentEndpointRenaming`; match root and generated support trees from the bundled registration correspondence. | GEN, accepted `sameInputs`, Lemmas 68/70 | **XL** | Vestigials are intentionally absent from the mapping; they must be excluded from support before using the total raw-name bijection. |
| O20 | Show two canonical support orders differ only by adjacent incomparable blocks; transpose those blocks and align matched registration positions. | RAR, L71Q, O16, O19 | XL | Orders use different raw names and may choose different incomparable tie orders. A list permutation alone is not enough; each swap needs operational replay. |
| O21 | Compose renaming-after-renaming and vestigial classifications; prove exact ambient/table equality and `EndpointFiberRelatedModuloVestigial` for every current name. | GEN, L71Q, O12, O19–O20 | **XL** | Four endpoint cases (related, left vestigial, right vestigial, both vestigial) interact with total name bijections and exact scanner deleted lists. |
| O22 | Assemble two `CanonicalSchedule`s and O21 into `ConfluenceResult`, then inhabit `confluenceTheorem`. | all above | S | Outer assembly is already checked by the cross-trace spike; risk is only implicit-index alignment. |
| O23 | Targeted regressions, adversarial statement review, package validation, docs, and release-only merge (excluding all `research/` holes). | existing CP3/vestigial checks | M–L | Main must remain hole-free; the registered cold-build split stays paused unless separately released. |

## 3. Checked spikes of the five hardest areas

All spikes elaborate with Idris 2 v0.8.0. Named holes are expected research
artifacts, not proofs.

### 3.1 Local operational diamonds

File: `research/DGamma/CP5ConfluenceLocalDiamondSpike.idr`

Checked types:

- `PaperActivationStep` restricts the host to L-Begin and L-Advance tagged
  L-Iter/L-Finish, exactly matching paper Lemma 71.
- `LocalRelationalDiamond` returns swapped checked transitions plus ordered
  control and effect relations; it does not demand forbidden equality of
  function-valued state.
- `activationActivationDiamondSpike` carries the paper's explicit early-
  applicability premise.
- `activationOrchestrationDiamondSpike` states the generated-child foreign-
  parent condition.

Finding: the effect quotient alone is insufficient for an indexed trace splice.
The practical theorem must return a concrete swapped endpoint and feed it to RAR
for suffix replay.

### 3.2 Repeated Lemma-72 deletion and induction measure

File: `research/DGamma/CP5ConfluenceDeletionChainSpike.idr`

Checked types:

- `traceLength` is a simple structural measure.
- `CanonicalizationPremises` exposes everything that must survive one deletion.
- `DeletableClosingEpisode`, `DeletionChainStep`, and `ClosingStepChoice` state
  maximal selection and strict decrease.
- `ClosingFreeReduction` states cumulative endpoint output.
- `checkedDeletionSubroutine = deletionTheoremProof` checks that D72 plugs into
  the proposed chain without an adapter.
- `traceIndependentAfterDeletionReplaySpike` states the newly identified
  first-class gate.

Finding: `restrictTraceIndependent` cannot prove the survivor field because
`survivingTrace` consists of reconstructed transitions at new source states.
Independence transport is XL and must be solved before investing in the maximal
selector/recursion proof.

### 3.3 Renaming composition and vestigial union

File: `research/DGamma/CP5ConfluenceRenamingCompositionSpike.idr`

Checked/proved:

- `composeGenerationBijection` is fully proved.
- `composeNameBijection` is fully proved.
- `ComposedModuloVestigialEndpoint` and
  `composeModuloVestigialEndpointSpike` state scanner/endpoint transitivity.

Finding: bijection algebra is S; scanner composition and the union of discarded
current generations are XL. `SystemEquivalentByRenamingModuloVestigial` is
expressive enough; no statement change was exposed.

### 3.4 Closing-free shape, support order, and canonical sorting

File: `research/DGamma/CP5ConfluenceCanonicalSortSpike.idr`

Checked types:

- `LocatedInterleavedOpenEpisode` captures an installed open suffix before
  sorting.
- `ClosingFreeTraceShape` states supported-open/unsupported-absent structure.
- `SupportOrderingCapital` packages the required finite topological list.
- `SortedClosingFreeTrace` contains every sorting-only field needed downstream.
- `closingFreeTraceShapeSpike`, `supportOrderingSpike`, and
  `sortClosingFreeTraceSpike` state the three internal joins.

Finding: support well-foundedness is already proved, but no executable theorem
constructs `LinearizesSupport`. More importantly, no located open-episode
scanner exists. Those are independent prerequisites before block bubbling.

### 3.5 Cross-trace canonical matching and outer assembly

File: `research/DGamma/CP5ConfluenceCrossTraceSpike.idr`

Checked types/proof:

- `MappedCanonicalSupportOrders` avoids asking two valid topological lists to be
  equal.
- `canonicalSupportOrdersMatchSpike` consumes the fixed accepted bundled
  registration/current-renaming premise.
- `canonicalSchedulesConvergeSpike` states the exact remaining endpoint bridge.
- `confluenceResultFromCanonicalCapital` is fully proved.

Finding: `ConfluenceResult` is outer-constructor ready. The cross-trace debt is
support/block matching and vestigial-aware endpoint proof, not result packaging.

### Spike statement verdict

The five spike areas type cleanly and their premises appear derivable from the
accepted capital. No direct contradiction or forced public statement change was
found. Two internal statements need early adversarial attention:

1. `traceIndependentAfterDeletionReplaySpike` may require enriching the
   **internal** Lemma-72 fold result with generator correspondence; public
   `DeletionResult` stays unchanged.
2. The closing-free extractor must prove that every remaining open episode uses
   only L-Begin/L-Iter/L-Finish plus yielded registrations. If a valid quiet,
   no-failure, closing-free trace retains L-Divert/L-Raise/L-Leave/L-Unload, the
   transposition scope and possibly the accepted canonical machinery must be
   re-reviewed before proof work continues.

## 4. Recommended execution order and shift budget

| Phase | Work | Expected shifts |
|---|---|---:|
| A | Relation algebra, generator correspondence, O2 independence transport | 4–8 |
| B | Lemma-71 local diamonds and relational suffix swapping | 4–7 |
| C | Located episode scanner, maximal selector, D72 premise derivation | 4–8 |
| D | Delete-all recursion and cumulative generation/endpoint composition | 4–7 |
| E | Closing-free structure and finite support linearization | 3–5 |
| F | Root/generated input placement and support-ordered block sorting | 4–8 |
| G | Canonical registration composition and cross-trace convergence | 4–8 |
| H | Outer assembly, regressions, independent review, validation, docs | 2–4 |

The ranges overlap because capital created in A/B will shorten D/F. Recommended
hard gate order:

1. **Prove or refute O2 first.** Do not begin the full delete-all grind until
   survivor independence is available.
2. Prove O3–O5 local swaps next; run small two-actor regressions for every tag.
3. Build O6–O8 episode selection and only then call D72 recursively.
4. Finish one-trace `CanonicalSchedule` completely before starting cross-trace
   work.
5. Use the accepted bundled Lemma-56 premise directly in O19–O21.
6. Keep all main statements immutable and require an adversarial review at each
   XL interface boundary.

## 5. Expected supervisor decisions

The following are decision points, not permission to change statements:

1. **Resolved:** keep rich `SameOrchestrationModuloGenerated` as fixed accepted
   capital. Track bare-input paper Lemma 56 as optional post-Theorem-73 debt.
2. **If O2 fails:** choose between strengthening only the internal Lemma-72
   replay witness (recommended) or revisiting Definition-60/confluence premises.
   Any public change requires explicit approval and a new adversarial round.
3. **Activation-tag scope:** confirm that closing-free quiet/no-failure traces
   eliminate L-Divert/L-Raise/L-Leave/L-Unload before canonical sorting. A
   counterexample would be a statement-level tension.
4. **Maximality order:** confirm the host selector uses the union of precedence
   and parent/support edges to derive both Lemma-72 negative premises, while
   `NoDependentClosingEpisode` itself remains the accepted precedence clause.
5. **Vestigial composition:** if current `CurrentEndpointRenaming` cannot carry
   the composed discarded-generation union, decide whether an internal scanner
   theorem suffices (recommended) or the accepted record needs repair.
6. **Canonical input interpretation:** retain the accepted
   `RootInputsBeforeLifecycle` reading, which includes root retire/remove as well
   as root births. Report any same-actor obstruction rather than weakening it.
7. **Paper clarification:** record the explicit-registration one-head/many-child
   over-approximation and bundled Lemma-56 premise in the eventual authors
   letter; neither gates the finite-host theorem.
8. **Validation:** the cold-build module split remains paused and must not be
   mixed into CP5 unless separately released.

## Release boundary

Nothing in `research/DGamma/` may merge to main. Eventual implementation must
restate the accepted spike interfaces in hole-free `src/DGamma/CP5*` modules,
check each module with one Idris process at a time, pass adversarial review, and
remove or exclude every research artifact before release. Theorem 73 remains
unproved after this scoping branch by design.
