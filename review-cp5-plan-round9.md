# Theorem 73 scoping plan — adversarial review round 9

- Reviewer role: fresh-context adversarial reviewer
- Target branch/commit: `cp5-thm73-scoping` / `fc7d2b2`
- Immutable production target: `src/DGamma/CP3.idr` blob `2c697e532e83989de8591fa6a4378747c6a501c0`
- Review date: 2026-03-10

## Probe log

### Probe 1 — immutable production baseline and worktree

- **Command:** `git branch --show-current; git rev-parse HEAD; git hash-object src/DGamma/CP3.idr; git diff --stat 34b21c9..fc7d2b2 -- src dgamma.ipkg; git status --short`
- **Result:** Branch `cp5-thm73-scoping`, HEAD `fc7d2b2cd5e8710078bb85faeebc6506eb855ee7`; CP3 blob exactly `2c697e532e83989de8591fa6a4378747c6a501c0`; production diff empty. No tracked worktree changes. Existing untracked `paper/` plus this permitted report.
- **Classification:** note — immutable target and production baseline confirmed.

### Probe 2 — review surface inventory

- **Command:** `find . -maxdepth 2 -type f; find research -type f -name '*.idr'; wc -l THM73-PLAN.md review-cp5-plan-round{1..8}.md`
- **Result:** Five expected research spikes present; plan is 375 lines; all eight prior reports present. No unexpected research Idris module found.
- **Classification:** note — review surface identified.

### Probe 3 — prior-front and revision-9 claim read

- **Command:** `cat review-cp5-plan-round8.md; cat THM73-PLAN.md`
- **Result:** Round 8's exact blockers/majors and round 9's claimed remedies were read. The plan claims exact producer-chain sealing, unified origin coherence, authoritative range injectivity, a raw nontrivial fixture, unchanged 30-hole split, and revised 110–193 sum.
- **Classification:** note — attack targets fixed from the actual prior report and current plan.

### Probe 4 — exact external release tree and toolchain

- **Command:** recreate `/tmp/thm73-review9-probes/release` using `git archive fc7d2b2 src research dgamma.ipkg`; compare CP3 SHA-256; count research modules; `idris2 --version`.
- **Result:** Archived and copied CP3 SHA-256 both `23a9a0d3c8e4475f40ee4c85227683ecea51cc8f94bffc9f001e058f9b54e2ec`; five research modules; Idris 2 version 0.8.0.
- **Classification:** note — all subsequent probes use the exact external release copy.

### Probe 5 — declaration inventory (first attempt)

- **Command:** `wc -l research/DGamma/*.idr; grep -nE <declaration regex> ...`
- **Result:** Research files total 3,803 lines (735/1179/522/686/681), but GNU-style regex contained an empty alternative rejected by BSD grep (`empty (sub)expression`, exit 2).
- **Classification:** note — tooling-only failure; retry required, no interface conclusion.

### Probe 6 — declaration inventory (retry)

- **Command:** `rg -n 'record |data |\\?_rhs|<round-9 type names>' research/DGamma` with output saved to `/tmp/thm73-review9-probes/declarations.txt`.
- **Result:** New declarations exist at the claimed layers: coherence/conversion in LocalDiamond, raw accounting + fixture + sealed capital in CanonicalSort, coordinate injectivity + origin-plan fold in CrossTrace, and bridge consumers in RenamingComposition. Source anchors captured for exact reading.
- **Classification:** note — structural claims exist in code; semantic verification follows.

### Probe 7 — coherence and exact-accounting source audit

- **Command:** inspect LocalDiamond lines 100–242 and CanonicalSort lines 1–390.
- **Result:** Conversion copies the same dependent occurrence payload; coherence is an exact equality. Identity uses `Refl`; composition uses left coherence then `cong (replayActionOrigin left)` of right coherence. Raw laws construct the CP3 tree with `canonicalToOriginal = replayGeneratedRegistrationOrigin`, making strong authentication `Refl`. `OneTraceOrchestrationAccounting` is indexed by exact reduction/order/sorted and authenticates against the definitional composed fold.
- **Classification:** note — claimed internal coherence and strong-tree construction are genuine at these declarations; injectivity/forgery attacks still required.

### Probe 8 — fixture and sealed-capital source audit

- **Command:** line-numbered inspection of CanonicalSort lines 390–735.
- **Result:** The fixture constructor receives two actual located sorted births, exact singleton endpoint withdrawal, equality to reduction withdrawal list, external equality, distinct mapped original generations, and `CanonicalReplayAccountingLaws`; it does not receive accounting/authentication. The sealed capital carries premise/reduction/order/sorted/support/accounting, a runtime schedule, erased equality to the exact producer schedule, and withdrawal classification. All trusted projections pattern-match the equality as `Refl`; the assembler constructs the producer schedule with `Refl`.
- **Classification:** note — claimed telescope and no-accounting fixture boundary are present. Residual strength/constructibility and propositional-equality attacks remain.

### Probe 9 — five-spike serial elaboration (first attempt)

- **Command:** loop `idris2 --check --source-dir src --source-dir research <each spike>` serially.
- **Result:** Every invocation fails at import lookup (`DGamma.Calculus not found`) because Idris 2 treats repeated `--source-dir` non-additively. No source/type finding.
- **Classification:** note — harness configuration failure; retry with a merged external source root.

### Probe 10 — five-spike serial elaboration (merged-root retry)

- **Command:** merge exact `src/DGamma` and `research/DGamma` under external `all/DGamma`, then serially `idris2 --check --source-dir all` each of the five spikes.
- **Result:** Exit 0. Fresh terminal counts: LocalDiamond 31/31, DeletionChain 165/165, CanonicalSort 166/166, CrossTrace 168/168 (including Renaming), and Renaming current. Only pre-existing implicit-binding warnings.
- **Classification:** note — all research interfaces elaborate serially.

### Probe 11 — upstream reality-anchor audit

- **Command:** line-numbered inspection of DeletionChain through `ClosingFreeReduction` and CrossTrace through coordinate injectivity.
- **Result:** A reduction cannot be merely a schedule/map pair: it carries an actual reduced `Transitions`, closing-free proof, same-external witness, relational and coherent occurrence maps, typed deletion classifications, endpoint, aligned history, and CP3 registration accounting. Sorted values carry an actual sorted trace, invariant bundle, exact located blocks/order/range non-alias law, input/lifecycle coverage, endpoint, and registration tree. Coordinate injectivity's same-block cases are constructive addition cancellation; cross cases directly apply the decomposition's range-disjointness in both orientations.
- **Classification:** note — the producer chain is still publicly constructible from evidence, but its fields state substantial trace-indexed reality; any synthetic chain must forge those actual semantic witnesses, not only a correspondence map.

### Probe 12 — tree-only capital clone (first attempt)

- **Command:** `idris2 --check --source-dir all R9TreeOnlyCloneNegative.idr` as expected failure.
- **Result:** Idris rejects the harness path because the probe file itself is outside `all`; the source body was not elaborated.
- **Classification:** note — harness placement failure; retry inside the external merged source root.

### Probe 13 — tree-only capital clone (scope retry)

- **Command:** compile the relocated negative probe.
- **Result:** Probe reaches elaboration but fails first on missing direct imports for `RegistrationProtocol` and a deletion projection, not on the seal.
- **Classification:** note — import-scope failure; add direct producer imports and retry.

### Probe 14 — tree-only capital clone (second scope retry)

- **Command:** retry after importing Calculus and DeletionChain.
- **Result:** Still fails on non-reexported `RegistrationProtocol` and `replayDiscipline` projection visibility. No seal conclusion.
- **Classification:** note — direct Coeffects/LocalDiamond imports required.

### Probe 15 — tree-only capital clone (third scope retry)

- **Command:** retry with Coeffects and LocalDiamond direct imports; then source-search owners of unresolved names.
- **Result:** Remaining names are direct CP3 definitions (`RegistrationProtocol`, `endpointWithdrawnGenerations`), not exported transitively. Probe still has not tested the seal.
- **Classification:** note — add direct CP3 import.

### Probe 16 — tree-only capital clone (fourth scope retry)

- **Command:** retry with direct CP3 import.
- **Result:** Only `DecEq` remains out of scope, causing downstream inference failure. No interface finding.
- **Classification:** note — add `Decidable.Equality` and retry.

### Probe 17 — round-8 tree-only capital clone at new type

- **Command:** compile `R9TreeOnlyCloneNegative.idr` after complete direct imports, expecting failure while replacing only `capitalCanonicalSchedule` and reusing every chain field/proof.
- **Result:** Expected exit 1 exactly at `capitalCanonicalScheduleExact`: Idris cannot solve `capital.capitalCanonicalSchedule = replacement`.
- **Classification:** note — pass negative. Tree-only schedule substitution cannot reuse the seal.

### Probe 18 — round-8 coherent tree+map capital clone at new type

- **Command:** compile `R9CoherentPairCloneNegative.idr`, supplying a replacement schedule, a correspondence coherent with that schedule, and its exact tree authentication while reusing all chain fields.
- **Result:** Expected exit 1 at the schedule seal (`capital.capitalCanonicalSchedule` cannot unify with `replacement`). The coherent alternate map/authentication have no constructor field through which to enter.
- **Classification:** note — pass negative. `replaceCapitalWithCoherentPair` is closed at the capital constructor.

### Probe 19 — bridge and whole-pipeline consumer audit

- **Command:** line-numbered inspection of `ReplayedCanonicalEndpointBridge`, scanner capital, O19/O20 records, and outer assembly.
- **Result:** The bridge accepts sealed capitals, and generation matching explicitly maps source/right births through each capital's derived `canonicalOccurrenceCorrespondence`. `canonicalActorBlockDecomposition` pattern-matches the seal and reconstructs blocks/range law from `capitalSorted`. O19/O20 carry exact capitals through operational folds; outer construction preserves original projected schedules.
- **Classification:** note — the consumer chain references derived producer correspondence end to end; direct constructor probes remain needed.

### Probe 20 — public schedule at bridge

- **Command:** compile `R9PublicScheduleCannotReachBridgeNegative.idr`, placing a `CanonicalSchedule` in the bridge's capital parameter.
- **Result:** Expected exit 1 in the bridge result type: exact mismatch `CanonicalSchedule ...` vs `IndependentCanonicalSchedule ...`.
- **Classification:** note — pass negative. Public schedules cannot enter the bridge.

### Probe 21 — arbitrary propositional (including transported) seal

- **Command:** positive compile of `R9PropositionalSealPositive.idr`, whose constructor accepts an arbitrary proof `schedule = producerCanonicalSchedule ...`, then applies `canonicalOccurrenceCorrespondence`.
- **Result:** Exit 0 at 167/167. The pattern match accepts and eliminates any propositional equality, not only syntactic `Refl` at the call site.
- **Classification:** note — this is normal equality elimination, not a forgery: without an escape hatch, such a proof makes the schedule substitutable for the producer schedule. The seal blocks unequal schedules, not non-normal-form proofs of equality. Residual trust is precisely the producer-chain evidence.

### Probe 22 — whole-boundary proof and producer-fixture search

- **Command:** inspect CrossTrace lines 606–825; search research for `1x1|2x1|2x2|OriginPlan|Fixture|rawTwoBirth|twoBirth`.
- **Result:** `wholeSelectedCoordinateAliasImpossible` directly applies the authoritative cross-range field with exact bounded positions. The origin-plan fold constructs labels recursively. However, no committed 1×1/2×1/2×2 origin-plan producer fixture exists anywhere in research; the only `TwoBirthOneWithdrawal` code is the abstract record/assembler. The search command exits 2 only because an unrelated `*.md` glob was evaluated in the external release directory.
- **Classification:** major — claimed positive producer calibration is not present in the release artifacts; generic definitions alone do not verify constructibility of 2×1/2×2 plans or disjointness producers.

### Probe 23 — exact claimed producer names and constructor-use audit

- **Command:** repo-wide search for `rawTwoBirthOneWithdrawalProducer`, whole-block positive fixture names, and constructor uses of reduction/sorted/fixture/origin-plan/whole records.
- **Result:** `rawTwoBirthOneWithdrawalProducer` is absent. There is no committed round-9 whole-block positive module. `MkClosingFreeReduction` and `MkSortedClosingFreeTrace` have zero uses outside their declarations; `CrossingOriginPlanStep` is only declared and pattern-matched by the fold, never constructed; `MkWholeBlockSwapDerivation` is never used; only the abstract fixture assembler calls `MkTwoBirthOneWithdrawalFixture`.
- **Classification:** major — revision 9 does not contain the claimed nontrivial producers. The fixture path assumes the hard reduction, sorting, and raw replay-law evidence, and the coordinate path has no concrete recursive origin plan.

### Probe 24 — generated→action conversion injectivity (first attempt)

- **Command:** compile a constructor-pattern proof that equality after conversion implies equality of located generated occurrences.
- **Result:** Parser rejects the multiline left-hand side before type checking.
- **Classification:** note — probe syntax failure; retry with direct equality elimination.

### Probe 25 — generated→action conversion injectivity (equality-elimination retry)

- **Command:** retry with `generatedConversionInjective left right Refl = Refl`.
- **Result:** Exit 1: Idris cannot infer `left = right` merely by matching equality of converted values. This does not yet show non-injectivity; explicit source-constructor elimination is required.
- **Classification:** note — retry with constructor patterns on one line.

### Probe 26 — generated→action conversion injectivity (constructor retry)

- **Command:** constructor-pattern both occurrences and match converted equality as `Refl`.
- **Result:** Idris reports the second occurrence's runtime fields already unify with the first through the common trace/index and asks for identical pattern names; only erased proof fields may remain distinct.
- **Classification:** note — evidence supports injectivity; retry with shared runtime patterns.

### Probe 27 — generated→action conversion injectivity (shared-name retry)

- **Command:** use shared runtime pattern names for both source constructors.
- **Result:** Idris 2 does not permit the repeated second binder in this dependent pattern position despite its unification suggestion. Probe-syntax issue, not a counterexample.
- **Classification:** note — retry using wildcards for the second constructor.

### Probe 28 — generated→action conversion injectivity (wildcard retry)

- **Command:** wildcard the second occurrence's runtime fields but name its erased proofs.
- **Result:** Equality also unifies the second erased action proof with the first; named proof binder is rejected as redundant.
- **Classification:** note — retry with all second fields wildcarded.

### Probe 29 — generated→action conversion is injective

- **Command:** positive compile of `R9GeneratedConversionInjectivePositive.idr` with constructor elimination and all second fields wildcarded.
- **Result:** Exit 0 at 32/32. Equality of converted located action occurrences forces equality of the specialized generated occurrences (including dependent location payload; erased proofs are irrelevant).
- **Classification:** note — pass. The conversion does not admit same-action-type occurrence aliasing.

### Probe 30 — generated-only retarget (first attempt)

- **Command:** compile `R9RetargetGeneratedOriginsNegative.idr`, retaining action half/tag/coherence while substituting a generated-origin function.
- **Result:** Probe type omitted explicit `{child,parent,component}` binders on the ordinal premise; failure occurs before the intended constructor field.
- **Classification:** note — harness binder failure; retry with a fully dependent ordinal telescope.

### Probe 31 — generated-only retarget rejected by coherence

- **Command:** retry `R9RetargetGeneratedOriginsNegative.idr` with the complete ordinal premise.
- **Result:** Expected exit 1 at the coherence field, before the ordinal field: old `replayGeneratedRegistrationOrigin occurrence` cannot unify with `alternate occurrence`.
- **Classification:** note — pass negative. Generated-only origin retargeting is closed.

### Probe 32 — laundering moved into producer-chain occurrence fields

- **Command:** positive compile of `R9UpstreamOccurrenceMapClonePositive.idr`, replacing only `reductionOccurrenceCorrespondence` in a `ClosingFreeReduction`, or only `sortingOccurrenceCorrespondence` in a `SortedClosingFreeTrace`, while reusing every other field.
- **Result:** Exit 0 at 167/167. Both producer records publicly store a free coherent occurrence correspondence with no equality to their relational replay, deletion result/history/accounting, finite swap derivation, or any executable fold. All endpoint, registration-tree, block/range, and premise evidence reuses unchanged.
- **Classification:** blocker — the seal moves trust one level up. `canonicalOccurrenceCorrespondence` is definitionally derived from the carried chain, but the carried reduction/sorting occurrence maps themselves are caller-replaceable and only satisfy the weak `ActionRegistrationReplayCorrespondence` laws. The plan's claim that the chain is producer-authentic is stronger than its types.

### Probe 33 — raw replay laws to sealed capital (first attempt)

- **Command:** compose `assembleOneTraceAccountingFromReplay` with `assembleIndependentCanonicalSchedule` in `R9RawLawsCapitalPositive.idr`.
- **Result:** Exit 1 only because opaque projection reduction does not identify the caller's `endpoint` with `accounting.accountedEndpoint` for the withdrawal-classifier argument.
- **Classification:** note — index-normalization issue; retry by constructing the accounting record transparently inside the capital constructor.

### Probe 34 — raw replay laws to sealed capital (transparent retry)

- **Command:** manually construct accounting/capital with a named local tree.
- **Result:** Exit 1 because `replayConstructedTreeAuthentication` unfolds to the canonical tree expression and Idris does not identify it with the opaque local `tree` binder.
- **Classification:** note — local definitional-opacity issue; inline tree/authentication exactly as the checked source assembler.

### Probe 35 — raw replay laws to sealed capital (inlined tree retry)

- **Command:** inline the canonical tree/authentication while retaining a local accounting binder.
- **Result:** Authentication now elaborates, but classifier indexing still cannot reduce through the local accounting binder.
- **Classification:** note — final retry will inline the accounting constructor in the capital field and producer schedule.

### Probe 36 — caller-selected producer maps reach sealed capital via raw laws

- **Command:** final positive compile of `R9RawLawsCapitalPositive.idr`, inlining the checked tree/accounting constructors and the sealed producer schedule.
- **Result:** Exit 0 at 167/167. Any carried reduction/sorted values—including the occurrence-map clones from Probe 32—reach `IndependentCanonicalSchedule` once the caller supplies ordinary `CanonicalReplayAccountingLaws`, endpoint/external equalities, support transport, and required deleted-generation classification. No executable deletion/sorting derivation or equality tying occurrence maps to one is required.
- **Classification:** blocker-supporting — the capital seal authenticates internal consistency with caller-supplied producer records, not provenance from actual deletion/sorting folds. Raw laws are substantial but are exactly CP3 accounting facts over the selected map; they do not connect it to operational replay.

### Probe 37 — authenticated bridge actual-direction constructor (first attempt)

- **Command:** compile `R9BridgeActualDirectionPositive.idr` with every constructor field in the actual replay→canonical-left→original→right direction.
- **Result:** Parser reports an unclosed parenthesis in the controls premise before elaborating the bridge.
- **Classification:** note — syntax-only failure; correct telescope parentheses and retry.

### Probe 38 — authenticated bridge actual-direction constructor (parenthesis retry)

- **Command:** retry after adding a controls-premise close.
- **Result:** Same parse error; recount shows the controls premise originally had the required five closes, while the nested dependent birth matcher is two closes short.
- **Classification:** note — correct both regions and retry.

### Probe 39 — authenticated bridge actual-direction constructor (second telescope retry)

- **Command:** retry after correcting controls and nested birth-matcher close counts.
- **Result:** Parser still rejects the declaration as a whole. The handwritten duplication of the bridge telescope is too brittle and supplies no semantic value.
- **Classification:** note — replace with a pattern/reconstructor over the exact record, which verifies constructor field orientation without duplicating its type.

### Probe 40 — authenticated bridge constructor orientation

- **Command:** positive compile of the exact-record `R9BridgeActualDirectionPositive.idr` reconstructor.
- **Result:** Exit 0 at 168/168. The constructor preserves the exact replayed-occurrence input and its replay→canonical-left→left-original→right-original birth matcher; no reverse-direction coercion is accepted.
- **Classification:** note — positive bridge boundary remains constructible. This is a constructor-orientation check, not a concrete reachable bridge fixture.

### Probe 41 — bridge wrong source birth

- **Command:** compile `R9BridgeWrongBirthNegative.idr`, returning a caller-selected source birth while using `Refl` for the bridge's required exact replay-origin equality.
- **Result:** Expected exit 1: `replayGeneratedRegistrationOrigin ... replayedBirth` cannot unify with `wrongBirth`.
- **Classification:** note — pass negative. Fixed-correspondence wrong-birth substitution is rejected.

### Probe 42 — bridge wrong accepted generation (first attempt)

- **Command:** compile a generic `Refl` proof for the bridge generation-match equation.
- **Result:** Probe omitted explicit child/parent/component binders, so elaboration fails before the equality.
- **Classification:** note — harness binder failure; retry.

### Probe 43 — bridge wrong accepted generation

- **Command:** retry `R9BridgeWrongGenerationNegative.idr` with complete dependent binders.
- **Result:** Expected exit 1 at `Refl`; an arbitrary right birth generation cannot equal `generationForward renaming` of the left birth.
- **Classification:** note — pass negative. The bridge's accepted generation equation remains substantive.

### Probe 44 — round-8 isolated shifted-start alias

- **Command:** positive compile of `R9IsolatedBlockAliasingPositive.idr`, retargeting the same node label to any other block/position with equal global ordinal (including start 1/pos 1 versus start 2/pos 0).
- **Result:** Exit 0 at 169/169. Isolated `NodeCrossesSourceBlockPosition` remains intentionally aliasable by global-coordinate equality.
- **Classification:** note — expected residual. Soundness depends entirely on the new authoritative selected-block disjointness field, not on the node record itself.

### Probe 45 — whole-boundary alias rejection (first attempt)

- **Command:** externally restate/apply `wholeSelectedCoordinateAliasImpossible`.
- **Result:** Probe lacks a direct `Data.Nat` import for `LTE`; the theorem lookup then cascades as inaccessible.
- **Classification:** note — import-scope failure; retry.

### Probe 46 — whole-boundary shifted-start alias rejected

- **Command:** retry `R9WholeBoundaryAliasRejectedPositive.idr` with `Data.Nat` in scope.
- **Result:** Exit 0 at 169/169. For exact selected blocks and in-bounds positions, an equal global coordinate yields `Void` through the authoritative disjoint-range field.
- **Classification:** note — pass. The round-8 alias is closed at the whole-record consumer boundary, conditional on producing the decomposition invariant.

### Probe 47 — equal-bound and off-by-one coordinate checks (first attempt)

- **Command:** compile `R9CoordinateBoundaryPositive.idr` proving selected starts cannot coincide and one-past-end bounds are impossible.
- **Result:** Equal-start theorem elaborates; Idris does not accept an unconstrained `prf impossible` clause for `LTE 2 1` without first exposing its `LTESucc` constructor.
- **Classification:** note — numeric proof pattern issue; refine constructor pattern.

### Probe 48 — equal selected starts and off-by-one boundaries

- **Command:** retry `R9CoordinateBoundaryPositive.idr` with constructor-refined impossible LTE case.
- **Result:** Exit 0 at 169/169. Distinct selected blocks cannot have equal start coordinates even at position 0, and `position = bodyCount + 1` cannot satisfy the wrapper's `LTE (S position) (S bodyCount)` bound.
- **Classification:** note — pass. Equal-bound and one-past-end aliases are excluded by the stated invariant/bounds, conditional on producer inhabitance.

### Probe 49 — arbitrary-tree strong authentication

- **Command:** compile `R9ArbitraryTreeAuthenticationNegative.idr`, asking the `Refl` producer to authenticate a caller-selected CP3 tree.
- **Result:** Expected exit 1: the constructed replay-origin tree does not unify with `arbitraryTree`.
- **Classification:** note — pass negative. Definitional `Refl` authentication is restricted to `canonicalRegistrationTreeFromReplay`, not arbitrary trees.

### Probe 50 — fixture accounting to sealed O18 capital

- **Command:** positive compile of `R9FixtureToSealedCapitalPositive.idr`, feeding `twoBirthOneWithdrawalAccounting fixture` directly to `assembleIndependentCanonicalSchedule`.
- **Result:** Exit 0 at 167/167. The erased schedule equality is not over-strong: O18 can seal the fixture-produced accounting with `Refl` without normalization trouble.
- **Classification:** note — pass at the abstract fixture boundary. It does not cure Probes 22–23: no actual reduction/sorted/two-birth fixture or raw laws are constructed in the release.

### Probe 51 — exact named-hole inventory

- **Command:** Python regex scan of all five research modules for unique `?*_rhs` and every question-mark identifier.
- **Result:** Exact split 6 canonical / 4 cross / 10 deletion / 8 local / 2 renaming = **30**. No extra question-mark identifier.
- **Classification:** note — hole-count claim passes exactly.

### Probe 52 — forward/reverse O1–O23 reconciliation

- **Command:** inspect every hole declaration/output and map it in both directions against the plan table.
- **Result:** Exact mapping holds: O1 = same-external refl/trans, relational-endpoint refl/trans, modulo composition (5); O2 = two independence transports (2); O3=AA (1); O4=AO/OA (2); O5=OO (1); O6=suffix+block (2); O7–O12 one each; O13=0; O14–O18 one each; O19=support match+selector (2); O20=convergence (1); O21=left/right scanner induction+endpoint composition (3); O22=0; O23=0. Strengthened outputs are present for O1 coherence record, O16 exact accounting, O17 range law/fold, O18 sealed chain, and O20 derived-map consumers.
- **Classification:** note — syntactic hole/O-map reconciliation passes. Probe 32 identifies a strength defect inside O16/O17/O18 outputs rather than a hidden hole.

### Probe 53 — phase arithmetic and mandatory gates

- **Command:** independently sum A 6–12, B 23–40, C 10–18, D 10–19, E 7–13, F 18–32, G 34–54, H 2–5; search all three mandatory gate phrases.
- **Result:** Exact sum **110–193**; all three gates present.
- **Classification:** major — arithmetic passes, but grade credibility fails: B/F claimed producer calibration artifacts are absent (Probes 22–23), and F/G do not charge repair of caller-replaceable upstream occurrence maps (Probes 32/36).

### Probe 54 — exact external production build

- **Command:** `idris2 --build dgamma.ipkg` in the exact archived release tree.
- **Result:** Exit 0, terminal line `207/207: Building DGamma.CP4ProgressProof`; only existing implicit-binding warnings.
- **Classification:** note — exact 207/207 production build passes outside the repo.

### Probe 55 — escape, reachability, immutability, and repository hygiene

- **Command:** scan `src/`/package for named holes, `believe_me`, `assert_total`, `%default partial`, postulate declarations; scan package for research reachability and research for non-hole escapes; recheck CP3 blob, baseline source diff, tracked/index state.
- **Result:** All scans empty. CP3 blob exact; `git diff 34b21c9..fc7d2b2 -- src dgamma.ipkg` exit 0; tracked worktree count 0; staged count 0. Only pre-existing untracked `paper/` and this permitted report.
- **Classification:** note — hygiene pass.

### Probe 56 — three concrete scanner orderings (first attempt)

- **Command:** external eliminator over all six concrete scanner exactness theorems.
- **Result:** First three theorems are single whole-index equalities, not equality pairs; probe incorrectly patterns them as `(Refl, Refl)`.
- **Classification:** note — harness-shape failure; retry with `Refl` for whole indexes and pairs only for deleted-list projections.

### Probe 57 — three concrete scanner orderings (projection-scope retry)

- **Command:** retry with corrected equality shapes.
- **Result:** Whole-index equalities eliminate, but deleted-list equality projections require a direct CP3 import (`indexedDeletedGenerations` not reexported).
- **Classification:** note — import-scope failure; retry.

### Probe 58 — three concrete scanner orderings (combined elimination retry)

- **Command:** retry with direct CP3 import and nested `Refl` elimination.
- **Result:** Eliminating one whole-index equality rewrites later dependent constants in a way the nested probe cannot normalize. This is a probe-composition issue, not a scanner theorem failure.
- **Classification:** note — consume each proof opaquely without dependent rewriting.

### Probe 59 — three concrete scanner orderings (opaque consumer first attempt)

- **Command:** compile generic equality consumers around all six scanner theorems.
- **Result:** Parser rejects the overly implicit consumer declaration.
- **Classification:** note — make universe/value/proof binders explicit and use `Unit`.

### Probe 60 — three concrete scanner orderings (explicit erased-binder retry)

- **Command:** retry consumers with explicit quantity-zero binders.
- **Result:** Idris parser rejects this binder syntax in the local helper signature.
- **Classification:** note — use ordinary total proof consumers; runtime quantity is irrelevant in an external review probe.

### Probe 61 — three concrete scanner orderings (ordinary consumer retry)

- **Command:** retry with ordinary total helper signatures.
- **Result:** Parser rejects the clause because `proof` is reserved syntax in Idris 2.
- **Classification:** note — rename the binder and retry.

### Probe 62 — all three concrete scanner orderings

- **Command:** final compile of `R9ConcreteScannerSuitePositive.idr`, consuming whole-index and deleted-list exactness for target, reordered, and third scanner schedules.
- **Result:** Exit 0 at 168/168. All three scanner orderings retain identical exact final indexes and deleted generation lists.
- **Classification:** note — retained concrete scanner positives pass.

### Probe 63 — generated-child safety retained

- **Command:** positive external application of `generatedChildAtHeadContradictsSafety` in `R9GeneratedChildSafetyPositive.idr`.
- **Result:** Exit 0 at 169/169; a headed generated-child insertion contradicts `NoGeneratedChild` before O20.
- **Classification:** note — retained safety positive passes.

### Probe 64 — coherent occurrence composition

- **Command:** positive external application of `composeActionRegistrationReplayCorrespondence` in `R9OccurrenceFoldPositive.idr`.
- **Result:** Exit 0 at 32/32. Both all-action and generated-origin halves compose in the advertised source→middle→target direction with the coherence proof.
- **Classification:** note — retained occurrence fold passes.

### Probe 65 — one-trace producer pipeline from upstream premises

- **Command:** positive compile of `R9OneTracePipelinePositive.idr`: O10/O11 deletion → O12/O14/O17 sorting → O15 transport → O16 accounting → O18 sealed capital, starting only from `CanonicalizationPremises`.
- **Result:** Exit 0 at 167/167. The strengthened O18 equality is constructible at the intended normalized producer output; no extra downstream premise is required.
- **Classification:** note — end-to-end type composition passes. All hard producers remain holes, and the free-map defect is inside their output records (Probe 32), not a telescope mismatch.

### Probe 66 — full producer/consumer pipeline (first attempt)

- **Command:** compile `R9FullPipelinePositive.idr` from two premise bundles + accepted same-input witness through one-trace capitals, O19/O20/O21, and immutable result.
- **Result:** External helper `oneTracePipeline` defaults private, so the importing probe cannot call it.
- **Classification:** note — probe visibility failure; mark the external helper public and retry.

### Probe 67 — full producer/consumer pipeline

- **Command:** retry `R9FullPipelinePositive.idr` after exporting the external one-trace helper.
- **Result:** Exit 0 at 170/170. From only two `CanonicalizationPremises` and `SameOrchestrationModuloGenerated`, the type-level pipeline composes deletion/sorting/accounting/sealing, O19/O20/O21, original endpoint equivalence, and immutable `ConfluenceResult`.
- **Classification:** note — whole-pipeline telescopes compose. This does not prove hole bodies or repair caller-selectable occurrence provenance.

### Probe 68 — coherent retarget of both action/generated halves

- **Command:** positive compile of `R9RetargetBothOriginsPositive.idr`, replacing action and generated origin functions together while supplying tag, conversion coherence, and ordinal laws.
- **Result:** Exit 0 at 32/32. The correspondence record itself has no stronger operational-origin anchor; a coherent automorphism is accepted. Combined with Probe 32, such a map can replace reduction/sorting occurrence fields without changing their actual traces, endpoints, blocks, or registration trees.
- **Classification:** blocker-supporting — the expected “anchor” stops at free map fields in producer records. The sealed capital derives from those fields but does not authenticate them against an actual deletion/adjacent-swap derivation.

### Probe 69 — actual adjacent-swap occurrence-map clone (first attempt)

- **Command:** compile a clone of `AdjacentSwapResult` replacing only `swappedOccurrenceCorrespondence`.
- **Result:** Probe lacks direct `DecEq`/protocol imports; body not elaborated.
- **Classification:** note — add imports and retry.

### Probe 70 — actual adjacent-swap result accepts replacement occurrence map

- **Command:** retry `R9AdjacentSwapOccurrenceClonePositive.idr` with direct imports.
- **Result:** Exit 0 at 32/32. An `AdjacentSwapResult` can be cloned with an arbitrary coherent `swappedOccurrenceCorrespondence` while reusing exact original/swapped trace decompositions, relational replay, endpoint, premises, and same-input evidence unchanged.
- **Classification:** blocker — this removes the anticipated operational anchor for both-halves retargeting. The origin-plan recursion threads “actual result maps,” but those maps are not tied by type to the actual moved nodes or decompositions.

### Probe 71 — literal duplicate Cartesian key

- **Command:** expected-failure compile of `R9LiteralDuplicateNegative.idr`, attempting to reuse singleton uniqueness for `[x,x]`.
- **Result:** Exit 1; `UniqueKeys [x]` cannot be supplied where the duplicate construction needs the tail proof/freshness structure.
- **Classification:** note — retained literal-duplicate negative passes.

### Probe 72 — zero-node whole-block derivation

- **Command:** expected-failure compile of `R9ZeroNodeNegative.idr`, placing `FiniteAdjacentSwapDone` in the required nonempty family.
- **Result:** Exit 1 with exact finite-vs-nonempty family mismatch.
- **Classification:** note — retained zero-node negative passes.

### Probe 73 — alternate origin-plan root (first attempt)

- **Command:** expected-failure compile reindexing an origin plan from an arbitrary source-to-source map to the exact identity root.
- **Result:** Probe omitted the implicit target/derivation telescope, so Idris cannot bind `target` before reaching root equality.
- **Classification:** note — harness index failure; bind target and derivation explicitly.

### Probe 74 — alternate origin-plan root (block-index retry)

- **Command:** retry with explicit target and finite derivation.
- **Result:** Located left/right block indices remain underconstrained in the probe signature.
- **Classification:** note — bind actor names and exact block types, then retry.

### Probe 75 — alternate origin-plan root (DecEq scope retry)

- **Command:** retry with explicit blocks.
- **Result:** `DecEq` is out of direct scope. Idris anomalously returns process status 0 despite printing the declaration error; the wrapper correctly treats this as an invalid probe.
- **Classification:** note — add `Decidable.Equality`; do not use this run as evidence.

### Probe 76 — arbitrary origin-plan identity-root substitution

- **Command:** final expected-failure compile of `R9AlternateOriginRootNegative.idr` with complete direct imports and indices.
- **Result:** Exit 1 exactly at `alternate` versus the fully reduced identity `MkActionRegistrationReplayCorrespondence ...`.
- **Classification:** note — retained identity-root negative passes.

### Probe 77 — wrong occurrence relation at bridge (first attempt)

- **Command:** expected-failure compile reindexing a bridge under an alternate replay occurrence correspondence.
- **Result:** Direct `DecEq` scope missing; Idris again prints a declaration error with status 0, so run is invalid.
- **Classification:** note — add direct Coeffects/Decidable imports and retry.

### Probe 78 — wrong occurrence relation at bridge

- **Command:** final expected-failure compile of `R9WrongOccurrenceBridgeNegative.idr`.
- **Result:** Exit 1 with exact mismatch `originalOccurrences` vs `alternateOccurrences`.
- **Classification:** note — retained wrong-occurrence bridge negative passes for a fixed bridge. The blocker is earlier: actual swap/reduction/sorting records allow their own maps to be replaced before bridge construction.

### Probe 79 — external probe hygiene and expected-failure evidence

- **Command:** scan all 27 `R9*.idr` probes for holes/escapes/partial defaults; enumerate first errors for 11 retained negative outputs.
- **Result:** Probe forbidden-token scan empty. Expected failures are recorded at the intended seal/coherence/birth/generation/tree/duplicate/nonempty/root/occurrence mismatches, not import or parser errors.
- **Classification:** note — adversarial probe harness is hole-free and calibrated.

### Probe 80 — serial positive-probe closure rerun

- **Command:** serially recheck 16 positive probes covering seals, conversion injectivity, upstream map cloning, raw-laws capital, bridge orientation, isolated/whole coordinates, fixture sealing, scanners, safety, folds, one/full pipelines, coherent retargeting, and actual-swap map cloning.
- **Result:** **16/16 passed**; one Idris process at a time.
- **Classification:** note — positive evidence stable after all harness edits.

### Probe 81 — serial negative-probe closure rerun

- **Command:** delete any probe TTCs and serially rerun 11 expected-failure modules, requiring nonzero process status and an Idris `Error:` line.
- **Result:** **11/11 failed as expected** at the intended type boundaries; no anomalous status-0 run remains.
- **Classification:** note — negative evidence stable and fresh.

### Probe 82 — final repository state before findings

- **Command:** recheck branch/HEAD/CP3 blob, tracked/staged counts, status, active Idris processes, and report line count.
- **Result:** Exact branch/HEAD and CP3 blob; tracked 0, staged 0; no Idris/Chez process. Only untracked `paper/` and this report. Probe log has 495 lines before closure.
- **Classification:** note — final hygiene pass.

## Claimed-fix disposition

| # | Round-9 claim | Checked disposition |
|---:|---|---|
| 1 | Sealed producer-chain capital; no coherent clone | **Capital-level seal works, chain-level seal does not.** Public schedule, tree-only clone, and coherent schedule/tree/map clone fail. Any propositional equality is correctly eliminable. But `ClosingFreeReduction`, `SortedClosingFreeTrace`, and even each actual `AdjacentSwapResult` still have freely replaceable occurrence-map fields (Probes 32/70); those selected fields definitionally become the sealed capital map. |
| 2 | Unified action/generated coherence | **Passes locally.** Conversion is injective; identity/composition elaborate; generated-only retarget fails at coherence. A coherent both-halves retarget remains accepted, as expected for the record, but no operational law anchors its action half (Probes 68/70). |
| 3 | Authoritative coordinates and actual recursive fold | **Theorems pass conditionally; producer calibration absent.** Four cases are genuine, shifted alias is rejected at the whole boundary, equal starts/off-by-one fail, and the recursive fold is real. No `CrossingOriginPlanStep` or whole record is ever constructed in release code, so claimed 1×1/2×1/2×2 producer probes are not reproducible. |
| 4 | Raw two-birth/one-withdrawal derivability fixture | **Abstract assembler only.** Strong tree authentication is `Refl` only for the producer tree and seals successfully. `rawTwoBirthOneWithdrawalProducer` is absent; no reduction/sorted value is constructed; the fixture assumes the complete `CanonicalReplayAccountingLaws`, which contain all substantive CP3 registration-accounting obligations. |
| 5 | Exactly 30 holes and 110–193 | **Counts/arithmetic pass.** Exact 6/4/10/8/2 and O-map; exact sum 110–193. Grade credibility fails until producer provenance and missing fixtures are repaired. |
| 6 | Full retained suite | **Core front recreated and passes, but suite artifacts are absent.** Eleven fresh negatives, sixteen fresh positives, scanners, both pipelines, all five spikes, and 207/207 build pass. The named round-8/round-9 test modules are not committed, so the literal claimed suite is not independently reproducible from the release. |

## Numbered findings

1. **blocker — occurrence provenance is still caller-replaceable inside the purported producer chain** (`CP5ConfluenceLocalDiamondSpike.idr:162–195,398–429`; `CP5ConfluenceDeletionChainSpike.idr:369–398`; `CP5ConfluenceCanonicalSortSpike.idr:106–151,555–627`). The new capital seal correctly prevents replacing its runtime schedule or adding a free map at the final constructor. It derives `canonicalOccurrenceCorrespondence` from carried reduction/sorting records. Those records, however, publicly store occurrence correspondences that are not tied to an executable deletion fold, finite adjacent-swap derivation, relational replay, endpoint, or registration accounting. Probe 32 clones reductions and sorted traces while changing only those maps. More decisively, Probe 70 clones an *actual `AdjacentSwapResult`* while changing only `swappedOccurrenceCorrespondence` and reusing both exact trace decompositions and every semantic field. Probe 68 confirms that a coherent both-halves automorphism is accepted; Probe 36 shows selected maps plus ordinary replay laws assemble a sealed capital. Thus the schedule seal authenticates internal consistency with caller-selected producer records, not origin from the actual operational replay. The round-8 laundering moved one level up.

2. **major — the claimed nontrivial two-birth/one-withdrawal producer does not exist** (`CP5ConfluenceCanonicalSortSpike.idr:258–494`). `rawTwoBirthOneWithdrawalProducer` is absent. `MkClosingFreeReduction` and `MkSortedClosingFreeTrace` have no constructor use outside declarations. `assembleTwoBirthOneWithdrawalFixture` accepts those hard values plus two births, endpoint/external equalities, distinct mapped generations, and `CanonicalReplayAccountingLaws`. Those laws are precisely every-original-accounted, injectivity, and withdrawn-removal—the substantive fields used verbatim to build `CanonicalRegistrationCorrespondence`. The checked work is therefore generic record packaging and `Refl` authentication, not a concrete nontrivial deletion/sorting example. O16 remains uncalibrated.

3. **major — coordinate/fold consumer logic is sound but its advertised producer fixtures are absent** (`CP5ConfluenceCrossTraceSpike.idr:45–72,172–237,452–627`). Same-block cancellation and both cross-block cases are real proofs; equal starts, one-past-end, and shifted-start compensation are rejected when the decomposition invariant is available. The fold really creates occurrences/labels from each result. Yet there is no construction of `CrossingOriginPlanStep`, `MkWholeBlockSwapDerivation`, or even `MkActorBlockDecomposition` for a nontrivial concrete trace in the release. The plan's “updated 1×1/2×1/2×2 producer probes” are only prose. Moreover Finding 1 means the result map threaded by the fold is not operationally authenticated.

4. **major — the advertised retained validation suite is not a release artifact.** Prior reports name temporary modules such as `R8WholeBlockTwoByTwoPositive.idr`, but none is tracked at `fc7d2b2`. I recreated the active seal/coherence/coordinate/fixture/bridge fronts: 16 positives pass and 11 negatives fail at intended types. This is substantial evidence but does not make the claimed full suite independently rerunnable. Scoping authorization should require committed research tests or a reproducible script.

5. **major — 110–193 arithmetic is exact but grade readiness is not credible** (`THM73-PLAN.md:296–309`). Phase B claims producer calibration that is absent and consumes unauthenticated actual-swap occurrence maps. Phase F claims a nontrivial producer that only assumes the hard raw laws. Phase G trusts maps selected upstream. The revised range is numerically correct but does not charge another provenance repair and new actual fixtures.

## Positive results / non-findings

- Immutable CP3 blob is exactly `2c697e532e83989de8591fa6a4378747c6a501c0`; production/package diff from `34b21c9` is empty.
- All five research spikes elaborate serially; exact external production build reaches 207/207.
- Production/reachable code has no named holes, `believe_me`, `assert_total`, postulate declaration, or `%default partial`; research is package-unreachable and has no non-hole escape.
- Final capital seal rejects public schedules, tree-only replacement, and coherent schedule/tree/map replacement. Pattern matching correctly supports arbitrary genuine propositional equality; this is not an erasure hole.
- Generated→action conversion is injective. Identity and composition coherence are valid. Generated-only retargeting fails before ordinal evidence.
- Fixed-correspondence wrong birth, wrong generation, and wrong bridge occurrence relation fail.
- Strong `Refl` authentication cannot be applied to an arbitrary tree; the fixture-produced accounting seals without brittle equality normalization.
- Coordinate injectivity covers all four orientations. Isolated arithmetic aliases remain possible, but exact whole-boundary ranges refute them. Equal selected starts and one-past-end bounds are impossible.
- Identity-root substitution, literal duplicates, and zero-node whole swaps fail.
- All three concrete scanner orderings expose the same exact final indexes and deleted lists.
- Generated-child safety, two-step occurrence composition, the one-trace pipeline, and the full two-trace pipeline elaborate.
- Exact hole split is 6/4/10/8/2 = 30 and reverse O1–O23 mapping is exact.

## Residual risks

- All 30 research bodies remain holes by design; interface elaboration is not a proof of Theorem 73.
- No concrete distinct automorphism was instantiated because no nontrivial trace fixture is shipped. The blocker is an interface attack: the maps can be replaced independently of actual replay evidence, and repeated same-action/same-tag occurrences (for example iterator steps) are not excluded by their record types.
- `CanonicalReplayAccountingLaws` may be provable for intended folds, but no checked nontrivial example demonstrates it.
- Disjoint-range laws are asserted output fields of O17/decomposition; no actual producer demonstrates the required arithmetic.
- O/A, O/O, accepted scanner inductions, and universal O19 selection remain XL mathematical gates.
- Static vestigial artifacts remain interfaces rather than reachable O19/O20 executions.
- The named prior external suite is unavailable; recreated probes cover the active front but not every historical temporary file line-for-line.
- Worktree intentionally contains pre-existing untracked `paper/` and this report; tracked paths and index are clean.

## Estimate assessment

- **Arithmetic:** PASS — exact 110–193.
- **Hole reconciliation:** PASS — exactly 30 and exact forward/reverse O-map.
- **Mandatory gates:** PASS in prose.
- **Grade credibility:** FAIL. B, F, and G are not proof-grind ready because actual producer fixtures are absent and occurrence provenance is not sealed at the fold outputs. No honest replacement range can be inferred until those types and probes are repaired.

## Exact changes required for round 10

1. **Seal occurrence provenance at its first operational source, not only at O18.** `AdjacentSwapResult.swappedOccurrenceCorrespondence` must be definitionally derived from an explicit suffix-replay occurrence fold, or sealed by equality to such a fold whose step maps pin the moved-left/moved-right occurrences and recursive suffix occurrences. `replaceActualSwapOccurrenceMap` must fail.
2. **Carry executable deletion/sorting derivations to their output maps.** `ClosingFreeReduction` and `SortedClosingFreeTrace` must either store explicit recursive derivations and derive occurrence correspondence projections, or store erased equalities tying runtime maps to such derived folds. `replaceReductionOccurrenceMap` and `replaceSortedOccurrenceMap` must fail before accounting laws. The O18 capital should project through these seals.
3. **Repeat coherent-both-halves laundering attacks end to end.** A correspondence automorphism may be internally coherent, but it must not enter actual swap, deletion, sorting, O18, or bridge outputs without equality to the operational fold. Retain generated-only, public-schedule, tree-only, wrong-birth, wrong-generation, and wrong-occurrence negatives.
4. **Ship a genuinely concrete O16 fixture.** Construct an actual trace with two generated births and one withdrawal; construct (not assume) its deletion reduction, sorting result, endpoint/external laws, `CanonicalReplayAccountingLaws`, tree, authentication, sealed capital, and external projections. If this cannot be done before O16, rename the current record to an abstract assembler and withdraw the “nontrivial producer calibration” claim.
5. **Ship actual origin-plan fixtures.** Commit 1×1, 2×1, and repeated-Iter 2×2 modules that construct `AdjacentSwapResult`s, `CrossingOriginPlanStep`s, decomposition range laws, and `WholeBlockSwapDerivation`; do not accept prebuilt plans/labels/range laws as the test conclusion. Retain shifted-start, equal-start, boundary, duplicate, root, and zero-node negatives.
6. **Make the full suite reproducible.** Commit research test modules or a serial script for pollution (pure/outer), safety detachment, generated-child, wrong trace, stale quotient, mixed capital, wrong occurrence, zero/duplicate/root, scanner orderings/generation, static variants, O/A application, occurrence folds, vestigial assembly, deletion boundaries, threading, outer schedules, and full pipeline.
7. **Reconcile holes and re-estimate after the type repair.** Charge new provenance-derivation work to O1/O6/O9/O10/O16/O17/O18/O20 and phases A/B/C/D/F/G; retain exact arithmetic and mandatory gates.
8. **Retain release closure.** Re-run all spikes and committed probes serially, exact CP3/source diff, research isolation, no escapes, 207/207 external build, and clean tracked/index checks.

## Final verdict

**REJECT.** Revision 9 fixes the final-capital clone and generated/action coherence fronts, and its coordinate consumer theorems are materially stronger. It is not ready for the proof grind: exact occurrence provenance is still a freely replaceable field of the actual swap/deletion/sorting producer records, while the claimed nontrivial authentication and origin-plan producer fixtures are absent.

**Final verdict: REJECT**
