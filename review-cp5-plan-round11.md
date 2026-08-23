# Adversarial Review — CP5 Theorem 73 Scoping Plan, Round 11

**Reviewer:** fresh-context adversarial reviewer  
**Target:** branch `cp5-thm73-scoping`, claimed commit `6773ffc`  
**Scope:** type-level verification of the round-11 repairs; production tree is immutable.

## Probe log

_This log is appended immediately after each probe. Classifications are provisional until the final findings._

### Probe 1 — immutable production baseline and repository state
- **Command:** `git rev-parse HEAD; git branch --show-current; git status --porcelain=v1; git rev-parse HEAD:src/DGamma/CP3.idr; git diff --stat 34b21c9..HEAD -- src dgamma.ipkg; git diff --exit-code 34b21c9..HEAD -- src dgamma.ipkg`
- **Result:** HEAD is `6773ffc0ff766d3ebe0bd9c8dc0cc330349df6b5` on `cp5-thm73-scoping`; CP3 blob is the required `2c697e532e83989de8591fa6a4378747c6a501c0`; production diff is empty (`DIFF_EXIT=0`). Index/tracked files are clean. Porcelain reports only pre-existing untracked `paper/` and this permitted report.
- **Classification:** **note** — immutable target and production-tree hygiene pass; final no-staged-files check still required.

### Probe 2 — round-10 front, revision-11 claims, and harness source
- **Command:** read `review-cp5-plan-round10.md`, `THM73-PLAN.md`, `research-tests/audit-r11-claims.sh`, and `research-tests/run-r11-suite.sh` in full.
- **Result:** The plan addresses the two exact round-10 signature blockers and chooses per-derivation authority. The suite declares 5 spikes, 27 positives, and 26 negatives and runs serially. Each negative requires both a diagnostic fragment and declaration symbol. The audit script does check `git ls-files --error-unmatch` and nonempty files for eleven specifically cited R11 artifacts, and set equality between every tracked test `.idr` stem and runner entries. However, its semantic checks for O6/O9 and repackager honesty are only greps for declaration/name phrases; it does not type-check relation exhaustiveness/disjointness, certificate indexing, diagnostic tightness, production immutability/reachability, category counts, exact phase-row arithmetic, or execute the suite. These omissions make it a claims-inventory preflight, not verification of the substantive claims.
- **Classification:** **major (provisional)** — the auditor is materially weaker than the plan's “tracked-claims audit” rhetoric; independent probes are required and any final severity depends on whether its unverified claims actually hold.

### Probe 3 — exact external release copy and inventory
- **Command:** recreate `/tmp/thm73-review11-probes/release` using `git archive 6773ffc -- src research research-tests dgamma.ipkg THM73-PLAN.md`; count research/test modules; compare CP3 SHA-256 with `git show`; inspect tracked modes; run `idris2 --version`.
- **Result:** Idris 2 is 0.8.0. The exact archive has five research spikes, 53 research-test Idris modules, and 269 files total. CP3 hashes match exactly (`23a9a0d3...54e2ec`). Plan and both scripts are tracked; both scripts are executable.
- **Classification:** **note** — all subsequent generated/type-checking probes use the immutable tracked release outside the repository.

### Probe 4 — O6 source and malicious-prefix test audit
- **Command:** inspect `CP5ConfluenceLocalDiamondSpike.idr:420–629`, `R11AdjacentPrefixMalicePositive.idr`, `R11AdjacentPrefixCollapsedCertificateNegative.idr`, and `R10AdjacentSwapMapCloneNegative.idr` from the exact archive.
- **Result:** `AdjacentSwapOrdinalRelation` has the advertised four constructors and fixes the source ordinal in every region. `adjacentSwapOrdinalExhaustive` is structural over both Nats. The fold requires the relation for every located swapped occurrence; the old partial fields are gone. The malicious-prefix positive is not a concrete trace fixture, but it is a genuine universally quantified rejection theorem for two occurrences of one action with an explicit equal-tag premise and distinct ordinals. Its `sameTag` and one relation premise in the permutation theorem are unused, but the conclusion still follows non-vacuously from the exhaustive relation. The negative directly attempts a distinct strict-prefix source index. Source inspection alone does not establish totality, boundary correctness, or injectivity, so generated checks follow.
- **Classification:** **note** — advertised O6 shape exists; no interface defect established by source audit.

### Probe 5 — O9 source, immutable deletion semantics, and tracked tests audit
- **Command:** inspect `CP5ConfluenceDeletionChainSpike.idr:180–409`, immutable `CP3.idr:3375–3425,3638–3710`, and all three R11 O9 positive/negative modules.
- **Result:** `GenerationActionSubsequence` consumes one original transition in both constructors and one survivor transition only in `KeepGenerationAction`. The executable fold matches exactly: keep-zero → source zero; keep-successor recurses and increments source; delete recurses at unchanged target and increments source. `DeletionResult` splits the original as before / opening+episode / after and the survivor as before / episode / after. The embedding offsets use survivor-before for episode targets, survivor-before+survivor-episode for after targets, original-before for episode sources, and original-before+original-episode for after sources. The certificate quantifies every actual survivor occurrence and relates its actual replay origin ordinal. The full-step clone reuses every other field and changes only the runtime map. No caller-selected ordinal function is stored.
- **Classification:** **note** — source-level keep/delete direction and three segment offsets match immutable semantics; boundary and within-segment malice still require type probes.

### Probe 6 — per-derivation authority dependency trace
- **Command:** inspect deletion fold/core/reduction, canonical accounting/O16/O18 projections, O19/O20 in `CP5ConfluenceCrossTraceSpike.idr:780–1189`, and bridge/scanner/endpoint composition in `CP5ConfluenceRenamingCompositionSpike.idr`.
- **Result:** The actual chain is: each O9-certified step → `closingFreeDeletionOccurrenceFold` over one explicit `ClosingFreeDeletionDerivation` → `reductionOccurrenceCorrespondence`; one explicit `FiniteAdjacentSwapDerivation` → `sortingOccurrenceCorrespondence`; their composition → `deletionSortingOccurrenceCorrespondence`; O16 constructs the CP3 tree *from that same map* and authenticates it by exact occurrence equality; `producerCanonicalSchedule` and O18 retain the same reduction/sort/accounting chain, with `canonicalOccurrenceCorrespondence` projecting that chain. O19 carries the two independently selected capitals and realizes a block permutation only from the selected left capital. O20's bridge is indexed by that exact permutation map plus those exact left/right capitals. O21's generated-birth equation applies the left capital's map to its source occurrence and the right capital's map to its right occurrence under the immutable cross-trace generation bijection. Scanner capital classifies withdrawals from each selected capital against the original accepted cross-trace scanner. Generic renaming composition composes endpoint bijections/relations, not independently recomputed occurrence maps. No consumer compares two different deletion/sorting derivations of one trace or substitutes one capital's map into another capital's tree/schedule.
- **Classification:** **note** — the no-path-independence rationale survives the explicit consumer trace. Path independence would be a separate canonical-algorithm theorem, not an implicit premise of the existential immutable `ConfluenceResult`.

### Probe 7 — repackager rename and honesty search
- **Command:** grep `THM73-PLAN.md`, all research sources, tests, and scripts for `fixture`, `constructs raw`, `calibration`, old `OperationalOriginPlanFixtures`, `SuppliedOriginPlanIngredients`, `RawOrigin`, and `repackage`; inspect `R11GenericRawPlanRepackagerPositive.idr:1–180`.
- **Result:** The old R10 module/name is absent. The R11 type explicitly stores the threaded `prefixOccurrences`, both ordinal-origin equations, and a recursively supplied tail. Comments say the code merely repackages these premises; 1×1/2×1/2×2 exports are `repackage...SuppliedPlan`/`...Whole`. No remaining text calls this repackager a fixture or claims it constructs/proves the raw origin ingredients. Other `fixture` uses refer to the separately disclosed abstract O16 assembly, concrete scanner values, or actor-block decomposition fixtures and are not origin-repackager claims.
- **Classification:** **note** — option (a) honesty and rename completeness pass.

### Probe 8 — execute tracked claims auditor
- **Command:** `cd /Users/vyacheslavshebanov/Work/dgamma && bash research-tests/audit-r11-claims.sh`
- **Result:** Exit 0, `R11_TRACKED_CLAIMS_AUDIT=passed`.
- **Classification:** **note with major audit limitation** — its implemented inventory/grep checks pass, but Probe 2's semantic and release omissions remain; the success marker must not be interpreted as independent verification of all revision-11 claims.

### Probe 9 — independent suite set/cardinality reconciliation
- **Command:** Python-parse `SPIKES`, `POSITIVE`, and `NEGATIVE_SPECS` from the exact archived runner; compare ordered entries and sets with every archived `research-tests/DGamma/*.idr`; check duplicate/cross-category membership and retired R10 artifacts.
- **Result:** Exactly 5 unique spikes, 27 unique positives, and 26 unique negatives. All 53 tracked test modules occur exactly once; missing/extra/within-category/cross-category duplicate sets are empty. Retired `run-r10-suite.sh` and `R10OperationalOriginPlanFixturesPositive.idr` are absent.
- **Classification:** **note** — exact 5/27/26 and all-53-once source coverage claims pass independently; execution remains to be checked.

### Probe 10 — holes, arithmetic, and escape scan
- **Command:** independently regex-enumerate every named hole in the five archived spikes; sum the documented O1–O23 values and eight phase rows; grep `src`, research tests, and research for holes/escapes; search `dgamma.ipkg` for research/CP5-confluence references.
- **Result:** Exact hole split is canonical 6, cross 4, deletion 11, local 9, renaming 2; total and unique count are 32. O-map sums to 32. Phase rows sum exactly 148–257. `src` and research tests have no holes, `believe_me`, `assert_total`, `%default partial`, postulate, or axiom declarations; research has no escape beyond the 32 named holes. No package reference to research or CP5-confluence spikes was found. The compound command's final cosmetic production-module count grep used the wrong indentation pattern and exited 1 after all substantive checks; package reachability is rechecked separately.
- **Classification:** **note** — hole split and arithmetic claims pass; no hidden escape found. The final count subcommand was a harness mistake, not a code failure.

### Probe 11 — production package reachability retry
- **Command:** parse every `DGamma.*` module token in the exact archived `dgamma.ipkg`; count duplicates and names containing `Confluence`/`Spike`.
- **Result:** Exactly 207 unique production modules; no confluence-spike/research-like module is listed.
- **Classification:** **note** — research and research-tests are unreachable from the production package graph.

### Probe 12 — best-effort unseeded exact release build
- **Command:** verify no prior Idris/Chez process, remove external archive `build/`, then serially run `idris2 --build dgamma.ipkg` with output captured to `/tmp/thm73-review11-probes/unseeded-build.log`.
- **Result:** Exit 137; launcher reports `Killed: 9` and no Idris type diagnostic. No concurrent Idris process was running (the process listing only showed the current shell command text).
- **Classification:** **note** — disclosed host-kill is reproduced exactly and yields no type-level failure; seeded retry is required.

### Probe 13 — exact seeded 207/207 package closure
- **Command:** copy the production TTC seed into the byte-identical exact archive, delete archived `CP4ProgressProof.ttc/.ttm`, then serially run `idris2 --build dgamma.ipkg` and require the terminal counter.
- **Result:** Exit 0 with `207/207: Building DGamma.CP4ProgressProof (src/DGamma/CP4ProgressProof.idr)` exactly once.
- **Classification:** **note** — seeded external release claim passes; production source/package identity was established before using the seed.

### Probe 14 — authoritative exact-release suite execution
- **Command:** delete external research/test TTCs and run exact archived `bash research-tests/run-r11-suite.sh` serially, capturing `/tmp/thm73-review11-probes/r11-suite.log`; count category and pass markers.
- **Result:** Exit 0 with exactly 5 `SPIKE`, 27 `POSITIVE`, 26 `NEGATIVE`, and one `R11_REPRODUCIBLE_SUITE=passed` marker. Every research/test unit was forced through source checking against the exact seeded production interfaces.
- **Classification:** **note** — suite cardinality and full serial execution claims pass.

### Probe 15 — hand audit of four module-specific negative diagnostics
- **Command:** fresh serial source checks of `R11AdjacentPrefixCollapsedCertificateNegative`, `R11DeletionFillerMapCertificateNegative`, `R11CoherentBothHalvesAssemblyNegative`, and `R11BridgeWrongGenerationNegative`; inspect exact error/declaration/location in `/tmp/thm73-review11-probes/hand-negative-errors.txt`.
- **Result:** All four exit 1 at the intended declarations and source RHS lines: O6 fails by `targetOrdinal` vs `sourceOrdinal`; O9 fails by `generationSubsequenceSourceOrdinal (beforeDeletion result) ...` vs the filler origin; O18 reassembly fails by `alternate` vs the actual composed `MkActionRegistrationReplayCorrespondence`; bridge generation fails by the arbitrary right birth ordinal vs `(generatedGenerationBijection sameInputs).generationForward ...`. Every runner-required diagnostic and symbol is present in its own substantive type error, not an import/parser/coincidental failure.
- **Classification:** **note** — sampled per-module checks are tight and exercise the advertised boundaries.

### Probe 16 — generated O6 boundary/injectivity probe, first attempt
- **Command:** check `/tmp/.../R11ReviewerO6SoundnessPositive.idr`, containing classifier checks at empty-prefix targets 0/1/2 and prefix-count-2 targets 0/1/2/3/4 plus a full constructor-pair proof that two target ordinals cannot alias one source ordinal.
- **Result:** Harness timeout after 300 seconds with no returned Idris result. This is not a type failure; process state and a serial retry are required.
- **Classification:** **note** — environment/resource outcome only.

### Probe 17 — split O6 boundary classifier probe, first elaborating run
- **Command:** check a smaller generated module covering `prefixCount=0` targets 0/1/2 and `prefixCount=2` targets 0/1/2/3/4 via `adjacentSwapOrdinalExhaustive`.
- **Result:** Exit 1 because a wildcard dependent-pair binder kept the existential source ordinal opaque in the probe body; all eight errors were probe-construction unification errors, not contradictory classifier outputs.
- **Classification:** **note** — invalid first probe formulation; refine by matching the relation constructor.

### Probe 18 — O6 classifier boundaries, relation-constructor formulation
- **Command:** retry matching each returned relation constructor; then import `Data.Nat` after the first retry exposed only an unresolved `Data.Nat.LT` name in the generated probe, and check serially again.
- **Result:** Final exit 0 (1/1). Empty-prefix moved-right/moved-left/suffix edge targets and nonempty prefix/suffix boundaries all inhabit exactly the advertised source ordinals: for prefix count 2, `0→0`, `1→1`, `2→3`, `3→2`, `4→4`.
- **Classification:** **note** — classifier coverage and all requested boundary ordinals pass. Intermediate `Data.Nat.LT` was a missing generated-probe import, not a release defect.

### Probe 19 — generated global O6 ordinal no-alias proof
- **Command:** check a generated 16-constructor-pair proof that two `AdjacentSwapOrdinalRelation` witnesses with one source ordinal force equal target ordinals.
- **Result:** Harness timeout after 600 seconds with no Idris output; no residual Idris process. Idris 0.8.0 did not finish elaborating the exhaustive dependent match, so this generated theorem is not accepted evidence. Source-level analysis still shows all four source images are `target`, `S p`, `p`, `target`, with disjoint regional bounds, but a smaller type-checking attack is required.
- **Classification:** **note** — environmental/elaboration limitation, not a demonstrated interface defect.

### Probe 20 — round-10 Probe 41 rerun at strengthened O6 type
- **Command:** compile a generated copy of the old `operationalFoldFromOnlyAdvertisedLaws`, supplying an arbitrary correspondence plus only moved-right, moved-left, and suffix ordinal laws, with no strict-prefix law.
- **Result:** Exit 1 at `MkAdjacentSwapOperationalOccurrenceFold`: the first old moved-right equality cannot unify with the new required function `(occurrence : LocatedActionOccurrence ... ) -> AdjacentSwapOrdinalRelation ...`. The old prefix-gap constructor attack is dead.
- **Classification:** **note** — O6 under-specification blocker is repaired at the constructor codomain.

### Probe 21 — new authenticity-front source calibration
- **Command:** inspect the generated-only retarget, tree-only capital clone, O18 coherent-both-halves positive/negative, and bridge wrong-generation modules in full.
- **Result:** Generated-only retarget actually reconstructs `MkActionRegistrationReplayCorrespondence` while changing only its generated-origin function and reuses old coherence. Tree-only clone actually reconstructs `MkIndependentCanonicalSchedule` while changing only its runtime schedule. The O18 pair calls `assembleIndependentCanonicalSchedule` with the existing capital's exact producer fields; the negative equates its projected map to arbitrary coherent input. Bridge wrong-generation states the exact accepted generation-forward equation for arbitrary canonical births. These are not merely universal projection inequalities or comments.
- **Classification:** **note** — the five newly tracked suite fronts are substantively calibrated.

### Probe 22 — round-10 Probe 42 rerun at strengthened O9 codomain
- **Command:** compile the old exact-index function that returned an arbitrary `ActionRegistrationReplayCorrespondence` at the O9 result indices, changing only its declared codomain to the new O9 codomain.
- **Result:** Exit 1 at the body: bare `ActionRegistrationReplayCorrespondence ... trace (survivingTrace result)` cannot unify with `DeletionOperationalOccurrenceCertificate ... result`.
- **Classification:** **note** — the old generic-codomain under-specification is closed; constructing O9 now requires per-survivor embedding evidence.

### Probe 23 — generated O9 keep/delete and segment-boundary laws, first attempt
- **Command:** check a generated module whose proof-index patterns test keep-delete-keep (`0→0`, `1→2`), delete-keep-keep (`0→1`, `1→2`), and first episode/after global offsets.
- **Result:** **Invalid run despite exit 0:** Idris emitted multiple errors beginning `Undefined name Decidable.Equality.Core.DecEq` because the generated module omitted `Decidable.Equality`; later declarations were consequently not checked. This Idris 0.8.0 behavior confirms exit code alone is unsafe and vindicates diagnostic scanning in the suite.
- **Classification:** **note** — generated-probe import failure only; no semantic evidence accepted.

### Probe 24 — generated O9 law retry with DecEq import
- **Command:** add `Decidable.Equality`, preserve proof-index pattern tests, use explicit `+ 0` boundary indices, and recheck.
- **Result:** Exit 1. The dependent catch-all clauses did not reduce the proof-indexed law families to `Unit`, and the boundary declarations lacked the module exposing `LocatedClosedEpisode`. These are generated-probe formulation/import failures; the shaped branches themselves produced no computation mismatch.
- **Classification:** **note** — no release defect; reformulate with explicit shape witnesses and import `DGamma.Metatheory`.

### Probe 25 — exhaustive proof-index formulation retry
- **Command:** enumerate outer/nested keep/delete/end shapes in the generated type family and proof, import metatheory, and recheck.
- **Result:** Exit 1 with a 73KB coverage explosion: Idris did not recognize the nested dependent patterns as covering and could not reduce the generic delete proof branch. This generated formulation is invalid and gives no semantic result. The segment-boundary declarations emitted no independent offset mismatch before the coverage failure.
- **Classification:** **note** — reviewer-probe elaboration limitation; switch to direct constructor recurrence equations.

### Probe 26 — valid O9 recurrence and segment-edge equations
- **Command:** check generated direct equations for `KeepGenerationAction` at target zero and successor, `DeleteGenerationAction` at arbitrary target, plus episode-first and after-first constructors with the exact global offsets.
- **Result:** Exit 0 with zero error diagnostics. The equations establish keep-zero=`Just 0`, keep-successor=`map S` of the tail at predecessor, delete=`map S` of the tail at the same survivor target; episode and after first-survivor embeddings elaborate exactly at survivor/source segment offsets. Only benign auto-implicit shadowing warnings occurred.
- **Classification:** **note** — actual execution direction and segment-boundary offsets type-check against immutable semantics.

### Probe 27 — O9 segment-boundary disjointness
- **Command:** check a generated structural theorem that `generationSubsequenceSourceOrdinal subsequence (transitionCount surviving) = Nothing`, then instantiate it to reject before claiming the episode boundary and episode claiming the after boundary.
- **Result:** Exit 0 with zero error diagnostics. Keep and delete cases both rewrite through the exact recursive fold; last-valid/first-next segment boundaries cannot overlap.
- **Classification:** **note** — before/episode/after constructor ranges are separated by the executable subsequence length, including the off-by-one edges.

### Probe 28 — generated within-segment strictness theorem, first attempt
- **Command:** structurally prove adjacent survivor targets map to strictly increasing source ordinals using an inversion lemma for `map S input = Just output`.
- **Result:** Exit 1 solely on totality coverage of nested local equality-case blocks; no type equation or strictness branch failed. The generated theorem is not accepted until refactored into named total equality helpers.
- **Classification:** **note** — reviewer-proof coverage issue, not an interface break.

### Probe 29 — within-segment strictness refactor, first run
- **Command:** replace nested equality cases with named total helpers and rewrites; recheck the strictness theorem.
- **Result:** Exit 1 at the generated helper application because its unconstrained literal `0` defaulted to `Integer`, while the subsequence ordinal is `Nat`. This is a probe annotation error; all recursive cases otherwise elaborated to that point.
- **Classification:** **note** — add explicit `Nat` type to zero and retry.

### Probe 30 — valid within-segment strictness theorem
- **Command:** type the helper literal as `Nat` and recheck the structural theorem that adjacent survivor positions with successful source lookups have strictly increasing source ordinals.
- **Result:** Exit 0 with zero diagnostics. The theorem covers end, keep-zero, keep-successor, and delete recursively. Therefore two same-action survivors cannot be collapsed or permuted within one deletion segment by the embedding computation.
- **Classification:** **note** — O9's exact executable relation is injective/ordered within each segment, not merely deterministic by name.

### Probe 31 — standing forgery-front reconciliation against executed suite
- **Command:** map the required standing attacks to the exact runner entries and the successful Probe-14 run; cross-check new module bodies and four hand diagnostics.
- **Result:** Executed negatives include swap-map clone; deletion-step direct clone plus reduction/sorted clones; coherent both-halves O18 assembly; generated-only retarget; tree-only capital schedule clone; public schedule; wrong bridge birth/generation/occurrence/trace; scanner wrong-generation; shifted node/coordinate, duplicate label, arbitrary root, and zero-derivation node. Pollution, detachment, stale quotient, mixed schedule, and outer schedule attacks also remain. No required standing front was dropped.
- **Classification:** **note** — retained authenticity coverage passes at tracked HEAD.

### Probe 32 — forward/reverse O1–O23 hole reconciliation
- **Command:** print all 32 exact hole sites from the archive and map each declaration semantically in both directions to the plan obligation counts.
- **Result:** Bijection holds: O1 has same-external refl/trans, endpoint refl/trans, and composed endpoint (5); O2 has two independence transports; O3/O4/O5 have 1/2/1 diamond holes; O6 has occurrence fold, suffix replay, whole-block swap (3); O7/O8 have scan/selection; O9 has certificate fold and enriched step (2); O10/O11 have recursive core/accounting; O12 shape; O13 none; O14 ordering; O15 support; O16 accounting; O17 sort; O18 capital; O19 match/selector (2); O20 convergence; O21 two scanner inductions plus replayed endpoint composition (3); O22/O23 none. No hole is unmapped or double-counted.
- **Classification:** **note** — exact 32-hole reverse reconciliation passes after in-place O6/O9 codomain strengthening.

### Probe 33 — concrete O6 no-alias edge proof, first attempt
- **Command:** check four concrete prefix/prefix, prefix/moved, moved/moved, and moved/suffix same-source alias rejections at prefix count 2.
- **Result:** Exit 1 only because Idris's coverage checker demanded explicit impossible arithmetic clauses around the moved-pair case; the constructor source-index mismatch clause itself was accepted. Add the tracked arithmetic contradictions explicitly.
- **Classification:** **note** — reviewer-proof coverage issue, no successful alias.

### Probe 34 — valid concrete O6 no-alias edge proof
- **Command:** add explicit prefix-vs-pivot and suffix-vs-pivot contradiction clauses using the five tracked arithmetic functions; recheck all four concrete same-source alias attacks.
- **Result:** Exit 0 with zero diagnostics. At prefix count 2, consecutive strict-prefix, prefix/moved, moved-pair, and moved/suffix target ordinals cannot share one source ordinal.
- **Classification:** **note** — together with the four-region identity/swap indices, the relation enforces ordinal-level injectivity at all boundary kinds. No separate map-injectivity field is present, but target-totality is the fold's universal field and ordinal no-alias follows from the indexed relation.

### Probe 35 — all-test trackedness (stronger than auditor)
- **Command:** compare `git ls-files 'research-tests/DGamma/*.idr'` stems against every working-tree test module and the eleven required R11 stems.
- **Result:** 53 tracked versus 53 present; no untracked module, tracked-missing module, or untracked required R11 artifact.
- **Classification:** **note** — actual commit trackedness passes, although the auditor's all-53 set check incorrectly uses filesystem globbing rather than `git ls-files`.

### Probe 36 — suite-log diagnostic and freshness audit
- **Command:** grep the Probe-14 suite log for `Error:`, `Warning:`, and Idris build counters; inspect where research TTCs were written.
- **Result:** The log has zero errors/warnings, but no build counters: the earlier cleanup removed TTCs only under `research/` and `research-tests/`, while Idris had placed them in root `build/ttc`. Thus Probe 14 established runner traversal and cached interface acceptance, not forced fresh source elaboration. Also, Probe 23 demonstrated Idris 0.8.0 can emit `Error:` yet return 0; the runner does not capture/scan positive or spike diagnostics, so `set -e` alone can falsely accept such a positive.
- **Classification:** **major** — runner robustness claim is incomplete. Actual tracked sources may still pass a correctly forced run, but the authoritative harness must reject `Error:` diagnostics for successful units and provide a fresh-TTC mode or documented clean command.

### Probe 37 — correctly forced fresh source suite
- **Command:** delete root `build/ttc/*/DGamma/{all 5 spikes + 27 positives + 26 negatives}.{ttc,ttm}` by parsed runner inventory, then rerun the exact tracked suite serially and scan output.
- **Result:** Removed 64 existing interfaces across the 58 listed units. Exit 0 with exact 5/27/26 markers, one pass marker, **zero positive/spike `Error:` lines**, and exactly 32 successful build counters (5 spikes + 27 positives). Negatives were freshly attempted and rejected internally. The tracked sources genuinely pass when forced; the Probe-36 issue is harness hardening, not a false current artifact.
- **Classification:** **note, preserving Probe-36 major** — actual fresh source evidence passes; the authoritative script can still false-pass a future error-with-zero-exit positive unless repaired.

### Probe 38 — full historical review reconstruction
- **Command:** read `review-cp5-plan-round1.md` through `review-cp5-plan-round9.md` in full (including paginated tails), in addition to the already-read round 10.
- **Result:** The complete narrowing history is consistent with the current attack: early schedule/support/bridge gaps; then vestigial path and operational permutation defects; then certificate pollution, occurrence-map authenticity, fake fixtures, and finally the round-10 O6/O9 signature gaps. No older blocker bypassed by the revision-11 interfaces was rediscovered. The standing forgery suite maps to the historical front as claimed.
- **Classification:** **note** — review basis is the full prior evidence, not only the current plan's closure table.

### Probe 39 — auditor duplicate-entry mutation, first simulation
- **Command:** clone the external release into a temporary git repository, duplicate one positive runner entry, and execute `audit-r11-claims.sh`.
- **Result:** Simulation invalid: the cloned external tree also contained ten generated `R11Reviewer*.idr` probes from this review, so the auditor correctly failed set equality on those extras before testing duplicate detection.
- **Classification:** **note** — remove reviewer probes from a clean simulation and retry.

### Probe 40 — auditor duplicate-entry mutation, conclusive
- **Command:** create a clean temporary git archive of exact HEAD, stage all artifacts, duplicate `R10ProvenanceProjectionPositive` in the runner (two occurrences), and execute the unchanged audit script.
- **Result:** `duplicate_count=2`, yet audit exits 0 with `R11_TRACKED_CLAIMS_AUDIT=passed`. Its Python converts runner entries to a `set`, so it cannot verify the advertised “exactly once” property. Combined with Probe 2, it also does not verify category counts or run/type-check semantic claims.
- **Classification:** **major** — concrete false acceptance by the auditor. Replace set-only comparison with ordered/list cardinality and duplicate checks; derive the filesystem set from `git ls-files`; include spike/trackedness and release assertions, or rename the script as a limited inventory audit.

### Probe 41 — runner error-with-zero-status mini-simulation, first attempt
- **Command:** put a currently malformed generated module behind the runner's exact `set -e; idris2 --check; continue` pattern.
- **Result:** This malformed version exits 1, so `set -e` stops and the continuation marker is absent. It does not reproduce Probe 23's anomalous status-0 diagnostic and is not evidence of false acceptance.
- **Classification:** **note** — construct the same missing-`DecEq` error shape that produced status 0 and retry.

### Probe 42 — runner positive false acceptance, conclusive
- **Command:** copy the generated dependent module, remove its direct `Decidable.Equality`/metatheory imports to reproduce the missing-`DecEq` diagnostic, and run it under the runner's exact `set -e; idris2 --check; continue` pattern.
- **Result:** Script exits **0**, output contains **8 `Error:` lines**, and `RUNNER_CONTINUED_AFTER_IDRIS_ERRORS` is printed. Idris 0.8.0 returned success despite declaration errors, so the tracked runner's spike/positive loops can falsely pass exactly this class of broken module.
- **Classification:** **major** — concrete harness false acceptance. Capture each successful-unit output and fail on any `Error:` (and preferably require the expected build/TTC), rather than trusting process status alone.

### Probe 43 — final coordinate, immutable target, index, and process hygiene
- **Command:** recheck HEAD/branch/CP3 blob; `git diff --exit-code 34b21c9..HEAD -- src dgamma.ipkg`; tracked and staged names; status; active Idris/Chez; report line count/hash.
- **Result:** Exact HEAD `6773ffc0...` on the requested branch; exact CP3 blob `2c697e...`; production diff exit 0; tracked worktree and index empty; no Idris/Chez process. Status contains only pre-existing untracked `paper/` and this permitted report. Before this entry the report had 220 lines and SHA-256 `99143d99...7461f`.
- **Classification:** **note** — production, tracked tree, index, and process hygiene pass.

## Claimed-fix disposition

| # | Revision-11 claim | Checked disposition |
|---:|---|---|
| 1 | O6 exhaustive four-region certificate and malicious-prefix closure | **Pass.** Classifier edges at empty/nonempty prefixes check; old Probe 41 fails; the universal fold law covers every located target occurrence; concrete no-alias proofs cover every region boundary. The relation itself fixes the source ordinal, while generated/action coherence remains in the correspondence. |
| 2 | O9 exact subsequence fold, three-segment certificate, and step seal | **Pass.** Keep/delete recurrences, first-next segment offsets, boundary disjointness, and within-segment strict source ordering check. Old Probe 42 fails. Filler-map and full-step clones reject at the intended boundaries. |
| 3 | Honest option-(a) raw-plan repackager | **Pass.** Rename is complete; map, both equations, and recursive tail are disclosed; no origin-fixture claim remains. |
| 4 | Exact tracked suite and strengthened authenticity coverage | **Artifacts and current results pass; authoritative harness has a major defect.** Exactly 5/27/26 and all 53 tests once; a correctly forced source run builds all 32 successful units with no errors and all 26 negatives reject. But the runner can false-pass a spike/positive when Idris prints errors with exit 0 (Finding 1). |
| 5 | Per-derivation authority; no path-independence hole | **Pass.** Every consumer stays indexed by its selected chain. No use site compares maps from two derivations of one trace. |
| 6 | Exactly 32 holes and 148–257 | **Pass.** Exact 6/4/11/9/2 split, exact reverse O-map, exact row sum. |
| 7 | Seeded 207/207 and disclosed unseeded exit 137 | **Pass.** Best-effort unseeded run reproduced exit 137 without diagnostic; seeded exact archive rebuilt terminal module at 207/207. |

## Dependency-chain decision: path independence

The checked chain is:

1. each selected O9 step carries its local exact survivor certificate;
2. one explicit deletion derivation composes those step projections;
3. one explicit finite adjacent-swap derivation composes O6 projections;
4. O16 constructs/authenticates the CP3 tree against that exact composed map;
5. O18 seals the schedule/map to those exact carried reduction/sorting/accounting values;
6. O19 realizes a permutation from the exact selected left capital;
7. O20 retains that operational map and the two exact selected capitals;
8. O21 relates left and right original generations by applying each capital's own authenticated map under the accepted cross-trace bijection; and
9. renaming composition combines endpoint relations/bijections, not alternative occurrence maps.

Even if two algorithms canonicalize the same trace differently, immutable `ConfluenceResult` asks existentially for the selected schedules and endpoint equivalence. No consumer requires equality of independently computed maps. A future canonical-algorithm-independence theorem would be additional API work, not a missing premise here.

## Numbered findings

1. **major — `research-tests/run-r11-suite.sh` can falsely accept broken spikes/positives.** The success loops rely only on `set -e` and Idris's process status. Probe 42 reproduces Idris 2 v0.8.0 emitting eight declaration `Error:` diagnostics, returning 0, and letting the runner-style continuation execute. Negatives are protected by captured-output checks; positives and spikes are not. The script also has no built-in fresh-TTC mode, which made the first review run cached until the reviewer deleted the correct root TTCs. The current tracked source is not falsely green: a correctly forced run produced 32 fresh successful build counters, zero errors, and all 26 intended rejections. This is a release-harness defect, not an O6/O9 interface defect.

2. **major — `research-tests/audit-r11-claims.sh` is a limited grep/set inventory but reports a broad claims-audit pass.** It checks trackedness only for the eleven named R11 artifacts, uses filesystem globbing for the all-test set, reduces runner entries to a set, and greps declaration names. It does not check category cardinalities, duplicates, exact phase-row arithmetic, hole category split, semantic types, production immutability/reachability, escapes, or execute the suite. Probe 40 duplicates a positive runner entry in a clean temporary tracked tree; the unchanged auditor still emits `R11_TRACKED_CLAIMS_AUDIT=passed`. Actual HEAD trackedness and all-once coverage independently pass, so this is an auditor false-acceptance defect rather than a hidden missing artifact.

## Positive results / non-findings

- O6's strict prefix gap is closed. Empty-prefix and pair/suffix edges classify correctly; a target-total certificate cannot reuse the old moved/suffix-only contract.
- O6 source ordinals form the adjacent transposition: prefix/suffix identity and pair exchange. Concrete boundary no-alias proofs reject two distinct target positions sharing one source ordinal.
- O9's computation exactly mirrors immutable `GenerationActionSubsequence`; successive survivor positions map to strictly increasing source positions, and segment boundaries return `Nothing` before the next offset begins.
- O9's before/episode/after offsets match the immutable original/survivor concatenation parentheses and counts.
- Direct swap/deletion/reduction/sort/capital map substitution, generated-only retarget, tree-only schedule clone, coherent O18 reassembly, and bridge wrong birth/generation/occurrence attacks all reject.
- The generic repackager is now described honestly; no closed fixture is implied.
- All 53 test modules and every cited R11 artifact are genuinely tracked at HEAD.
- Production target, package graph, escape isolation, seeded build, tracked worktree, and index all pass.

## Residual risks

- All 32 research theorem bodies remain holes by design; this review validates scoping, not Confluence.
- No concrete O16 two-birth/one-withdrawal producer exists; it remains an explicit XL gate.
- No reachable repeated-Iter 2×2 operational origin plan is constructed; the generic repackager assumes its recursive ingredients.
- O/A, O/O, universal operational selection, accepted scanner inductions, and vestigial endpoint composition remain the largest mathematical risks.
- The O6 relation does not ship a generic named injectivity theorem, although its indexed constructors and checked boundary proofs enforce the permutation at ordinal level. Downstream generated injectivity/accounting is separately explicit.
- O9 retains local certificates inside the chosen derivation rather than exposing one flattened original→final ordinal embedding theorem; composition is by the carried maps. This is sufficient for the current consumers but may be worth proving for a runtime provenance API.
- Fully unseeded package compilation remains host-killed in this environment; exact seeded closure is reproducible.

## Estimate assessment

- **Hole count/reconciliation:** PASS — exactly 32, exact forward/reverse O1–O23 map.
- **Arithmetic:** PASS — exact 148–257.
- **Interface repair charge:** PASS — O6/O9 codomains were strengthened in place and their larger B/C/D/F/G bands reflect downstream proof threading.
- **Credibility:** acceptable only as a high-variance provisional research budget. B/C/F/G retain explicit XL gates and mandatory re-estimation points; this review found no additional path-independence or provenance-interface obligation requiring another numerical increase.

## Exact changes required for round 12

1. **Harden successful-unit execution.** Add one runner helper that captures spike/positive output, requires process status 0, rejects any `Error:` diagnostic, and prints diagnostics on failure. Do not trust `set -e` alone with Idris 0.8.0.
2. **Provide a genuinely fresh suite mode.** Delete the exact 5+53 module TTC/TTM paths under the discovered root `$TTC_ROOT/DGamma` (or use an isolated empty build root), then require 5 spike + 27 positive successful build markers. Keep execution serial.
3. **Fix all-once auditing.** Parse runner entries as lists, assert lengths 5/27/26, reject within/cross-category duplicates, and compare all 53 test paths against `git ls-files`, not only `Path.glob` sets.
4. **Either broaden or rename the claims auditor.** A broad auditor must check exact CP3/source diff, package reachability, production/test escapes, 6/4/11/9/2 hole split, eight exact phase rows/sum, tracked scripts/spikes/tests, and invoke the hardened suite. Otherwise label it clearly as `inventory` rather than claiming substantive verification.
5. **Repeat closure after harness-only repair.** Forced fresh serial suite, sampled exact negative diagnostics, best-effort unseeded plus seeded 207/207, immutable production diff, escape/reachability scans, and clean tracked/index state. No O6/O9/path-independence type redesign is required by this review.

## Final verdict

**ACCEPT-WITH-CHANGES.** The round-10 interface blockers are repaired: genuine adversarial type probes could not launder prefix or deletion provenance, and per-derivation authority is sufficient for the immutable existential theorem. The plan's proof interfaces are ready; authorization should remain conditional on the two concrete validation-harness repairs above, because both the runner and auditor currently admit false-positive scenarios.

**Final verdict: ACCEPT-WITH-CHANGES**

### Probe 44 — final report integrity and acceptance state
- **Command:** inspect the final report tail; locate required closing sections/verdict; count/hash report; recheck staged/tracked counts and status.
- **Result:** Findings, residual risks, estimate, exact round-12 changes, and verdict are present. Before this entry the report was 300 lines, SHA-256 `7b7d0059...c3fca`; staged count 0 and tracked-diff count 0. Status contains only pre-existing `paper/` and this permitted report.
- **Classification:** **note** — report artifact and no-staged-files evidence confirmed.

**Final verdict: ACCEPT-WITH-CHANGES**
