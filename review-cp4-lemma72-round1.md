# Adversarial review: CP4 Lemma 72 deletion theorem, round 1

- Target: `ddcabf1fb110f26053c680683254bd3b5e055f00`
- Accepted statement baseline: `b7f12c9`
- Scope: `src/DGamma/CP3.idr`, `src/DGamma/CP4DeletionTheorem.idr`, dependencies, paper Section 7.
- Reviewer stance: fresh-context adversarial review; no implementation changes.

## Probe 0 — repository baseline

**note** — The requested HEAD is checked out exactly. The pre-existing worktree has unrelated untracked `paper/` and `review-cp3-round10.md`; this review will not touch them. Evidence: `git rev-parse HEAD` returned `ddcabf1fb110f26053c680683254bd3b5e055f00`; `git status --short` listed only those two pre-existing paths before creation of this report.

## Probe 1 — paper interface and drift inventory

**note** — Paper Lemma 72 (`paper/cordis-paper.txt:2262-2297`) quantifies over a pairwise-independent trace reaching quiet/no-failure, a closing episode `[b,u]`, no closing higher-precedence episode, and no episode for names registered by the selected fiber; its conclusion is a replay obtained by deleting the selected episode actions and all actions on generated names, ending `≈`-equal and `≃`-equal outside `R`. Lemma 71 is the adjacent transposition dependency (`:2235-2261`), and Theorem 73 consumes deletion (`:2298-2307`).

**note** — The baseline-to-target diff is exceptionally broad: 205 files, including 972 changed lines in `src/DGamma/CP3.idr` and 63,592 insertions overall. This substantially increases statement-drift risk and requires definition-by-definition review rather than relying on the earlier statement acceptance. Evidence: `git diff --stat b7f12c9..ddcabf1` and the 3,429-line focused CP3 diff saved outside the repository as `/tmp/cp3-drift.diff`.

## Probe 2 — exact public-statement comparison

**major (provisional, requires semantic review before verdict)** — Contrary to the literal “TYPE is unchanged” check, `deletionTheorem` is not syntactically unchanged from accepted baseline `b7f12c9`. Baseline `src/DGamma/CP3.idr:3020-3047` (as shown by `git show b7f12c9:...`) used raw `List name`, `RegisteredNamesDuring`, raw `NoRegisteredEpisode`, `ActionSubsequence`, `ControlEquivalentOutside`, and raw withdrawal. HEAD `src/DGamma/CP3.idr:3718-3750` instead quantifies exact `RegistrationGeneration`s plus start scan state and returns generation-aware filtering/control/withdrawal (`:3373-3693`). The focused diff is `/tmp/deletion-statement.diff` and demonstrates a real public type change, not visibility-only drift. It is, however, explicitly documented as the Finding-#8 same-raw-name repair in `NOTES.md:317-339`, so it is not *silent*. I defer final severity until executable reissue probes and extensionally-faithful review establish whether the change is a necessary strengthening/correction or itself invalidates the accepted interface.

**note** — The repaired output remains constructive: `DeletionResult` still packages three checked survivor trace segments, a forced keep/delete witness, effect relatedness, controls outside `R`, and withdrawal; HEAD adds exact generation scans. No identity-replay shortcut is visible in the record shape (`src/DGamma/CP3.idr:3642-3693`).

## Probe 3 — dependency-change inventory and available checker

**note** — Post-baseline CP3 changes are concentrated in support fixed-point machinery, repaired trace totality, runtime/accumulator relatedness, generation-aware deletion, and a few export changes. `cf57379` replaced Prelude `all` by the local executable `allList`; subsequent commits renamed the old uninterrupted Definition-69 predicate and made `TraceComponentsTotal` inspect checked transition endpoints. The commit history explicitly labels these semantic repairs rather than hiding them.

**note** — Idris 2 v0.8.0 is available and warm artifacts include both `build/ttc/2025081600/DGamma/CP3.ttc` and `.../CP4DeletionTheorem.ttc`. Executable/type-level probes will use one checker process at a time and external directory `/tmp/dgamma-review-probes/`.

## Probe 4 — `allList` equivalence attempt (tool invocation retry needed)

**note** — The first external checker invocation failed before elaboration because Idris 2 v0.8.0 rejected `-i build/ttc/...` in that argument position (“Expected at most one input file”). This is a command-line/tooling failure, not proof evidence. Probe source is `/tmp/dgamma-review-probes/AllListProbe.idr`; no repository file was changed. I will retry with the supported package/source-path invocation.

## Probe 5 — Idris path-option discovery

**note** — `idris2 --help` confirms this v0.8.0 binary has no `-i`; import search must use `IDRIS2_PATH`, a package, or `--source-dir`. The failed Probe 4 was therefore conclusively an invocation error.

## Probe 6 — external source-root retry

**note** — The second `allList` probe invocation again failed before elaboration: running from the package root made Idris enforce that the input live under that source directory. Evidence: “Source file ... is not in the source directory .../dgamma”. No claim about the code follows; next retry runs from `/tmp/dgamma-review-probes` with absolute `IDRIS2_PATH`.

## Probe 7 — warm TTC import-path retry

**note** — `IDRIS2_PATH` pointed directly at the versioned warm TTC root did not resolve `DGamma.CP3`; Idris reported “Module DGamma.CP3 not found”. This v0.8.0 setup apparently expects source lookup (or installed package metadata) rather than that raw TTC root. Probe remains unelaborated; next run uses the repository `src` path while keeping the probe/build output external.

## Probe 8 — source-path and cache-layout diagnosis

**note** — `IDRIS2_PATH=/.../src` likewise did not resolve modules in this brew v0.8.0 invocation. `idris2 --paths` shows lookup via the current source directory and local `build`, while the warm cache is 943 MB. I will avoid copying it and instead create only external symlinks to the repository source and warm `build/ttc` cache, so any generated probe artifact remains outside the repository.

## Probe 9 — first elaborated `allList` equivalence attack

**note** — External import setup now works via source/TTC symlinks entirely under `/tmp/dgamma-review-probes`. The naive structural proof that local `allList` definitionally equals `Prelude.all` failed: Idris exposes Prelude `all` as a `foldl` over monoidal conjunction, not the same reduction tree. This is not a counterexample—only evidence that the substitution is not definitionally equal and needs an extensional proof. The unrelated sample also used undefined `even`. Exact checker diagnostics are retained in the command transcript; no repository artifacts were written by the probe.

## Probe 10 — universal `allList` extensional proof (auxiliary sample parse failure)

**note** — The universal proof body elaborated: helper `foldAllAcc` proves Prelude's fold-left conjunction equals an accumulator conjoined with local `allList`, and `allListMatchesPreludeAll` derives equality for every predicate/list. The file still failed overall only because the separate erased sample declaration implicitly rebound/shadowed its lowercase top-level name under Idris syntax. I will remove that irrelevant sample and recheck. This strongly indicates `cf57379` is extensionally faithful despite lacking definitional equality.

## Probe 11 — `allList` substitution passes universally

**note** — `/tmp/dgamma-review-probes/AllListProbe.idr` fully typechecks. It proves
`DGamma.CP3.allList predicate xs = Prelude.all predicate xs` for arbitrary element type, predicate, and list via a total fold-accumulator lemma. Therefore the `cf57379` support-clause substitution is extensionally faithful; it is not a semantic blocker.

## Probe 12 — independent full escape-hatch scan

**note** — Full anchored scan of all 207 `src/**/*.idr` modules found zero `believe_me`, `assert_total`, postulate declarations, `%default partial`, `%default covering`, named holes, or explicit `partial` declarations. Every 207 module contains exact `%default total`. Unanchored `partial` hits are documentation about mathematical partial maps; `void` hits are ordinary eliminations from explicit contradictions. A separate hole-syntax scan returned empty. No escape-hatch blocker found.

**note** — `git diff --check` is clean. Worktree status now lists only pre-existing untracked `paper/`, pre-existing `review-cp3-round10.md`, and this required review file.

## Probe 13 — failed-close runtime probe, first elaboration

**note** — The first failed-close probe reached elaboration but used the wrong accessor: `fire` returns `TransitionResult` (`Calculus.idr:5850-5868`), whose endpoint is `transitionAfter`, not deletion-layer `namedAfter`. The checker rejected only that undefined name; the probe is being corrected. No semantic result yet.

## Probe 14 — failed-close endpoint pattern refinement

**note** — The corrected probe exposed an Idris dependent-pattern issue when matching the concrete `ColdError` through an existential `Fiber`; the checker reports a postponed polymorphic pattern. This is not rejection of the failed close. The probe will instead match `Inactive (Just failure)`, which is the exact property under attack and avoids naming the existentially transported error value.

## Probe 15 — failed-close removal check import refinement

**note** — After the dependent-pattern repair, elaboration progressed through failed `LUnload`, `ORetire`, and `ORemove` branches and stopped only because `bindings` was not imported. Adding `DGamma.Coeffects` will expose that endpoint observer.

## Probe 16 — failed-close final dictionary alignment

**note** — The probe now elaborates through the full schedule but `quiet` could not infer `DecEq` dictionaries from the existential transition result. This is the same proof-dictionary alignment issue modeled by `AlignedTransitions`, not a semantic failure. The final check will pass `@{failureNameEq}` and `@{failureKeyEq}` explicitly.

## Probe 17 — explicit `DecEq` interface import

**note** — Explicit dictionaries were accepted syntactically, but the standalone probe had not imported the public `DecEq` interface module itself. The checker reports the interface name unavailable, so I add `Decidable.Equality`; still no semantic rejection.

## Probe 18 — standalone interface dependency completion

**note** — The remaining standalone elaboration error is missing public `Data.List.Elem.Elem` needed when unfolding the `quiet` dependency check. Adding that base import should complete the probe; again, all lifecycle branches already elaborate.

## Probe 19 — failed-close schedule elaborates; definitional proof does not normalize

**note** — With imports complete, the full executable failed-close → retire → remove schedule typechecks except for the optional `Refl` assertion that the nested proof-producing `fire` computation normalizes definitionally. Idris leaves `fire`/well-formedness checks opaque enough that `Refl` cannot close the Boolean. This is not a failed evaluator branch. I remove only that assertion and execute `main` to observe the runtime Boolean.

## Probe 20 — executable failed close succeeds and is cleaned by suffix

**note** — `/tmp/dgamma-review-probes/FailedCloseProbe.idr` executed and printed `True`. Starting from the checked `L-Raise` state in `CP4FailureOutcomeChecks`, the selected `LUnload` succeeds to `Inactive (Just failure)`, then checked `ORetire` and checked `ORemove` succeed, producing an empty quiet, failure-free endpoint. This concretely refutes the suspected “only clean closes are representable” vacuity.

**note** — Source inspection matches the executable case: `PostCloseSelectedBoundary` deliberately records merely `InactiveFiberAt` with arbitrary outcome (`src/DGamma/CP4DeletionSelectedCloseBoundary.idr:130-160`); `selectedUnloadClosesPostBoundary` carries the exact `outcome : Maybe error` into `Inactive outcome` (`:209-443`). The suffix fold either discharges selected `ORemove` (`CP4DeletionPostCloseFold.idr:337-365`, `CP4DeletionPostCloseRemove.idr:201-333`) or, at an unremoved endpoint, uses `noFailedFibers` to eliminate `Just failure` (`CP4DeletionPostCloseFinal.idr:80-171`). This is honest failed-close support, not an impossible-premise shortcut.

## Probe 21 — public proof import, quantity mismatch

**note** — An external alias without quantity annotation could not access `deletionTheoremProof`, despite its `public export`, because the proof is declared at quantity 0 (`CP4DeletionTheorem.idr:148-149`) while the alias defaulted to runtime quantity. This is expected Idris erasure enforcement, not a visibility bug. The next alias is also quantity 0.

## Probe 22 — proof inhabitant imports at the exact public type

**note** — `/tmp/dgamma-review-probes/PublicProofProbe.idr` typechecks after matching quantity 0. The external module imports the built package and checks `publicProofHasExactPublicType : deletionTheorem name key value world error; publicProofHasExactPublicType = deletionTheoremProof`. This attests that the exported inhabitant closes the exact HEAD public type with no hidden module-local premise.

## Probe 23 — Finding-#14 countermodel attack, dictionary-name retry

**note** — The first executable crossing-provider attack failed to elaborate only because it referenced non-exported convenience names `toyNameEq`/`toyKeyEq`. The concrete `DecEq` implementations are available through `%search`; I will retry with inferred dictionaries. The probe schedule is: reach active provider P and active committed consumer A, try to insert same-provision S; then put P into Unloading, retry S insertion, and attempt P's L-Unload while A relies.

## Probe 24 — crossing-provider instance visibility retry

**note** — `%search` could not see `DecEq ToyKey` because the defining module `DGamma.Section3Example` was not directly imported by the standalone probe (transitive imports do not re-export all instance names here). Adding that direct import addresses only probe visibility.

## Probe 25 — crossing-provider attack returns `False`; branch diagnostics needed

**note** — The first runnable Finding-#14 attack printed `False`. This does not establish a countermodel: the conjunction hides whether the initial state failed, insertion unexpectedly succeeded, L-Leave was itself blocked, or an unloading guard differed. I will print branch diagnostics before drawing any finding.

## Probe 26 — crossing-provider diagnostics identify stronger guard

**note** — Diagnostics printed `[True, True, False]`: the committed provider/consumer setup exists; insertion of same-provision S is rejected; and provider P cannot even take L-Leave while relied upon (rather than reaching Unloading and failing only at L-Unload). Thus the intended countermodel is blocked earlier than NOTES' prose, not admitted. I adjust the pass condition to exactly these observed guards.

## Probe 27 — Finding-#14 countermodel is executablely refuted

**note** — `/tmp/dgamma-review-probes/CrossingProviderProbe.idr` now prints `True`: with active provider P and active consumer A committed to P, checked O-Insert of same-provision S is `Nothing`, and checked P L-Leave is also `Nothing` while A relies. This executable probe refutes the insertion/withdraw/reissue route underlying the proposed countermodel.

**note** — The proof does not merely assume the result. `committedProviderProvisionPersists` structurally recurses over an `InstalledTrace`, transporting the fixed committed list and static component through every checked installed step (`src/DGamma/CP4DeletionCommittedProviderPersistence.idr:42-96`). `crossingActivationExcludesSelectedProvider` turns a hypothetical current selected candidate into a committed current selection, transports it to the actual consumer L-Begin boundary, reconstructs `ResolvedProviderData` and a `PrecedenceEdge selected actor`, then applies the unchanged public `NoDependentClosingEpisode` (`CP4DeletionSelectedForeignLifecycleCrossing.idr:56-158`). `DirectProviderFrameEvidence` is therefore a genuinely quantified exclusion function, not an unconstrained trivial witness (`CP4DeletionSelectedForeignLifecycleProviderFrame.idr:26-62`). No blocker found on Finding #14.

## Probe 28 — exact-generation same-name reissue regression

**note** — `/tmp/dgamma-review-probes/GenerationReissueProbe.idr` imports the repository regression and prints `True`. The ten-step checked schedule removes a generated child generation and inserts a quiet, non-retired root generation at the same raw name; `generationFilterPreservesReissue` keeps the latter exact transition while the diagnostic raw filter deletes it (`src/DGamma/CP4DeletionGenerationChecks.idr:96-157,169-230`). This confirms the public generation change is a necessary paper-fidelity repair rather than weakening the deletion conclusion.

**note** — Endpoint withdrawal is exact-generation sensitive. `CurrentRegisteredWithdrawable` requires a final `lookupCurrentGeneration actor live = Just generation` before demanding retired/inactive/empty evidence (`CP4DeletionEndpoint.idr:26-41`). `currentGenerationAtScanStart` proves an old birth cannot be recreated by a later insertion because its birth ordinal is strictly below the scanner ordinal (`CP4DeletionWithdrawalCurrent.idr:16-104`). The retirement join locates the promised post-birth `ORetire`, persists it only while that exact generation remains current, and treats removal/reissue as historical rather than applying retirement to the new generation (`CP4DeletionWithdrawalJoin.idr:145-219,259-505,507-609`; `CP4DeletionRetirementPersistence.idr:110-203`). No exact-generation blocker found.

## Probe 29 — vestigial endpoint scenarios

**note** — `/tmp/dgamma-review-probes/VestigialProbe.idr` prints `True` for `allCP3VestigialChecks`. This covers both no-remove and later-lifecycle vestigial scenarios, generation correspondence, and live-provider behavior (`src/DGamma/CP3VestigialChecks.idr:1113-1119,1400-1412,1961-1968,2070-2086`). The endpoint relation does not require R remnants to vanish from the original; it requires exact retired/uninstalled/empty certificates when current and absence from the survivor (`CP3.idr:3590-3636`). No vestigial-leftover vacuity found.

## Probe 30 — whole-package validation

**note** — `idris2 --build dgamma.ipkg` at target HEAD completed successfully (exit 0) with the warm cache. Together with the external exact-public-type probe, this confirms the tracked proof graph typechecks as packaged.

## Probe 31 — premise-use and statement-hash audit

**note** — Lexical use counts in `deletionTheoremProof` show `finalQuiet` and `componentsTotal` occur only in the left-hand-side binder and are not consumed; `finalNoFailed`, independence, discipline, initial well-formedness, and initial emptiness are consumed downstream. This is not vacuity: the proof establishes a stronger result that does not need the paper's quiet/total assumptions once the explicit no-dependent-close and selected-unload reliance arguments are available. The ignored premises do not make inputs impossible or conclusions trivial.

**minor** — `NOTES.md:2292-2295` says the inhabitant has the “unchanged public `deletionTheorem` type,” but exact baseline/current statement-block SHA-256 hashes differ (`32ffd2...` vs `25aeea...`) and Probe 2 gives the concrete type diff. The generation-aware drift is documented and semantically justified elsewhere, so this is a status-wording defect, not a proof blocker. The provisional major in Probe 2 is downgraded to this minor after Probes 11 and 28 established the key substitutions/repair.

## Probe 32 — repository mutation guard

**note** — After all builds/probes, `git status --short` still lists only the two pre-existing untracked paths plus this review file; `git diff --name-only` is empty and `git diff --check` passes. No repository source/build configuration was modified.

## Probe 33 — repaired Definition-69 drift regression

**note** — `/tmp/dgamma-review-probes/TotalityRepairProbe.idr` prints `True` for `allCP4TotalityChecks`. The suite executes the foreign-interleaving counterexample accepted by the old uninterrupted predicate, proves repaired trace totality rejects that schedule, and accepts an actually total interleaving (`src/DGamma/CP4TotalityChecks.idr:239-343`). Thus the post-baseline `TraceComponentsTotal nameEq keyEq trace` change is a documented semantic correction, not a silent weakening used to fake Lemma 72.

## Probe 34 — forced-opening deletion proof, indexed-constructor retry

**note** — The first dependent classification datatype for the episode opening was over-indexed: Idris could not infer one implicit rest state and rejected it before checking the elimination. This is probe-design failure, not evidence about the implementation. I will simplify the result to a dependent pair consisting of the required head-deletability witness and the tail subsequence, which directly expresses that the first original transition was deleted.

## Probe 35 — forced-opening deletion pattern-name retry

**note** — The simplified theorem is accepted through result elaboration; its left-hand side failed only Idris's same-index pattern-variable naming rule (`rest` necessarily unifies with constructor `originalRest`). I will use the same name in both nested patterns.

## Probe 36 — forced-opening deletion transition-index retry

**note** — Idris next requires the constructor's `originalTransition` pattern to be named identically to its forced index `beginTransition openingStep`. I will pattern it with that exact expression; this remains elaboration bookkeeping.

## Probe 37 — forced-opening deletion coverage retry

**note** — Exact-expression patterns typecheck locally but the separate explicit `surviving` argument causes the coverage checker to enumerate hidden endpoint cases. Making the survivor trace an implicit index of the subsequence witness removes that redundant split and should yield the intended two-constructor proof.

## Probe 38 — forced-opening deletion case-tree retry

**note** — The coverage checker still over-splits nested dependent left-hand patterns (16 apparent action cases). I will move the constructor split into a right-hand `case witness`; this lets elaboration retain the already-fixed original head index without re-patterning it.

## Probe 39 — forced-opening deletion case index naming

**note** — The right-hand case removes the coverage complaint but still enforces exact naming of the fixed transition/rest indices. I will use `(beginTransition openingStep)` and `rest` directly in both constructors.

## Probe 40 — selected opening is structurally forced deleted

**note** — `/tmp/dgamma-review-probes/ForcedDeletionProbe.idr` fully typechecks. For an arbitrary episode filter witness, `openingIsForcedDeleted` returns the exact head-deletability certificate plus the tail subsequence. Its `KeepGenerationAction` branch is eliminated by applying the mandatory complement proof to `DeleteEpisodeGenerationLifecycle Refl Refl`. Therefore `DeletionResult.episodeDeletion` cannot be inhabited by an identity/keep-at-opening trick; the selected episode's checked L-Begin is structurally erased.

## Final assessment

### Statement drift

The public type is **not textually unchanged** from `b7f12c9`; Probe 2 caught that. The change is also not extensionally identical under raw-name reuse: HEAD keeps a later generation at the same raw name, while the accepted raw-name filter erased it. I do not classify this as a blocker because:

1. it is explicitly recorded as CP4 Finding #8 (`NOTES.md:317-339`), rather than silent;
2. the paper LTS permits reissue after O-Remove (`paper/cordis-paper.txt:1281-1289`), making the paper's later raw-name wording itself ambiguous;
3. the checked reissue counterexample demonstrates the accepted raw filter was wrong (Probe 28);
4. current `RegisteredGenerationsDuring` is complete in both directions, so callers cannot choose a convenient incomplete `R` (`src/DGamma/CP3.idr:3505-3520`); and
5. filtering, no-episode evidence, outside control agreement, and withdrawal all consistently use the same exact generation stamp through the final result (`CP3.idr:3373-3693`).

This round therefore re-attests the repaired HEAD statement. The only reportable defect is the misleading “unchanged” wording in the final NOTES status.

### Vacuity and proof integrity

- `SelectedEpisodeReplayBoundary` carries an actual accumulator model/run, complete current-R plan, ordered controls, and the exact clean-Inactive survivor (`src/DGamma/CP4DeletionSelectedBoundary.idr:364-401`); it is not an unconstrained relation.
- `PostCloseSelectedBoundary` permits arbitrary `Inactive outcome`, including failure, and the suffix must remove it or contradict final no-failure (Probe 20).
- The relational suffix propagates exact ambient/table binding equality plus ordered full control relatedness; `replayRelatedAction` exhaustively dispatches all eight `Action` constructors, with L-Advance split across empty finish/divert, raise, iter, successful finish, and landing divert (`CP4DeletionRelationalSuffixFold.idr:64-393`; `CP4DeletionRelationalActionReplay.idr:20-58`; `CP4DeletionRelationalLifecycleAdvanceDispatch.idr:20-337`). There is no exact-state shortcut or fallback premise.
- The selected opening is forced through the delete constructor by the keep-complement proof (Probe 40).
- The committed-provider/crossing and exact-generation retirement arguments survive their executable attacks (Probes 27-29).
- `CP4DeletionEndpoint` composes original-to-plan effect preservation with the final relational boundary, derives controls for every current generation outside R, and distinguishes current vestigial withdrawal from historical closure (`src/DGamma/CP4DeletionEndpoint.idr:138-219`).
- `assembleDeletionResult` copies the actual filter traces/scans and the three independently derived endpoint fields without weakening (`src/DGamma/CP4DeletionSkeleton.idr:102-161`).

### Paper/interface fidelity

HEAD universally quantifies the complete checked trace and returns a checked survivor trace obtained by forced deletion, exact effect recovery (`≈` strengthened to exact ordered runtime effect bindings), full control relation outside exact R generations, and current/historical withdrawal evidence. `TraceIndependent` supplies failure-aware yielded/inverse provenance, and the selected effect boundary runs the concrete accumulated inverse rather than an arbitrary map (`src/DGamma/CP4DeletionSelectedEffectCore.idr:17-126`; `CP4DeletionSelectedCloseEffect.idr:13-56`).

The finite runtime adds already-documented explicit premises—empty-start reachability, dictionary alignment, registration protocol/discipline, and trace-indexed totality. No new hidden premise is introduced by `deletionTheoremProof`. The proof actually leaves final quietness and trace totality unused; this strengthens rather than weakens Lemma 72 under the remaining premises.

### Residual risks

1. The proof graph is very large. This review checked the public inhabitant, priority boundaries, all action dispatch, endpoint join, and executable adversarial cases, but did not line-audit every helper among the 160+ imported deletion modules.
2. Validation used the requested warm cache. A clean/cold archive rebuild was not attempted.
3. The repository has no single concrete example that supplies every public Lemma-72 premise and then evaluates projections of `deletionTheoremProof`; the external probes instead exercise failed close, provider crossing, same-name reissue, vestigials, totality drift, forced deletion, and exact exported typing separately.
4. The generation-aware repair is necessarily a clarified reading of paper Lemma 72's raw-name `R`, not a textually identical statement. Future Theorem-73 work must keep that interpretation consistent.

## Verdict

**ACCEPT** — no blockers and no open majors.

Open findings: **0 blocker, 0 major, 1 minor, 47 notes**. One provisional major label in Probe 2 was explicitly downgraded after semantic/executable review.

## Final repository attestation

The last post-review check still reports HEAD `ddcabf1fb110f26053c680683254bd3b5e055f00` and only untracked `paper/`, `review-cp3-round10.md`, and this required report. No tracked source changed.

## Verdict (final)

**ACCEPT** — 0 blocker, 0 open major, 1 minor, 47 notes. The sole provisional major was downgraded after the generation-reissue and extensional-equivalence probes.
