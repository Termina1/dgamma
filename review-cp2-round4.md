# Checkpoint 2 adversarial review — round 4

**Target:** `8823cc429ce4e6538b35eb3560d7fa102d07b95a` (`document completed checkpoint 2 proof bar`)
**Scope:** paper Section 4 through Theorem 64; final round-3 bar audit, executable full-effect-state countermodels, raw Preservation proof, whole-episode resolution structure, remaining statement-only types, documentation, and clean-archive validation
**Mode:** adversarial review only; no source edits and no commit

## Review status

In progress. This report is being written incrementally.

## Baseline

- Confirmed `HEAD` is exactly the requested commit `8823cc4`.
- Pre-review working tree contained only the pre-existing untracked `paper/` directory; this report is the only review-created repository file.
- Read `review-cp2-round1.md`, `review-cp2-round2.md`, and `review-cp2-round3.md` in full.
- Round-3 acceptance bar under review: full-`EffectState` recovery surviving actual-handle countermodels; raw Theorem 59 proved; whole-episode first-exit split proved; global `orderingTheorem` allowed to remain explicitly documented CP3 debt.

## Validation performed (incremental)

- `idris2 --version`: **Idris 2 0.8.0**.
- Created fresh `git archive 8823cc4` at `/tmp/dgamma-cp2-round4.I3K3V9`, ran `idris2 --clean dgamma.ipkg && idris2 --build dgamma.ipkg`: all eight package modules rebuilt and **passed**.
- Diffed Definition 58's executable clauses against round-3 commit `fd9677d`. The old four checks (`parentInvariant`, fuel-bounded `parentChainInvariant`, `pairwiseProvisionInvariant`, `fiberViewInvariant`) are unchanged semantically; `all` was refactored into explicit recursive `parentsInvariant`/`chainsInvariant`/`viewsInvariant` folds for frame proofs. The pre-existing strengthening—providers must be Active/Unloading and contain each committed key—remains. No clause was dropped or weakened.

### Round-3 actual-handle attack re-run

- Added a review-only executable `FullEffectExecutableProbe.idr` in the clean archive. It reuses the round-3 malicious witnessed inverse: at its exact application state it restores correctly, but after a foreign consumer-bit toggle it deliberately retains the selected `ServiceA` table.
- The reachable prefix and closed runs still end with the malicious wrong table, confirming the probe did not accidentally sanitize the countermodel.
- In the redesigned API, however, `accumulatorEffectMap`/the selected L-Unload map and the foreign L-Finish map compose to observably different full `EffectState`s: one order has `ServiceA=True` at actor 0 and the other has no `ServiceA`. Thus the exact `PartialCommute (EffectStateEquivalence keyEq)` premise required by `PrefixRecoveryIndependent` and `TraceIndependent` rejects the model. The same disagreement blocks instantiation of Theorem 61, Corollary 62, and recovery-combined Theorem 64.
- Executable output was `[True, True, True, True]`: prefix attack rejected by full-state noncommutation; closed attack rejected by full-state noncommutation; malicious terminal table remains wrong; actual handle's full-state map observes/retains that table. The round-3 actual-handle countermodel therefore does **not** survive.

### BLOCKER — full-state redesign still omits the yielded inverses required by paper Definition 60

**File:** `src/DGamma/Metatheory.idr:1154-1181,1260-1309,4041-4056`; discrepancy with paper Definition 60 / Equations 54–55

The full-`EffectState` redesign closes the round-3 *projection* bug, but `TraceIndependent` still quantifies only the Table-1 maps of transitions that occur, and `PrefixRecoveryIndependent` quantifies only the **final composite accumulator** against each foreign transition map. Neither premise requires each inverse yielded by a selected iteration to commute with foreign maps. Paper Definition 60 explicitly places every yielded inverse of every reachable iterator in the generated monoid (Equation 54), then requires cross-component monoid commutation (Equation 55). Commutation of a composite does not imply commutation of its factors.

A new review-only executable `CompositeAccumulatorProbe.idr` constructs a reachable checked run over a four-state ambient world:

1. selected iteration `A1`: `Q0 -> Q1`, yielding permutation `G = (Q0 Q1)(Q2 Q3)`;
2. foreign iteration `F`: `Q1 -> Q2`;
3. selected iteration `A2`: `Q2 -> Q3`, yielding the same `G`;
4. selected accumulator is therefore `G . G = id` and L-Unload leaves `Q3`;
5. replaying only the foreign iteration from the episode opening gives `F(Q0) = Q1`.

Both selected forward maps and the foreign forward map are the same cyclic increment, so all actual Table-1 maps commute; the final selected accumulator/L-Unload map is identity, all maps are total, and the run is well formed. Each yielded inverse is nevertheless witnessed at its exact application state, as required by `StepEffect.stepWitness`. The missing fact is exactly that `G` itself does not commute with `F`.

The probe printed `[True, True, True, True, True, True]`: opening well formed; every trace map total; every encoded trace map pairwise commuting on the exhaustive four-state world; exact endpoint accumulator identity; terminal actual world `Q3`; foreign replay world `Q1`. Unlike the round-3 attack, this uses no table projection mismatch: empty provisions make full effect state observationally just the ambient world. It therefore falsifies the current Theorem-61 premise/conclusion pattern and, with the closed extension, Corollary 62 and recovery-combined Theorem 64.

This is a **surviving countermodel and a checkpoint blocker**. The repair must constrain every yielded inverse (and reachable continuation), not merely the final accumulator or actual forward/Table-1 maps—e.g. restore a full-effect-state form of paper `M(i)`/Equation 55, or carry per-yield commutation certificates in the trace.

## Raw Preservation audit

**Judgment: genuine and bar item met.**

- `preservationTheorem` (`src/DGamma/Metatheory.idr:779-790`) has the raw paper shape: source `registryWellFormed = True`, a raw `applyAction ... = Just (tag, afterState)` equation, and target `registryWellFormed = True`. It does not mention `checkedApplyAction`, `Transition`, or target admission.
- `preservationTheoremProof` (`:792-814`) exhausts all eight `Action` constructors; `LAdvance` internally exhausts the four Table-1 landing tags, giving all ten rules. Every branch consumes the source invariant and raw equation. A scan of the proof region found no call to `checkedApplyAction`, `checkedActionTargetValid`, or `checkedTransitionTargetValid`.
- **O-Remove:** `chainsInvariantDeleteCardinal` (`src/DGamma/Calculus.idr:2809-2849`) explicitly proves the one-entry length decrement, rewrites old fuel `S oldLength` to `S (S targetLength)`, excludes the removed name from the availability list, uses the raw no-child guard to show no surviving chain traverses it, then produces the target fold at `S targetLength`. Parent closure, provisions, and committed views are separately deletion-closed. This is a real cardinal/fuel proof, not a hidden target premise.
- **L-Advance:** `preservationLAdvance` (`src/DGamma/Metatheory.idr:547-663`) splits missing fiber, all lifecycle phases, empty-rest target match/mismatch, capability resolution, raise, successful target mismatch, finish, and iter continuation. `preservationReloadingRuntime` frames parent/chains/provisions and derives all view facts from source well-formedness. Its key premise `stableProvider source = False` is established by the source being Reloading; therefore no already-valid foreign committed view may name the table-mutating actor. There is no strengthened caller premise.
- **Guarded L-Unload:** `preservationLUnload` (`:719-777`) eliminates `relied=True` directly from the raw evaluator equation. `viewsInvariantUnloadingInactive` and its recursive `fiberViewUnloadOther` machinery (`src/DGamma/Calculus.idr:4450-4720`) convert `relied=False` into exclusion of the leaving name from every other installed committed view before replacing it by Inactive. This proves the hard Definition-58(4) case rather than assuming it.
- **Definition 58 diff:** round-3 `fd9677d` and HEAD check the same parent closure, acyclicity, pairwise provision disjointness, and committed-view validity. HEAD only replaces opaque `all` folds with named recursive folds. The existing strengthening (provider Active/Unloading and matching key in its table) remains intact. No invariant weakening was used to obtain the proof.

The mechanized invariant is stronger than paper Definition 58 in two documented ways—explicit acyclicity and key/table validity/stable provider phase—but these predate this proof pass and were not weakened. Within that declared restricted calculus, raw Theorem 59 is proved honestly.

## Whole-episode resolution-structure audit

**Judgment: genuine and bar item met (independent of the recovery blocker).**

- `ResolutionStructure.ExitedReloading` (`src/DGamma/Metatheory.idr:3935-3960`) carries an exact trace decomposition `initialPart ++ exitStep ++ remainingPart`, proves Reloading at every state of `initialPart` including `exitBefore`, proves Equation-59 coherence there, preserves the opening committed-provider list over the **whole** trace, and supplies one `StructuralExit` of exactly Finish, aborting Divert, landing Divert, or Raise shape. Because every structural exit lands Active or Unloading and no rule re-enters Reloading inside the same installed episode, this is the first and only Reloading exit.
- `StillReloading` is not an easy escape for an exited prefix: it requires `ReloadingThroughout` at both endpoints and every intermediate state. It correctly covers a final/open episode prefix that still ends in flight; after any exit only `ExitedReloading` is constructible. On a closed episode, the exact following L-Unload makes a whole-inside `StillReloading` branch uninhabited.
- `classifyReloadingStep` exhausts all eight executable actions with selected/foreign name splits. Foreign actions and selected O-Retire continue with a reloading snapshot; selected L-Iter continues; selected Finish/Divert/Raise produce the four `StructuralExit` constructors; selected O-Insert/O-Remove/L-Begin/L-Leave/L-Unload are eliminated from the raw evaluator equation.
- `resolutionStructureInstalled` recursively prepends continuing steps. Once the tail has an exit it carries that same exit and decomposition through the prefix; it does not choose a later exit or discard the earlier one. `resolutionStructureTheoremProof` seeds the induction from the exact checked L-Begin snapshot.
- **Alignment/vacuity check:** `InstalledTrace` intentionally requires each `Fired` transition to carry the episode's exact `nameEq`/`keyEq` dictionaries. This excludes traces assembled with extensionally equivalent but definitionally different decision procedures, so it is a real representation restriction. It does not make the theorem empty. A review-only `AlignedResolutionProbe.idr` built a four-transition installed episode (selected L-Iter, foreign L-Begin/L-Finish, selected L-Finish) using one dictionary pair, constructed `EpisodePrefix`/`InstalledTrace`, and applied `resolutionStructureTheoremProof`; it typechecked and its executable state checks printed `[True, True, True]`. The submitted `CalculusChecks` use the same checked evaluator, although they still return `Maybe State` and do not themselves retain whole aligned trace witnesses.

Thus the proved result is the paper's structural initial-Reloading/first-exit dichotomy for the restricted finite, checked LTS; it is not a trivially satisfiable tag classifier. The remaining `resolutionCoherenceTheorem` is false only because it combines this sound structure with the false recovery premise described above.

A second version, `CompositeAccumulatorVoidProbe.idr`, uses an uninhabited key type. Its `EffectStateRelated` table clause is therefore vacuous for the correct reason (there can be no table key), and the four ambient values exhaust the entire observable full-effect state. It printed the same six `True` flags. This rules out an untested-table explanation for the countermodel.

## Remaining statement-only types

| Declaration | Round-4 disposition |
|---|---|
| Lemma 35: `OperationsRespectIndistinguishability`, `CoarsestRespectedEquivalence` | No new countermodel found; unchanged approved Section-3 statement debt. |
| Theorem 40: `distinctKeysIndependent` | No new countermodel found; still explicitly stated only. |
| Theorem 42: `MediatedIndependenceTheorem` | No new countermodel found; still explicitly stated only. |
| Theorem 61: `recoveryExactnessTheorem` | **False.** Composite-accumulator/yielded-inverse countermodel above. |
| Corollary 62: `terminalRecoveryTheorem` | **False.** `TraceIndependent` checks actual forward/Table-1 maps and the final L-Unload composite, but never each yielded inverse; the closed checked run satisfies the encoded map conditions and ends at `Q3` instead of replay `Q1`. |
| Theorem 63: `orderingTheorem` | No fresh countermodel found. The initial-empty/global decomposition, provider-finally-uninstalled premise, strict same-trace containment result, pre-LUnload constancy ranges, and relied guard block the prior name-reuse/unrelated-episode/post-close attacks. It remains restricted and unproved CP3 debt. |
| Theorem 64: `resolutionCoherenceTheorem` | **False through its `ForeignReplay` field.** The structural `ResolutionStructure` component survives, but the same closed composite-accumulator run defeats the embedded terminal recovery claim. |

The recovery failure is not caused by partial undefinedness, arbitrary handles, episode suffixes, L-Raise, or table projection. Every relevant map in the countermodel is total; the selected handle is the actual endpoint accumulator; the episode begins at checked L-Begin and closes at checked L-Unload; and the full effect state has no possible table keys.

## Documentation audit

- README's proved/stated labels are mechanically accurate: raw Theorem 59 and structural Theorem 64 are marked proved, global ordering and recovery-combined results are marked unproved/stated. It does not pretend that `orderingTheorem` has an inhabitant.
- NOTES has a substantial Checkpoint-2 history, a current `## Status`, an explicit statement-only inventory, and a clearly labeled global-ordering CP3 debt. The debt list includes indexed trace search/splitting, name-reuse boundary extraction, restricted Lemma-54 lifecycle/view frames, and the forward relied-guard argument, satisfying the round-3 documentation request.
- **MAJOR documentation defect:** README's Def-60 row maps `TraceIndependent`/`PrefixRecoveryIndependent` to paper Definition 60 without saying that yielded inverses and continuation/yield stability are absent, while NOTES treats “trace-specific rather than generated-monoid independence” as a benign partial deviation. The new countermodel shows that omission makes Theorems 61/62/64 false, not merely weaker or less reusable. The `README`/`NOTES` completed-proof-bar narrative and “precise” remaining recovery statements are therefore not semantically truthful at HEAD, despite honest `stated` labels.

## Clean build, checks, and escape-hatch audit

- Fresh archive clean build: **passed**, 8/8 package modules, Idris 2 0.8.0; repeated after all review probes.
- Submitted executable checks printed `[True, True, True, True, True, True, True, True, True, True]` for all nine individual CalculusChecks flags plus `allRuleChecks`.
- Review probes: old full-table attack rejection `[True, True, True, True]`; composite-accumulator countermodel `[True, True, True, True, True, True]`; uninhabited-key full-state variant `[True, True, True, True, True, True]`; aligned resolution probe `[True, True, True]`.
- Anchored scan found no `believe_me`, `assert_total`, postulate, named metavariable hole, `%unsafe`, unsafe IO, `%default partial`, or `%default covering`. Every one of the eight packaged modules has `%default total`; the package lists exactly those eight.
- TODO inventory is exactly seven explicit statement sites: Lemma 35 (two declarations under one site), Theorems 40/42/61/63/64, and Corollary 62.
- Repository `git diff --check` passed. No staged files exist. The only review-created repository file is this report; `paper/` was pre-existing and untracked.

## Per-round-3 finding disposition

| Round-3 finding / disposition | Round-4 result | Evidence |
|---|---|---|
| **BLOCKER:** world-only independence could not justify table recovery | **FIXED for that exact attack, but superseded by a new BLOCKER.** | Every recovery map/premise/conclusion now uses full `EffectState`; the old malicious table inverse is rejected by full-state noncommutation. The new composite-accumulator attack exposes omitted yielded-inverse commutation instead. |
| Actual endpoint handle binding | **STILL FIXED.** | `actualAccumulatorAt current = Just handle` fixes the exact dependent accumulator; neither probe chooses an arbitrary handle. |
| Post-LUnload ordering endpoint | **STILL FIXED.** | `OrderingResult` constancy remains over `closedInside`, not the Inactive endpoint. |
| L-Raise replay identity | **STILL FIXED.** | Full/world map dispatch retains L-Raise identity and submitted regression passes. |
| Raw Preservation was statement-only | **FIXED / PROVED.** | `preservationTheoremProof` proves the raw source-valid + `applyAction` equation implication without checked target admission. |
| Whole-episode structural exit was statement-only | **FIXED / PROVED.** | Aligned installed-trace induction returns the maximal initial Reloading prefix and first structural exit; adversarial alignment probe is inhabited. |
| Global provider ordering was sound but unproved | **UNCHANGED, ALLOWED CP3 DEBT.** | No fresh countermodel; README/NOTES mark it stated and catalog the required machinery. |
| Trace-specific independence weaker than paper generated monoids (round-3 residual risk) | **MATERIALIZED AS BLOCKER.** | `TraceIndependent` omits yielded inverses; final composite commutation is insufficient for recovery. |

## Acceptance bar

| Supervisor bar item | Met? | Round-4 judgment |
|---|---:|---|
| (i) Full-`EffectState` recovery redesign surviving countermodels | **NO** | It survives the old table-projection attack but fails the new reachable composite-accumulator/yielded-inverse countermodel. |
| (ii) Raw Theorem 59 Preservation proved | **YES** | Genuine proof over raw `applyAction`, source and target Definition-58 invariant. |
| (iii) Whole-episode first-exit split proved | **YES** | Genuine aligned-trace induction with exact decomposition and exit shapes. |
| (iv) Global `orderingTheorem` may remain statement-only as documented CP3 debt | **YES** | Status and required machinery are explicitly documented; no replacement local lemma is overclaimed as the global proof. |

## Final findings

1. **BLOCKER — `src/DGamma/Metatheory.idr:1154-1181,1260-1309,4041-4056`:** recovery independence omits each yielded inverse from paper Definition 60. A reachable checked four-state run has all encoded actual maps total and commuting and a commuting identity final accumulator, yet terminal recovery returns `Q3` while foreign replay returns `Q1`. Theorem 61, Corollary 62, and recovery-combined Theorem 64 are false.
2. **MAJOR — `README.md:108-112`; `NOTES.md:379-452`:** the Def-60 correspondence and completed-proof-bar narrative describe the trace-specific full-state premises as adequate/precise without disclosing that yielded inverses and continuation stability are absent and that this falsifies the recovery statements. Proved-vs-stated labels themselves are accurate.

## Residual risks

- Repairing only the final accumulator premise will not suffice; paper Equation 54's full generated monoids (or equivalent per-yield certificates) and yield/continuation stability are needed over `EffectState`.
- `InstalledTrace` requires definitionally identical `DecEq` dictionaries. It is inhabited under one runtime dictionary pair but excludes otherwise legal proof traces assembled with different coherent decision procedures.
- Global ordering remains nontrivial CP3 proof debt; nested registration, Lemmas 54–57 as complete declarations, observational transport, Progress, and Confluence remain outside CP2.
- Exact full-effect equality, finite iterators, and checked-LTS proof traces remain documented restrictions.

# Final verdict: REJECT

```acceptance-report
{
  "criteriaSatisfied": [
    {
      "id": "criterion-1",
      "status": "satisfied",
      "evidence": "Concrete BLOCKER and MAJOR findings cite DGamma.Metatheory, README, and NOTES; executable old-attack and new composite-accumulator probes, raw-Preservation branch audit, structural-exit audit, and residual risks are documented."
    }
  ],
  "changedFiles": [
    "review-cp2-round4.md"
  ],
  "testsAddedOrUpdated": [],
  "commandsRun": [
    {
      "command": "git archive 8823cc4 | tar -x ... && idris2 --clean dgamma.ipkg && idris2 --build dgamma.ipkg",
      "result": "passed",
      "summary": "Fresh archive rebuilt all eight packaged modules under Idris 2 0.8.0; repeated after probes."
    },
    {
      "command": "idris2 --source-dir src -o eval-all-checks src/EvalAllChecks.idr && ./build/exec/eval-all-checks",
      "result": "passed",
      "summary": "All nine individual CalculusChecks flags and allRuleChecks printed True."
    },
    {
      "command": "idris2 --source-dir src -o full-effect-executable-probe src/FullEffectExecutableProbe.idr && ./build/exec/full-effect-executable-probe",
      "result": "passed",
      "summary": "Printed [True, True, True, True]: redesigned full-state commutation rejects both variants of the round-3 table attack while preserving its malicious endpoint."
    },
    {
      "command": "idris2 --source-dir src -o composite-accumulator-probe src/CompositeAccumulatorProbe.idr && ./build/exec/composite-accumulator-probe",
      "result": "passed",
      "summary": "Printed six True flags for a reachable checked countermodel: well formed, all encoded maps total/commuting, final accumulator identity, actual Q3, replay Q1."
    },
    {
      "command": "idris2 --source-dir src -o composite-accumulator-void-probe src/CompositeAccumulatorVoidProbe.idr && ./build/exec/composite-accumulator-void-probe",
      "result": "passed",
      "summary": "Uninhabited-key full-effect variant printed the same six True flags, making the four ambient values exhaustive modulo EffectStateRelated."
    },
    {
      "command": "idris2 --source-dir src -o aligned-resolution-probe src/AlignedResolutionProbe.idr && ./build/exec/aligned-resolution-probe",
      "result": "passed",
      "summary": "Constructed an aligned four-step InstalledTrace/EpisodePrefix, applied resolutionStructureTheoremProof, and printed [True, True, True]."
    },
    {
      "command": "anchored escape-hatch, TODO(proof), package-module, and %default total scans",
      "result": "passed",
      "summary": "No escape hatches or named holes; seven explicit statement sites; all eight packaged modules total."
    },
    {
      "command": "git diff --check && test -z \"$(git diff --cached --name-only)\"",
      "result": "passed",
      "summary": "Repository diff check passed and no staged files exist."
    }
  ],
  "validationOutput": [
    "Idris 2 version 0.8.0",
    "Clean archive build: passed, 8/8 modules",
    "Submitted checks: [True, True, True, True, True, True, True, True, True, True]",
    "Old actual-handle table attack rejected: [True, True, True, True]",
    "Composite-accumulator countermodel: [True, True, True, True, True, True]",
    "Uninhabited-key full-state countermodel: [True, True, True, True, True, True]",
    "Aligned resolution structure probe: [True, True, True]"
  ],
  "residualRisks": [
    "Theorem 61, Corollary 62, and recovery-combined Theorem 64 are false because yielded inverses are absent from independence.",
    "InstalledTrace is definitionally DecEq-aligned; inhabited but narrower than all legal checked traces.",
    "Global ordering, nested registration, Progress, and Confluence remain future work."
  ],
  "noStagedFiles": true,
  "diffSummary": "Review-only: added review-cp2-round4.md; no Idris source, package, README, or NOTES files edited.",
  "reviewFindings": [
    "blocker: src/DGamma/Metatheory.idr:1154-1181,1260-1309,4041-4056 - encoded independence omits yielded inverses; reachable checked composite-accumulator countermodel falsifies Theorem 61, Corollary 62, and recovery-combined Theorem 64.",
    "major: README.md:108-112 and NOTES.md:379-452 - Def-60 correspondence/completed-bar narrative treats trace-specific forward/final-accumulator commutation as adequate despite the missing yielded-inverse condition and false recovery types.",
    "verified: src/DGamma/Metatheory.idr:779-814 - raw Preservation proof is genuine and does not use checked target admission.",
    "verified: src/DGamma/Metatheory.idr:3935-4037 - whole-prefix Reloading/first-exit structure proof is genuine and non-vacuous on an aligned installed trace."
  ],
  "manualNotes": "Final verdict: REJECT. Bar items (ii), (iii), and documented (iv) are met; bar item (i) fails under a new yielded-inverse countermodel."
}
```
