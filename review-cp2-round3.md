# Checkpoint 2 adversarial review — round 3

**Target:** `fd9677da3542a71a7b0d0fa2cf34839c8ca8d99a` (`repair CP2 recovery ordering and raise semantics`)  
**Scope:** paper Section 4 through Theorem 64; round-2 blocker remediation, all statement-only recovery/ordering/resolution types, claimed proof set, proof-bar tractability, executable checks, clean-archive build  
**Mode:** adversarial review only; no source edits and no commit

## Review status

Completed. This report was written incrementally so evidence survived interruption.

## Baseline

- Confirmed `HEAD` is exactly the requested commit `fd9677d`.
- Pre-review working tree contained only the pre-existing untracked `paper/` directory.
- Read `review-cp2-round1.md` and `review-cp2-round2.md` in full.
- Initial source scan located the admitted raw-preservation, recovery, global-ordering, global-structure, and combined-resolution TODO declarations in `src/DGamma/Metatheory.idr`.

## Validation performed (incremental)

- `idris2 --version`: **Idris 2 0.8.0**.
- Created fresh `git archive fd9677d` at `/tmp/dgamma-cp2-round3.yjvgyh`, ran `idris2 --clean dgamma.ipkg && idris2 --build dgamma.ipkg`: all eight package modules rebuilt and **passed**.
- Evaluated the submitted checks in that archive. Output was `[True, True, True, True, True, True, True, True, True]` for dynamic resolution, guarded lifecycle/removal, L-Raise identity, L-Raise lifecycle, stale-empty divert, aborting divert, landing divert, one-step proof trace, and the aggregate.

## Findings (incremental)

### BLOCKER — Pointwise table recovery is false because independence still projects every inverse to `world`

**Files:** `src/DGamma/Metatheory.idr:319-345,420-512,1272-1287`; `src/DGamma/Calculus.idr:26-67`; overclaims at `README.md:109-110` and `NOTES.md:332-353,379-383`

The round-2 repair added `SelectedTableRecovered` and `TerminalTableRecovery`, but neither independence premise constrains the **table component** of an accumulator off its original world. `TraceIndependent`, `PrefixRecoveryIndependent`, `partialWorldMap`, and `accumulatorWorldMap` all compare only `PartialMap world`. A `StepEffect` inverse is required to recover its exact application state, but may inspect a later `world` and return a different owned table there. Its world projection can still be identity and commute with every foreign map.

A review-only clean-archive executable constructs exactly that case:

1. selected fiber 0 installs `ServiceA=True` without changing `ToyRuntime`;
2. its witnessed inverse restores the opening empty table at the exact application world, but deliberately keeps `ServiceA=True` if the consumer bit has since changed;
3. independent foreign fiber 1 toggles that bit;
4. the actual accumulator extracted by `actualAccumulatorAt 0 current` is world-identity, commutes with the foreign map, and produces the correct ambient foreign replay;
5. applying it at the actual prefix/close endpoint nevertheless leaves `ServiceA=True`, while the episode-opening selected table has no `ServiceA` binding.

The prefix probe printed `[True, True, True, True, True, True]` for reachable checked prefix, actual handle found, accumulator world identity, prefix-map commutation over all four `ToyRuntime` values, ambient replay correctness, and **selected table recovery failure**. Extending the same run through checked O-Retire/L-Leave/L-Unload printed `[True, True, True, True, True]` for reachable close, all trace maps total, all pairwise commuting over the finite world, terminal ambient replay correctness, and **terminal selected-table recovery failure**.

This is not the rejected caller-chosen-handle attack: the probe extracts the exact endpoint handle. It shows that `recoveryExactnessTheorem`, `terminalRecoveryTheorem`, and the recovery-combined `resolutionCoherenceTheorem` are false as types. The repair must lift replay/commutation and definedness to the full effect state retained by paper `≈` (ambient world plus owned tables), or weaken/remove the table conclusions. Merely adding pointwise table fields to the conclusion cannot recover information discarded by the premises.

## Round-2 blocker re-attacks (incremental)

### Arbitrary/mismatched accumulator

**Old attack: fixed.** `recoveryExactnessTheorem` no longer lets the caller choose either an arbitrary partial map or an arbitrary restored endpoint. The equality `actualAccumulatorAt n current = Just handle` ties the existential package (current selected table plus stored lifecycle accumulator) to the exact indexed trace endpoint, and `runAccumulator handle` fixes both result projections. I found no way to satisfy that equality with an unrelated handle or a handle from another transition history.

**Deeper variant: theorem still false.** The BLOCKER above uses the actual extracted handle and attacks what its hypotheses observe, not its identity. The trace premises constrain `accumulatorWorldMap handle`; the new table conclusions constrain more state than that map carries.

### Post-L-Unload ordering endpoint

**Fixed, neither impossible nor vacuous.** Both `consumerResolution` and `providerValueStable` now range over `closedInside`, whose final state is the last installed state immediately before L-Unload. `ConsumerResolutionConstant` still checks both endpoints and every intermediate state; even `NoTransitions` requires `ResolutionConstantEnd`, so the range is not an empty proposition. This matches paper Theorem 63's inclusive installed interval `[b',u']`, not the post-close state `u'+1`.

A review-only checked run recorded all six states from the consumer's post-L-Begin opening through its pre-L-Unload Unloading endpoint. It printed `[True, True, True]`: the committed resolution stayed provider 0 throughout that entire `closedInside` range, provider 0's dynamic `ServiceA=True` value stayed constant throughout it, and the resolution became false immediately after consumer L-Unload. Thus the former generic `OrderingResult -> Void` attack is closed and the repaired range is inhabited in principle on a nontrivial episode.

### L-Raise replay map

**Fixed.** `partialWorldMapFor ... (LAdvance n) LRaiseTag` is total identity, matching Table 1, and the submitted `raiseMapIsIdentity` check passes. The identity map removes the round-2 replay impossibility and does not introduce a new failure in `ForeignReplay`, commutation, or definedness stability. The lower-level function is public and accepts an arbitrary action/tag pair, but theorem paths call it through an indexed `Transition`, whose checked evaluator equation prevents a mismatched tag; I found no statement-level exploit.

## Clean-archive and honesty validation

- Repeated from a second fresh archive, `/tmp/dgamma-cp2-round3-final.kW5Gas`: `idris2 --clean dgamma.ipkg && idris2 --build dgamma.ipkg` rebuilt all eight package modules successfully.
- Anchored scan found no `believe_me`, `assert_total`, postulate, unsafe primitive, `%default partial`, `%default covering`, `%unsafe`, or named Idris hole.
- All eight packaged modules contain `%default total`; the package lists exactly those eight modules.
- `TODO(proof)` inventory is explicit: three pre-existing Section-3 declarations in `Unified.idr`, plus raw Preservation, Theorem 61, Corollary 62, global Ordering, global ResolutionStructure, and recovery-combined Theorem 64 in `Metatheory.idr`.
- `git diff --check` passed. No staged files exist. Review work changed only this untracked report; the untracked `paper/` directory predated the review.

## Audit of the claimed proved set

### `beginSatisfactionTheorem` — valid, faithful, non-vacuous

**File:** `src/DGamma/Metatheory.idr:514-559`

The proof projects the checked L-Begin equation to the raw evaluator and eliminates every non-`Inactive Nothing`/non-target branch. Its conclusion, `isJust (targetAt n before) = True`, is the encoding's executable form of Equation 58: `targetFiber` is present only when every declared key resolves to an Active provider table. The dynamic-resolution scenario reaches this branch with a nonempty dependency list, so this is not an empty-dependency-only proof.

### unload guard and `reliedProviderCannotUnload` — valid local ordering facts

**File:** `src/DGamma/Metatheory.idr:847-887,990-1007`; evaluator guard at `src/DGamma/Calculus.idr:577-589`

`unloadGuardTheorem` projects the checked equation and exhausts `applyAction (LUnload n)`, leaving exactly `relied n = False`. `reliedProviderCannotUnload` then directly contradicts a supplied `relied = True` equation. This is a real exclusion: `guardedScenario` reaches a provider in Unloading, attempts L-Unload while its installed consumer commits to it, observes rejection, then succeeds only after the consumer closes.

It remains a local rule exclusion, not the missing induction that selects a provider episode and proves global containment.

### `AdvanceStructure` — valid endpoint-phase and Equation-59 classification

**File:** `src/DGamma/Metatheory.idr:561-783`

The raw `LAdvance` equation is exhaustively split by lifecycle, remaining program, capability resolution, step result, target equality, and remaining tail. The constructors now expose:

- L-Iter: target equality at the pre-state and Reloading at the endpoint;
- L-Finish, including `Reloading []`: target equality and Active at the endpoint;
- landing/empty-stale L-Divert: Unloading at the endpoint;
- L-Raise: Unloading at the endpoint.

The endpoint booleans are proved through a lookup-after-replacement lemma, rather than asserted from the tag. Submitted scenarios exercise every constructor class, including empty stale divert and L-Raise. The result records the exact phase, not every endpoint accumulator/table equation; those remain derivable from the retained raw evaluator equation, so the README's narrower “endpoint shapes” claim is accurate.

### `abortDivertStructureTheorem` — valid and non-vacuous

**File:** `src/DGamma/Metatheory.idr:785-845`

The proof exposes an actual pre-state fiber, Reloading lifecycle, target mismatch, and Unloading endpoint for the separate aborting `LDivert` action. The `abortDivertScenario` check reaches this rule. It covers the branch omitted by `advanceStructureTheorem` without conflating it with landing L-Divert.

### checked target monitor — valid and honestly scoped

**File:** `src/DGamma/Metatheory.idr:107-125,137-172`; `src/DGamma/Calculus.idr:669-691`

`checkedTransitionTargetValid` is exactly the postcondition tested by `checkedApplyAction`; it does not consume a source invariant and is therefore not Preservation. This commit correctly renamed it and separately states raw `preservationTheorem` with both source validity and a raw `applyAction` equation. The checked relation is operationally nonempty (all submitted checked traces pass), so the monitor fact is not logically empty, but it remains intentionally tautological as a safety gate.

### strengthened Definition 58 provider phase — coherent with reachable states

**File:** `src/DGamma/Calculus.idr:609-645`; `src/DGamma/Metatheory.idr:28-53`

Committed providers must now be Active or Unloading, never Reloading. This is stronger than paper Definition 58(4)'s bare “installed”, but agrees with reachable rule states: a consumer can commit only while the provider is Active, and the relied guard prevents that provider from reaching Inactive and then Reloading while the consumer remains installed. It also prevents an in-progress provider table mutation from invalidating an existing committed capability. The activation and guarded-withdrawal checks show both permitted phases are reachable.

## Statement-only countermodel hunt

| Declaration | Round-3 disposition |
|---|---|
| raw `preservationTheorem` | **Sound/non-vacuous, unproved.** I found no raw-rule countermodel to the strengthened Boolean invariant. The checked scenarios exercise all ten tags, but do not constitute the missing universal proof. |
| `recoveryExactnessTheorem` | **False.** Actual handle identity is fixed, but world-only independence cannot imply its new selected-table conclusion. |
| `terminalRecoveryTheorem` | **False.** The reachable closed variant has total pairwise-commuting world maps and correct ambient replay but a wrong selected table after L-Unload. |
| `orderingTheorem` | **Sound, restricted, unproved.** The post-unload impossibility is fixed; strict same-trace containment, distinct fibers, consumer resolution, and provider value constancy are all meaningful. It covers the documented finite case where the provider is no longer installed at the final state, rather than the paper's open-provider alternative. |
| `resolutionStructureTheorem` | **Sound/non-vacuous, unproved.** The anchored input blocks suffix attacks; `StillReloading` and `ExitedReloading` cover exactly the possible prefix shapes, including separate aborting divert, landing divert, raise, and finish. I found no structural countermodel. |
| `resolutionCoherenceTheorem` | **False through terminal table recovery.** Its structural component survives review, but the combined result embeds the false `TerminalTableRecovery` conclusion under the same world-only `TraceIndependent` premise. |

Even apart from the false selected-table field, the recovery types still do not state the full table half of paper `≈`: `ForeignReplay` composes only worlds, while `foreignTablesExact` says merely that the closing selected L-Unload leaves foreign tables equal to their last-installed values. It does not relate those tables to a full-state replay from the episode opening. A correct repair should replay a state projection containing ambient world and all owned tables, not append table equalities disconnected from the replay object.

## Proof-bar tractability judgment

These estimates assume one engineer already familiar with this encoding and exclude redesign needed to repair the newly false recovery statements.

| Admitted proof | Judgment | Focused estimate and required work |
|---|---|---|
| Raw Theorem 59 Preservation | **Tractable within the current encoding** | **3–6 engineering days.** The action space is finite and the strengthened invariant is favorable. Needed lemmas are mostly Boolean/list frame results for lookup/replace/insert/delete, parent-chain fuel under insertion/removal, pairwise provision preservation, committed-view stability, and the L-Unload guard. No semantic redesign appears necessary. |
| Global provider selection/ordering | **Tractable, but needs substantial reusable trace machinery** | **7–12 engineering days.** The current type appears true. The proof needs indexed trace splitting/search, matching L-Begin/L-Unload boundary extraction under name reuse, lifecycle/view frame lemmas (restricted Lemma 54), conversion from opening resolution to an earlier Active provider episode, and a forward guard argument through consumer close. This is new proof infrastructure, not a change to the runtime or theorem type. |
| Whole-episode exit location split | **Tractable within the current encoding** | **4–7 engineering days**, likely less after lifecycle frame lemmas exist. Induct over `insideInstalled`, preserve the opening committed provider list across foreign/ORetire steps, use `advanceStructureTheorem`/`abortDivertStructureTheorem` at selected exits, and carry an already-found exit through the remaining installed suffix. No redesign is indicated. |

The three admitted gaps are therefore proof debt rather than evidence that the trace encoding must be replaced. The recovery layer is different: before Theorem 61/Corollary 62/Theorem 64 recovery can be proved, their maps and independence premises need redesign to retain the table state their conclusions now mention. A focused repair is plausible, but it is not “just finish the induction.”

## Per-round-2 finding disposition

| Round-2 finding | Round-3 disposition | Evidence |
|---|---|---|
| **BLOCKER:** caller-chosen Theorem-61 accumulator | **FIXED for that attack; replacement theorem still false** | `actualAccumulatorAt` and its equality select the exact endpoint handle. The new executable attack uses that actual handle and exploits missing table-level independence instead. |
| **BLOCKER:** `OrderingResult` includes post-L-Unload endpoint | **FIXED** | Both constancy predicates use `closedInside`. The checked range probe reports resolution/value constancy at every installed state and loss only after L-Unload. |
| **BLOCKER:** L-Raise classified as undefined replay map | **FIXED** | The tag-specific branch is identity and `raiseMapIsIdentity=True`; no replay/definedness regression found. |
| **MAJOR:** Preservation was a target monitor | **FIXED as an honesty/naming issue; proof still missing** | Monitor is now `checkedTransitionTargetValid`; raw Theorem 59 is a precise unproved type with source invariant and raw equation. |
| **MAJOR:** local classification did not meet whole-exit proof bar | **PARTIALLY FIXED** | Endpoint phases for all LAdvance exits and the separate aborting divert shape are proved. Global first-exit location remains explicitly statement-only. |
| **MAJOR:** temporal statements projected away dynamic tables | **NOT FIXED; escalated to BLOCKER** | Pointwise table conclusions were added, but premises/replay still project to `world`. The executable off-origin inverse countermodel falsifies Theorem 61, Corollary 62, and combined Theorem 64. |

## Positive results

- The exact three round-2 blocker mechanisms were directly addressed: no arbitrary handle, no post-close constancy endpoint, and correct L-Raise identity.
- The ordering statement is now both satisfiable in principle and faithful over its documented closed finite case.
- The local proved structural set is genuine and non-vacuous; all ten tags and both divert alternatives execute successfully.
- Raw Preservation is no longer overclaimed, and no hidden proof escape hatch replaces it.
- Two independent clean archives build under Idris 2 0.8.0 with total defaults and no escape hatches.

## Residual risks

- Recovery independence/replay observes only ambient `world`, so table-sensitive off-origin inverses invalidate every theorem that now promises selected-table recovery.
- Full foreign-table replay remains unstated even if the selected-table countermodel is repaired.
- `TraceIndependent` is trace-specific and weaker than paper Definition 60's component-level generated monoids and yield/continuation stability.
- Nested registration, Lemmas 54–57, observational transport/equivariance, Progress, and Confluence remain outside this checkpoint.
- The checked proof LTS can reject a raw endpoint; raw Preservation/completeness remains required before the monitor certifies the rules rather than merely filters them.
- Finite lists and exact ambient equality remain documented restrictions.

## Final verdict

The executable calculus and the local proof set are materially improved, and two of the three round-2 theorem blockers are genuinely closed. Acceptance is nevertheless impossible: the table-recovery repair asserts information that all recovery premises still erase, and a reachable actual-handle countermodel falsifies Theorem 61, Corollary 62, and recovery-combined Theorem 64.

# REJECT

```acceptance-report
{
  "criteriaSatisfied": [
    {
      "id": "criterion-1",
      "status": "satisfied",
      "evidence": "Concrete BLOCKER and statement dispositions cite DGamma.Metatheory, DGamma.Calculus, README, and NOTES; two clean-archive probes execute the actual-handle table countermodel and repaired ordering range, with residual risks and proof-bar estimates documented."
    }
  ],
  "changedFiles": [
    "review-cp2-round3.md"
  ],
  "testsAddedOrUpdated": [],
  "commandsRun": [
    {
      "command": "git archive fd9677d | tar -x ... && idris2 --clean dgamma.ipkg && idris2 --build dgamma.ipkg",
      "result": "passed",
      "summary": "Two independent fresh archives rebuilt all eight package modules under Idris 2 0.8.0."
    },
    {
      "command": "idris2 --source-dir src -o checkcp2r3 src/EvalChecksR3.idr && ./build/exec/checkcp2r3",
      "result": "passed",
      "summary": "All nine submitted scenario/aggregate booleans printed True."
    },
    {
      "command": "idris2 --source-dir src -o table-recovery-probe src/TableRecoveryProbe.idr && ./build/exec/table-recovery-probe",
      "result": "passed",
      "summary": "Reachable actual-handle prefix printed six True flags; closed trace printed five True flags, including world identity/commutation, correct ambient replay, and selected-table recovery failure."
    },
    {
      "command": "idris2 --source-dir src -o ordering-range-probe src/OrderingRangeProbe.idr && ./build/exec/ordering-range-probe",
      "result": "passed",
      "summary": "Printed [True, True, True]: resolution and provider value are constant through closedInside, then resolution disappears post-LUnload."
    },
    {
      "command": "anchored escape-hatch, named-hole, total-default, TODO(proof), and package-module scans over clean archive",
      "result": "passed",
      "summary": "No escape hatches or named holes; all eight packaged modules use %default total; all proof TODOs are explicit."
    }
  ],
  "validationOutput": [
    "Idris 2 version 0.8.0",
    "Clean archive build: passed, 8/8 modules (repeated twice)",
    "Submitted checks: [True, True, True, True, True, True, True, True, True]",
    "Actual-handle prefix countermodel: [True, True, True, True, True, True]",
    "Closed terminal countermodel: [True, True, True, True, True]",
    "Ordering closedInside probe: [True, True, True]",
    "No staged files; only report and pre-existing paper directory are untracked"
  ],
  "residualRisks": [
    "World-only recovery maps cannot justify the selected-table conclusions; Theorem 61, Corollary 62, and combined Theorem 64 are false.",
    "Foreign tables are not part of ForeignReplay, so the full paper control-forgetting equation remains unstated.",
    "Raw Preservation, global provider selection, and whole-episode exit location remain explicit proof debt.",
    "Nested registration, generated-monoid independence, Lemmas 54-57, Progress, and Confluence remain absent."
  ],
  "noStagedFiles": true,
  "diffSummary": "Review-only: added review-cp2-round3.md; no Idris source, package, README, or NOTES files edited.",
  "reviewFindings": [
    "blocker: src/DGamma/Metatheory.idr:319-345,420-512,1272-1287 - recovery premises commute/replay only world projections, but conclusions assert owned-table recovery; reachable actual-handle countermodel falsifies Theorem 61, Corollary 62, and combined Theorem 64.",
    "no additional false raw-Preservation, ordering, or structural-resolution type found; ordering endpoint and LRaise fixes withstand re-attack.",
    "verified: src/DGamma/Metatheory.idr:514-1007 - Equation 58, endpoint-phase classification, abort divert, unload guard, and relied-provider exclusion are genuine and non-vacuous.",
    "verified: src/DGamma/Metatheory.idr:149-172 - checked target admission is correctly scoped and raw Preservation is honestly statement-only."
  ],
  "manualNotes": "Final verdict: REJECT. The three admitted proof-bar gaps look tractable within the current trace encoding, but the recovery statements require a full-effect-state independence/replay redesign before proof."
}
```
