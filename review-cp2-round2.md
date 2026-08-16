# Checkpoint 2 adversarial review — round 2

**Target:** `29840c908a53b773c00ff5ca3143acc9b2acc6fb` (`redesign CP2 traces capabilities and rule checks`)  
**Scope:** paper Section 4 through Theorem 64; round-1 countermodel remediation, checked-LTS non-vacuity, proof bar, executable checks, clean-archive build  
**Mode:** adversarial review only; no source edits and no commit

## Review status

Completed. This file was written incrementally so evidence survived interruption.

## Baseline

- Confirmed `HEAD` is the requested commit `29840c9`.
- Pre-review working tree contained only the pre-existing untracked `paper/` directory.
- Read `review-cp2-round1.md` in full and skimmed `review-cp1-round3.md` for the acceptance standard.

## Validation performed (incremental)

- `idris2 --version`: **Idris 2 0.8.0**.
- Created fresh `git archive 29840c9` at `/tmp/dgamma-cp2-round2.Nume1J` and rebuilt all eight package modules: **passed**.
- Evaluated the eight submitted scenario booleans in the clean archive. Output was `[True, True, True, True, True, True, True, True]` for dynamic resolution, guarded lifecycle/removal, raise, stale-empty divert, aborting divert, landing divert, one-step proof trace, and aggregate coverage.
- Added a review-only module in the clean archive that chains `fire` seven times (provider/consumer O-Insert, provider L-Begin/L-Iter/L-Finish, consumer L-Begin/L-Finish) and packages the exact endpoints into one indexed `Transitions initialSystem final`. It compiled and printed `True`. The checked LTS is therefore operationally nonempty beyond its one-step submitted smoke check.

## Findings (incremental)

### BLOCKER — `recoveryExactnessTheorem` is false because its accumulator is arbitrary

**File:** `src/DGamma/Metatheory.idr:356-389`

The L-Begin anchoring fixes the round-1 suffix attack, but the new theorem does not connect its `accumulator : PartialMap world` to the selected fiber's actual lifecycle accumulator. The only endpoint premise is the tautological equation the caller may arrange for that arbitrary map.

At the zero-transition prefix immediately after L-Begin, choose `accumulator = const (Just bad)` for any `bad` distinct from the episode-start world. `PrefixRecoveryIndependent` is vacuously inhabited because the trace is `NoTransitions`, and the endpoint equation is `Refl`. The conclusion is `ForeignReplay ... NoTransitions start bad`, whose only constructor `ReplayDone` requires `start = bad`, contradiction.

A review-only clean-archive module typechecked the generic refutation `immediatePrefixAttack`: from any checked L-Begin endpoint with two distinct world values it maps an assumed inhabitant of `recoveryExactnessTheorem` to `Void`. The seven-step checked ToyRuntime trace above supplies such a reachable L-Begin on a non-subsingleton world. This is a false statement-only theorem, not merely an omitted proof.

### BLOCKER — `orderingTheorem` has an impossible conclusion at every closed consumer episode

**File:** `src/DGamma/Metatheory.idr:713-794`

`OrderingResult.consumerResolution` asks for `ConsumerResolutionConstant` over `closedTransitions (locatedEpisode consumerEpisode)`. `closedTransitions` includes the closing L-Unload and its endpoint. At that endpoint the consumer is `Inactive`, `committed` is `Nothing`, and therefore `resolvedProviderAt consumer k provider` is `False`. But `ConsumerResolutionConstant` checks both endpoints and eventually requires `ResolutionConstantEnd ... = True` at exactly that post-unload state.

Paper Theorem 63(1) ranges through the last installed state `u'`, not `u'+1`. This field must range over `closedInside`, or otherwise exclude the L-Unload endpoint.

A review-only module typechecked `orderingResultImpossible`, a generic erased proof that **every** `OrderingResult` entails `Void`: it proves resolution is false after the exact checked L-Unload equation, recursively extracts the final `ResolutionConstantEnd`, and contradicts its `True` equation. The submitted guarded provider/consumer scenario shows the theorem premises are reachable, so this is not benign vacuity.

### BLOCKER — L-Raise is misclassified as a failing replay map, making terminal recovery/Theorem 64 false

**File:** `src/DGamma/Metatheory.idr:246-280,337-354,394-402,975-990`

`partialWorldMapFor` ignores its `tag`. For every nonempty `LAdvance` it reruns the iterator; if that rerun raises, it returns `Nothing`. On an actual `LRaiseTag`, however, paper Table 1 defines `Psi_t = id`, because the failed iteration installs no state effect. A review-only executable probe built the checked `raiseRun` prefix, selected its `LRaiseTag` transition, and confirmed `partialWorldMap transition (MkToyRuntime False False) = Nothing` (printed `True`).

Consequently a foreign L-Raise inside another fiber's closed episode makes `ForeignReplay` impossible: `ReplayForeign` demands `partialWorldMap transition input = Just next`. Yet `TraceIndependent` does not exclude this case. A nowhere-defined map commutes partially with every total map (both compositions are `Nothing`), and every `definednessStable` obligation mentioning it has an impossible `Just` premise. Thus a trace with an otherwise independent selected fiber and an interleaved failing foreign fiber satisfies the stated independence premise but cannot satisfy `terminalRecoveryTheorem`; the same impossible replay is embedded in `resolutionCoherenceTheorem`.

The honest off-origin-failure repair must dispatch on the actual rule tag: L-Raise is identity; only actual L-Iter/L-Finish/landing-L-Divert rerun a successful moved iterator and may become `Nothing` off-origin.

### MAJOR — The claimed Preservation proof is a postcondition monitor, not paper Theorem 59

**Files:** `src/DGamma/Calculus.idr:646-681`; `src/DGamma/Metatheory.idr:107-155`; `README.md:107`; `NOTES.md:264-270,325-335`

`checkedApplyAction` first runs the raw evaluator and then admits the endpoint **iff `registryWellFormed afterState` is already true**. `Transition` stores that checked equation. `checkedActionTargetValid` merely eliminates the `if`; `preservationTheorem` ignores its `TransitionSourceValid` argument completely and returns the postcondition embedded in transition admission.

The clean-archive seven-step proof trace establishes that this checked relation is operationally nontrivial, and NOTES honestly says raw-rule completeness is unproved. Neither fact turns this into the preservation induction of paper Theorem 59. The missing theorem is the substantive direction

```text
wellFormed before -> applyAction action before = Just (tag, after) -> wellFormed after
```

(or equivalently that a raw rule from a valid source is never rejected by the monitor). As submitted, malformed raw rule endpoints can be hidden by making them non-transitions, and the source hypothesis's erasure from the proof is decisive evidence that no preservation property of the rules was proved. This fails the supervisor's explicit “Thm 59 proved” bar despite honest disclosure.

### MAJOR — The proved local classification does not meet the structural Equation-59/exit proof bar

**Files:** `src/DGamma/Metatheory.idr:451-568,796-832,905-970`; `README.md:112`; `NOTES.md:290-309,325-339`

`advanceStructureTheorem` proves target equality for L-Iter/L-Finish pre-states and that an `LAdvance` result tag is one of Iter/Finish/Divert/Raise. Its `DivertAdvance` and `RaiseAdvance` constructors contain no pre/post-state facts, and even `FinishAdvance` does not state the required `Active(_, omega)` endpoint. It does not cover the separate aborting `LDivert` action. The data type that does expose Active/Unloading exit states is `StructuralExit`, but the theorem that locates such an exit after the maximal initial Reloading interval is `resolutionStructureTheorem`, explicitly `TODO(proof)`.

Accordingly Equation 59 has a useful one-step proof, but the paper's structural exit lemma/dichotomy remains statement-only. Together with the statement-only (and currently false) global `orderingTheorem`, the requested proof bar “Thm 59 + Equation-58/provider ordering + structural Equation-59/exit lemma proved” is not met.

### MAJOR — Temporal statements project away the dynamic tables that paper `approximately equal` keeps

**Files:** `src/DGamma/Calculus.idr:12-67`; `src/DGamma/Metatheory.idr:246-280,337-402`; `NOTES.md:240-252,276-288`

The redesign correctly makes each fiber table mutable runtime state and witnesses undo over the full `LocalState` (ambient world plus owned table). But `partialWorldMap`, `ForeignReplay`, `recoveryExactnessTheorem`, and `terminalRecoveryTheorem` quantify only `world`. They do not state recovery of the selected fiber's owned table or preservation of foreign fibers' tables.

Paper Equations 56–57 use `approximately equal`, which forgets control fields but compares the coeffect tables and ambient state exactly (paper Definition 53 discussion). Once tables became dynamic rather than immutable component projections, a world-only theorem ceased to represent that relation. The full-state witness exists at `StepEffect`, but the global theorem types discard half of it. NOTES discloses exact equality and the checked-LTS restriction, not this dynamic-table recovery weakening.

## Additional validation

- Typechecked and executed three review-only adversarial modules in the clean archive: the generic immediate-prefix refutation of Theorem 61, the generic proof that every `OrderingResult` is impossible, and the executable L-Raise map probe. All compiled; each executable printed `True`.
- Re-ran `idris2 --clean dgamma.ipkg && idris2 --build dgamma.ipkg` in the clean archive after the probes: **passed**.
- Anchored escape-hatch scan found no `believe_me`, `assert_total`, postulate, unsafe primitive, `%default partial`, `%default covering`, or named hole. Every one of the eight package modules contains `%default total` and all eight are listed in `dgamma.ipkg`.
- No staged files were created. The repository changes made by this review consist only of this untracked report; the pre-existing untracked `paper/` remains.

## Round-1 finding disposition

| Round-1 finding | Round-2 disposition | Evidence |
|---|---|---|
| **BLOCKER:** universal `AllComponentsIndependent` forces a subsingleton world | **FIXED for that countermodel** | The type is deleted. `TraceIndependent` ranges over actual distinct-actor transition occurrences, and `emptyTraceIndependent` inhabits it for every world. Theorem 61 nevertheless has a new arbitrary-accumulator countermodel. |
| **BLOCKER:** arbitrary episode suffixes accepted | **FIXED** | `EpisodePrefix` requires the exact checked L-Begin immediately before its installed segment; `ClosedEpisode` additionally requires the exact checked L-Unload. Active/Unloading suffixes alone cannot inhabit them. |
| **BLOCKER:** pointwise provider visibility false from weak well-formedness | **FIXED** | The false helper was removed. `viewBindingsInvariant` now checks `resolveCommittedValues`, tying each committed key/provider to an installed table containing the key. |
| **BLOCKER:** unrelated provider episode accepted by `orderingTheorem` | **FIXED for that attack; theorem still false** | `LocatedClosedEpisode` has exact global decomposition and `ProviderContainsConsumer` has strict same-trace prefix equations. But `OrderingResult.consumerResolution` wrongly includes the post-L-Unload endpoint and is impossible. |
| **BLOCKER:** Theorem 64 accepted an Unloading suffix and omitted open-final structure | **FIXED for that attack; full theorem still false** | The structural input is L-Begin-anchored and `StillReloading` represents open-final prefixes. The full theorem inherits the L-Raise/ForeignReplay countermodel and still projects away tables. |
| **MAJOR:** stale `Reloading []` illegally L-Finished | **FIXED** | The raw branch checks target equality and otherwise emits L-Divert; `emptyStaleDiverts=True`. |
| **MAJOR:** immutable tables and no dependency capability hollowed out coeffects | **FIXED substantially** | Dynamic `OwnedTable`, `DepValues`, and `LocalState` are operational. `activationUsesResolution=True` confirms a consumer reads ServiceA and computes both ambient state and its own ServiceB. Nested registration remains an explicit restriction. |
| **MAJOR:** foreign replay totalized off-origin failure to identity | **PARTIALLY FIXED** | Successful moved iterators now propagate `Nothing`, but `partialWorldMapFor` ignores `LRaiseTag` and treats the paper-identity raise as a failed map, falsifying replay statements. |
| **MAJOR:** checks missed rule tags/guards | **FIXED** | Submitted scenarios hit all ten tags, both divert alternatives, stale empty, failed iteration, relied unload rejection, and removal; aggregate output is all `True`. |
| **MINOR:** same-action determinism is weak | **UNCHANGED / accurately limited** | The theorem remains pure-function same-action determinism. It is valid but not substantive confluence or rule-exclusivity evidence. |

## Countermodel-priority conclusions

1. **Episode-suffix attack:** blocked by the new L-Begin/L-Unload equations.
2. **Subsingleton-world attack:** blocked by deleting the open universal component quantifier. The empty witness is logically vacuous over occurrences, but it is sufficient to refute the old implication that independence collapses every world.
3. **Unrelated-provider-episode attack:** blocked by strict prefix equations in one supplied global trace.
4. **Unloading-suffix attack:** blocked for `resolutionStructureTheorem` by `EpisodePrefix`.
5. **New deeper failures:** immediate-prefix arbitrary accumulator, post-close consumer resolution, and L-Raise replay classification each make an advertised statement-only theorem false.

## Proof-bar judgment

The supervisor's bar was: **“Thm 59 + Equation-58/provider ordering + structural Equation-59/exit lemma proved.”**

| Required item | Judgment |
|---|---|
| Theorem 59 Preservation | **NOT MET.** The checked relation tests the target invariant as an admission condition; the source invariant is unused. Raw-rule preservation/completeness is unproved. |
| Equation 58 | **MET.** `beginSatisfactionTheorem` genuinely derives target existence from the L-Begin evaluator equation. |
| Provider ordering | **NOT MET.** Only the local unload guard and projection from an already supplied containment witness are proved. The global theorem is statement-only and its current result is impossible. |
| Structural Equation 59 | **PARTIALLY MET.** One-step target equality for L-Iter/L-Finish is proved. |
| Structural exit lemma | **NOT MET.** `advanceStructureTheorem` does not expose Divert/Raise endpoints or aborting L-Divert; the global `resolutionStructureTheorem` that does is statement-only. |

**Overall proof bar: NOT MET.**

## Statement-type disposition

| Result | Disposition |
|---|---|
| Theorem 59 | Checked safety-monitor tautology, not preservation of the raw ten-rule evaluator. Nontrivial checked traces exist, and the limitation is honestly disclosed. |
| Theorem 61 | **False:** arbitrary accumulator at the empty L-Begin-anchored prefix. Generic refutation typechecked. |
| Corollary 62 | **False:** a foreign always-raising step has paper map identity but encoded map `Nothing`; stated independence permits it, while replay cannot cross it. Also weaker than the paper because owned tables are omitted. |
| Theorem 63 | Equation 58 and local unload guard are valid/proved; the global statement is **false** because resolution constancy includes the post-unload endpoint. |
| Theorem 64 | Per-LAdvance Equation-59 fact is valid/proved; global structural split is unproved; recovery-combined statement is **false** through the same foreign L-Raise replay countermodel and omits table recovery. |

## Positive results

- The four named round-1 type attacks themselves were addressed rather than hidden.
- The raw stale-empty rule regression is fixed.
- Dynamic provider tables, declared dependency capabilities, and own-table confinement are meaningful executable improvements.
- All ten rule tags and the relied guard are exercised successfully.
- A seven-transition indexed checked trace was constructed, so the checked LTS is not empty or limited to a singleton transition.
- The clean archive builds under Idris 2 0.8.0 with total defaults and no escape hatches.
- NOTES is honest that raw-rule completeness and the global ordering/structure/recovery proofs are missing. Honest disclosure does not satisfy the proof bar or make false theorem types acceptable.

## Residual risks

- `TraceIndependent` is a trace-specific actual-map condition, not paper Definition 60's generated monoids over every reachable continuation and yielded inverse. Even after the concrete false statements are repaired, downstream Progress/Confluence will need a stronger reusable component-level account.
- Nested registration inside `StepEffect` is absent, so later registration cascades in Progress and Confluence remain outside the calculus.
- Lemmas 54–57, observational `approximately equal` transport, equivariance, and vestigial-entry reasoning remain unmechanized.
- Finite list iterators and exact ambient equality are disclosed restrictions.
- Boolean scenario coverage cannot substitute for raw preservation, provider-order induction, or the global resolution split.

## Final verdict

The executable redesign is materially better and most round-1 local countermodels are closed. Acceptance is still impossible: three current statement-only theorem types have direct countermodels, Theorem 59 is only enforced by a target monitor, and the required provider-order/exit proofs are absent.

# REJECT

```acceptance-report
{
  "criteriaSatisfied": [
    {
      "id": "criterion-1",
      "status": "satisfied",
      "evidence": "Concrete BLOCKER/MAJOR findings cite DGamma.Metatheory, DGamma.Calculus, README, and NOTES; two generic Idris refutations and an executable L-Raise map counterexample were checked in a clean archive, with residual risks listed."
    }
  ],
  "changedFiles": [
    "review-cp2-round2.md"
  ],
  "testsAddedOrUpdated": [],
  "commandsRun": [
    {
      "command": "git archive 29840c9 | tar -x ... && idris2 --clean dgamma.ipkg && idris2 --build dgamma.ipkg",
      "result": "passed",
      "summary": "Fresh archive rebuilt all eight package modules under Idris 2 0.8.0."
    },
    {
      "command": "idris2 --source-dir src -o eval-checks src/EvalChecks.idr && ./build/exec/eval-checks",
      "result": "passed",
      "summary": "Eight submitted scenario/aggregate checks printed [True, True, True, True, True, True, True, True]."
    },
    {
      "command": "idris2 --source-dir src -o checked-trace-probe src/CheckedTraceProbe.idr && ./build/exec/checked-trace-probe",
      "result": "passed",
      "summary": "Review-only seven-step indexed checked trace compiled and printed True."
    },
    {
      "command": "idris2 --source-dir src -o recovery-type-attack src/RecoveryTypeAttack.idr && ./build/exec/recovery-type-attack",
      "result": "passed",
      "summary": "Generic immediate-prefix refutation of recoveryExactnessTheorem typechecked and printed True."
    },
    {
      "command": "idris2 --source-dir src -o ordering-type-attack src/OrderingTypeAttack.idr && ./build/exec/ordering-type-attack",
      "result": "passed",
      "summary": "Generic proof that every OrderingResult entails Void typechecked and printed True."
    },
    {
      "command": "idris2 --source-dir src -o raise-map-probe src/RaiseMapProbe.idr && ./build/exec/raise-map-probe",
      "result": "passed",
      "summary": "Checked LRaise transition's partialWorldMap evaluated to Nothing; probe printed True."
    },
    {
      "command": "anchored escape-hatch/default-total/package-module scan over clean archive",
      "result": "passed",
      "summary": "No escape hatches or named holes; all eight modules use %default total and are packaged."
    }
  ],
  "validationOutput": [
    "Idris 2 version 0.8.0",
    "Clean archive build: passed (8 package modules)",
    "Submitted checks: all eight booleans True",
    "Checked proof-LTS: seven-step indexed trace exists",
    "Theorem 61 generic immediate-prefix refutation: typechecked",
    "OrderingResult generic impossibility proof: typechecked",
    "LRaise replay map probe: Nothing"
  ],
  "residualRisks": [
    "TraceIndependent is weaker and more trace-specific than paper Definition 60's generated iterator monoids.",
    "Nested registration, Lemmas 54-57, observational transport/equivariance, Progress, and Confluence remain absent.",
    "Temporal theorem statements project away dynamic owned tables even though paper recovery equivalence retains them.",
    "The checked monitor can reject raw endpoints; completeness/preservation of applyAction from valid sources is unproved."
  ],
  "noStagedFiles": true,
  "diffSummary": "Review-only: added review-cp2-round2.md; no Idris source, package, README, or NOTES files were edited.",
  "reviewFindings": [
    "blocker: src/DGamma/Metatheory.idr:356-389 - recoveryExactnessTheorem accepts an arbitrary accumulator and is false at the zero-transition prefix immediately after L-Begin.",
    "blocker: src/DGamma/Metatheory.idr:713-794 - OrderingResult requires consumer resolution at the post-L-Unload endpoint, making every result impossible and orderingTheorem false.",
    "blocker: src/DGamma/Metatheory.idr:246-280,394-402,975-990 - partialWorldMap misclassifies LRaise as a failed map rather than identity, falsifying terminal recovery and recovery-combined Theorem 64.",
    "major: src/DGamma/Calculus.idr:646-681 and src/DGamma/Metatheory.idr:107-155 - checked Preservation simply projects the target invariant used to admit Transition; the source invariant is unused and raw Theorem 59 remains unproved.",
    "major: src/DGamma/Metatheory.idr:451-568,905-970 - advanceStructureTheorem proves one-step tag/target facts but not the structural exit dichotomy required by the proof bar.",
    "major: src/DGamma/Metatheory.idr:246-402 - recovery statements retain only ambient world and omit dynamic owned-table recovery required by the paper's control-forgetting equivalence."
  ],
  "manualNotes": "Final verdict: REJECT. The specific round-1 suffix/subsingleton/unrelated-episode/stale-empty attacks were mostly repaired, but new typechecked countermodels and the unmet proof bar prevent acceptance."
}
```
