# Checkpoint 2 adversarial review — round 1

**Target:** `6e4fc6de4972500e8f8f07643d51e47a05bfab44` (`add Section 4 calculus and checkpoint 2 statements`)  
**Scope:** paper Section 4 through Theorem 64; executable calculus, statement types, restrictions, checks, and clean-archive build  
**Mode:** adversarial review only; no source edits and no commit

## Final verdict

# REJECT

The package builds cleanly, most non-empty-program rule branches match the paper, and the restrictions are disclosed honestly. That is not enough for CP2 acceptance. One executable LTS branch violates the L-Finish side condition, and multiple statement-only metatheorem types are false, vacuous, incomplete, or not the paper's statements. In particular, the submitted Definition-60 hypothesis quantifies over **every constructible component**, which collapses the ambient world to a subsingleton and hollows out temporal recovery; the episode predicates do not identify episode openings; the pointwise provider theorem has a direct countermodel; Theorem 63 does not relate the selected provider episode to the consumer episode it contains; and Theorem 64 requires a Reloading exit even when its input is merely an Unloading suffix.

`ACCEPT` is therefore not available under the requested standard (“statements faithful + calculus sound + restrictions acceptable”), independently of whether CP2 is allowed to leave sound statements unproved.

## Validation performed

- Read paper Section 4 in full (`paper/cordis-paper.txt:1132-2374`), including all ten rules, Definitions 43–69, Theorems 59/61/63/64, Corollary 62, and the surrounding metatheory through Theorem 73.
- Read all three new modules, `README.md`, `NOTES.md`, `dgamma.ipkg`, and all three CP1 review reports.
- Confirmed `HEAD` is exactly `6e4fc6d`; the pre-review working tree contained only the pre-existing untracked `paper/` directory.
- `idris2 --version`: **Idris 2 0.8.0**.
- Created a fresh `git archive 6e4fc6d` at `/tmp/dgamma-cp2-review.NQgqch` and ran `idris2 --build dgamma.ipkg`: all eight modules rebuilt and **passed**.
- In that clean archive, evaluated the three submitted checks: `(calculusScenarioRecovered, calculusScenarioNoActiveCoeffects, calculusScenarioWellFormed)` printed `(True, (True, True))`.
- Added a review-only probe in the temporary archive, not the repository. It constructs an empty-program consumer, begins it against an active provider, makes the provider leave, then evaluates `LAdvance` on the stale consumer. It printed `True`, confirming that the evaluator emits `LFinishTag` and makes the consumer `Active` while `targetFiber` is `Nothing`.
- An anchored source scan found no code-level `believe_me`, `assert_total`, postulate, unsafe primitive, `%default partial`, or `%default covering`. All eight package modules use `%default total` and are listed in `dgamma.ipkg`.
- No staged files were created.

## Rule-by-rule LTS audit

| Paper rule | Encoding | Assessment |
|---|---|---|
| O-Insert | `Calculus.idr:390-398` | The freshness, parent-presence, and provision-disjointness checks are present. Faithful for the registry-separated fragment. It cannot be invoked from a `StepEffect`, so it does not implement the paper's nested-registration iteration case. |
| O-Retire | `Calculus.idr:399-402` | Faithful: presence is the only precondition and repeated retirement remains an allowed no-op transition, as in the paper relation. |
| O-Remove | `Calculus.idr:403-410` | Faithful: retired, any `Inactive` outcome, and no child. |
| L-Begin | `Calculus.idr:411-422` | Faithful for the list representation: only `Inactive Nothing`, a non-bottom target, committed view captured, identity accumulator. |
| L-Iter | `Calculus.idr:430-451` via `LAdvance` | For a non-final successful list element, the target-equality test, forward world update, and `accumulator . undo` LIFO order are correct. |
| L-Finish | `Calculus.idr:426-429,430-445` via `LAdvance` | The non-empty final-element branch is correct. The `Reloading []` branch omits `target = committed` and is a real rule bug; see MAJOR finding below. |
| L-Divert | `Calculus.idr:452-469` | Both paper alternatives are represented: `LAdvance` lands a successful in-flight iteration, while `LDivert` aborts before it. Their target-inequality conditions are correct for non-empty iteration states. The empty-list L-Finish bug allows a third, illegal response to the same stale target. |
| L-Raise | `Calculus.idr:431-436` | Faithful: a raise exits Reloading regardless of the current target and preserves the accumulated inverse. |
| L-Leave | `Calculus.idr:471-482` | Faithful: target mismatch only; the committed view and accumulator are retained while active provisions disappear. |
| L-Unload | `Calculus.idr:483-493` | Faithful for the separated world: only Unloading, guarded by `not relied`, and the only evaluator branch applying the stored accumulator. |

Lifecycle-state classification, active-only provider resolution, and `relied` using every other installed committed view are otherwise aligned with Definitions 45, 49, and 50. The accumulator composition order is LIFO, not reversed.

## Findings

### BLOCKER — `AllComponentsIndependent` collapses the ambient world and makes Theorems 61/62 vacuous

**Files:** `src/DGamma/Metatheory.idr:109-145,239-247,277-304`; `README.md` Def 60 / Thm 61 / Cor 62 rows; `NOTES.md` “Metatheorem statement quality”

The comments say the hypothesis ranges over “every pair of component programs that can participate in the run.” Its actual type is:

```idris
(left, right : Component key value world error) ->
ComponentsIndependent left right
```

This ranges over **every value constructible at the open `Component` type**, not the components occurring in the trace or a supplied closed component universe. It includes components manufactured solely to probe the hypothesis.

For arbitrary `x, y : world`, construct two empty-interface, single-step components. The first step maps every origin to `x` and returns `const origin` as its witnessed undo; the second does the same with `y`. These are valid `StepEffect`s because each yielded inverse recovers its own application state. Applying `partialEffectsCommute` to the two forward generators says `const x . const y` and `const y . const x` are exactly equivalent, hence `x = y`. Therefore:

```text
AllComponentsIndependent key world error value
  implies (x, y : world) -> x = y.
```

The main temporal hypothesis admits only an observationally trivial/subsingleton exact-equality world. Corollary 62 can then hold without expressing recovery at all. This is not a harmless strengthening of paper Definition 60; it destroys the class of nontrivial worlds the theorem is intended to cover.

`RegistryProgramsIndependent` is much closer to the needed quantification, but it is unused and a single snapshot is insufficient for later insertion. The repair needs a trace-indexed/closed-universe family of the component instances that actually occur, quantified at distinct names, plus the paper's reachable-continuation and yielded-inverse stability.

### BLOCKER — `OpenEpisodeTrace` and `EpisodeTrace` do not identify episode openings, invalidating Theorems 61/62 and Theorem 64

**Files:** `src/DGamma/Metatheory.idr:213-229,260-304,562-575`

Paper Definition 53 starts an episode at the state **immediately after its L-Begin**, where the accumulator is identity, and makes the installed interval maximal. The submitted predicates only say that the selected fiber is installed throughout an arbitrary segment and, for `EpisodeTrace`, that the last transition is L-Unload. They do not require:

- a preceding state in which the fiber was not installed;
- the opening transition to be L-Begin;
- identity accumulator at the segment start; or
- the segment to start at the maximal installed interval's left boundary.

Consequences:

1. `OpenEpisodeTrace` admits `NoTransitions` at any `Active` or `Unloading` state. Theorem 61 then compares the stored accumulator against replay from that mid-episode world. For a nontrivial active effect, replay of the empty foreign trace leaves the active world unchanged while the accumulator removes the effect. This is not Equation 56.
2. `EpisodeTrace` admits the one-transition suffix consisting only of L-Unload. Corollary 62 then omits the selected transition from `ForeignReplay` and compares the pre-unload world directly with the recovered post-unload world. This is not Equation 57; the paper starts at L-Begin, not at L-Unload.
3. The same one-transition Unloading suffix is accepted by `resolutionCoherenceTheorem`, but `ResolutionOutcome` requires the trace to contain an exit from Reloading tagged L-Finish, L-Divert, or L-Raise. Its only transition is L-Unload. On a singleton `world`, where the submitted universal independence premise is satisfiable, this gives a direct false instance of the Theorem-64 type.

The comment calling `EpisodeTrace` “Definition 53 episode” is therefore incorrect. The type needs an opening boundary (or an indexed `BeginsEpisode` witness) in addition to the closing boundary. Separate types are likely needed for open final episodes and closed episodes.

### BLOCKER — `providerVisibilityTheorem` is false from the stated `wellFormed` premise

**Files:** `src/DGamma/Metatheory.idr:28-77,306-374`

`wellFormed` checks that names in a committed view denote installed fibers. It does **not** check that the named provider's immutable `providedValues` actually contains the dependency key. `View` guarantees totality over dependency positions, not validity of each provider/key association.

Concrete countermodel:

- an active root provider with empty provisions and an empty `providedValues` table;
- an active root consumer declaring key `k`, with a manually constructed committed view mapping `k` to that provider;
- disjoint provisions, valid parents, and both committed-view names installed.

The executable `wellFormed` clauses all hold, and `ResolvesAt consumer k provider` holds, but `ProviderAvailable` is impossible because the provider table contains no `k`. Such a state need not be reachable by L-Begin; that is exactly why reachability or a stronger invariant is necessary. Paper Theorem 63 is a theorem about episodes in the global sequence, not an implication from Definition 58 alone.

The TODO comment proposes deriving the missing table membership from well-formed clause 4, but clause 4 contains only installation, so the proposed proof cannot work.

### BLOCKER — `orderingTheorem` is neither faithful nor generally true for its supplied episodes

**Files:** `src/DGamma/Metatheory.idr:383-433`; `README.md` Theorem 63 row

Paper Theorem 63 selects **the provider episode containing the consumer episode's opening**. The submitted type accepts any `LocatedEpisode` of the provider anywhere in the same global trace. A provider can have multiple episodes; the caller may supply a later one. The requested field

```idris
Transitions (episodeStart providerEpisode)
            (episodeStart consumerEpisode)
```

then asks for a forward path from a later state back to an earlier one. Nothing in the premises supplies or implies such a path. A monotone retirement marker inserted between the two locations rules out recovering that earlier state.

Additional fidelity gaps:

- no premise `provider /= consumer`;
- no containment/decomposition witness relating the provider episode around the consumer episode;
- the returned paths need not be slices of the supplied `global` trace;
- strict inequalities `b < b'` and `u' < u` are weakened to arbitrary `Transitions`, which may be `NoTransitions`;
- the standalone claim `L-Begin(m) => gamma_t satisfies d_m` (Equation 58) is not stated;
- clause (1), constancy of the consumer's committed provider throughout its episode, is not stated;
- `ProviderValueConstant` checks only the immutable component table, not constancy of the committed resolution.

Thus the README claim that all three Theorem-63 clauses are precisely stated is false.

### BLOCKER — Theorem 64 is restricted, weaker than the paper, and false on accepted suffixes

**Files:** `src/DGamma/Metatheory.idr:435-575`; `README.md` Theorem 64 row

Besides the false suffix instance described above, the result omits material parts of paper Theorem 64:

- It accepts only a *closed* `EpisodeTrace`. The paper explicitly covers a final episode ending while still Reloading (`r = u`), in which only Equation 59 is asserted.
- No initial committed view `omega` is exposed. `transitionResolutionCoherent` compares each successful step with whatever view is currently stored, but the result does not state that this is the episode-opening `omega`.
- The finish branch states only `activeAt = True`; it does not expose `Active(_, omega)`.
- The abort branch's recovery is measured by the vacuous `AllComponentsIndependent` premise and the underframed `EpisodeTrace`/`ForeignReplay` definitions.

Representation may make stored-view constancy provable internally, but a statement-only theorem must expose the paper's conclusion in its result type. This one does not.

### MAJOR — Empty-program `LAdvance` illegally finishes against a stale target

**File:** `src/DGamma/Calculus.idr:423-429`

The `Reloading []` branch returns L-Finish unconditionally. Paper L-Finish requires `target_n(gamma) = omega`. The review-only executable probe established this sequence:

1. activate a provider;
2. L-Begin an empty-program consumer against it;
3. retire and L-Leave the provider, making the consumer target `Nothing`;
4. execute `LAdvance consumer`.

The evaluator returns `LFinishTag`, sets the consumer `Active`, and leaves `targetFiber consumer = Nothing`. The correct response is L-Divert (aborting before an iteration), not L-Finish.

The list encoding introduces `[]` as a terminal marker absent from the paper's callable iterator type, so it must supply the same target-equality side condition as every other L-Finish branch.

### MAJOR — Restrictions 1 and 3 hollow out the spatial/resolution content

**Files:** `src/DGamma/Calculus.idr:22-34,193-240,371-377`; `src/DGamma/Metatheory.idr:332-359`; `NOTES.md` “Runtime model and deliberate restrictions”

The static `providedValues` table never changes during a fiber's existence, and `providerValueAt` reads it without consulting the lifecycle. Consequently the provider-value constancy part of Theorem 63 is true by immutable record projection, not by confinement, the L-Leave/L-Unload interval, or the guard.

More seriously, `StepEffect` receives only `world`; it cannot read its declared dependencies through the committed view or mutate its own local table. Therefore a component's computation cannot depend operationally on the resolution whose coherence Theorem 64 purports to protect. Views affect scheduling, but not the effect being installed. The ordering guard remains non-vacuous, but the connection “effects run against one stable coeffect resolution” has been normalized away.

This is acceptable as an explicitly named scheduler/registry fragment. It is **not** acceptable as preserving the substance of full paper Theorems 63 and 64. Either weaken and rename the theorems to structural scheduling results, or redesign steps to receive a capability-limited declared-coeffect view and an own-table update channel.

### MAJOR — Foreign replay silently totalizes an off-origin iteration failure to identity

**File:** `src/DGamma/Metatheory.idr:159-189`

For L-Iter/L-Finish/landing-L-Divert, paper `Psi_t` is the iterator's forward map evaluated at the replay state. `worldTransformerFor.forward` instead returns the input unchanged when `runStepEffect` raises at that replay state.

Independence is supposed to prove that a successful actual iteration remains aligned when moved across foreign effects. The replay function should therefore be partial or carry a proof that failure is impossible; silently treating failure as identity weakens the equation and can mask exactly the continuation-stability obligation Definition 60 is meant to supply.

### MAJOR — `CalculusChecks` is a happy-path smoke test, not coverage of the ten-rule evaluator or metatheory-critical guards

**File:** `src/DGamma/CalculusChecks.idr:91-141`

The scenario is useful and nontrivial as a basic provider/consumer lifecycle. It exercises O-Insert, O-Retire, L-Begin, L-Finish, L-Leave, and L-Unload, and checks final ambient recovery/coeffect withdrawal/well-formedness.

It does not exercise:

- O-Remove;
- L-Iter;
- either L-Divert alternative;
- L-Raise;
- an attempted provider L-Unload while `relied` is true;
- target replacement or resolution change;
- zero-step components (which exposed the rule bug);
- registration;
- episode extraction or any statement predicate; or
- well-formedness at every intermediate state.

Because it retires and unloads the consumer before requesting provider retirement, it never actually challenges the withdrawal guard that carries Theorem 63. Passing all three Booleans therefore does not validate the advertised ten-rule semantics.

### MINOR — Same-action determinism is proved, but it is only evaluator-function determinism

**File:** `src/DGamma/Metatheory.idr:79-93`

`applyActionDeterministic` is correct and inhabited. Its proof is `Just` injectivity applied to two equal calls of the same pure function. It establishes that one fixed `Action`, state, and pair of `DecEq` instances cannot return two results.

It does not establish determinism of enabled lifecycle behavior, rule exclusivity, or confluence. In particular, at a stale Reloading state the separate `LDivert` and `LAdvance` actions intentionally represent the aborting and landing L-Divert alternatives. The theorem is meaningful as an API sanity fact, but very weak and should not be counted as substantive metatheory.

### NOTE — Preservation's type appears faithful and non-vacuous

**Files:** `src/DGamma/Metatheory.idr:28-77,95-107`

Unlike the other global declarations, `preservationTheorem` has the right one-step shape for this restricted evaluator. Registry uniqueness and view totality are intrinsic; the Boolean invariant covers parent closure/acyclicity, pairwise provision disjointness, and installed committed providers. I found no immediate transition countermodel to this type. The proof should be a reasonable exhaustive rule proof once the evaluator bug is fixed.

This does not rescue the false `providerVisibilityTheorem`: preservation of “view names an installed fiber” does not strengthen that invariant into “view names a fiber that contains this key.”

## Restriction-by-restriction judgment

1. **Immutable final `providedValues`: not acceptable for full Theorem 63.** It makes value constancy structural/trivial and cannot model values computed by activation. Acceptable only for a renamed static-provision fragment.
2. **External O-Insert/O-Retire pair without nested yield: acceptable through a clearly restricted 59–64 fragment, but not full Definition 47.** It will require redesign before the paper's registration cascades in Progress/Confluence can be claimed.
3. **Registry-separated steps: not acceptable for full spatial/resolution composability.** It removes declared coeffect reads and own-table writes, so effects do not run against their committed resolution.
4. **Finite `List` iterator: acceptable for finite executions and the later bounded-length progress hypothesis.** The empty-list terminal state must obey the paper's target guard.
5. **Whole-program exact independence: not acceptable as encoded.** Reachable step/continuation generators are missing, and `AllComponentsIndependent` quantifies the entire open component type, collapsing `world` to a subsingleton.
6. **Lemmas 54–57 absent: honest but premature.** Several are representationally easy, but failing to package the episode-boundary and rule-shape lemmas allowed false theorem types to survive. At least the field-write, lifecycle-boundary, and view-constancy lemmas should precede global statements.
7. **All global proofs statement-only: disclosure passes; statement quality does not.** Statement-only declarations are acceptable only when faithful and true. Theorem 59 meets that bar; 61/62/63/64 currently do not.

## Statement-type disposition

| Result | Disposition |
|---|---|
| Theorem 59 | **Faithful/non-vacuous for the restricted invariant; unproved.** |
| Theorem 61 | **Reject:** arbitrary mid-episode prefixes, universal-component/subsingleton independence, partial replay totalized to identity. |
| Corollary 62 | **Reject:** arbitrary L-Unload suffixes rather than episode openings; temporal hypothesis vacuous. |
| Theorem 63 | **Reject:** false pointwise helper, unrelated provider episode accepted, missing strict/containment and committed-view clauses, Equation 58 absent. |
| Theorem 64 | **Reject:** false on an Unloading suffix, closed episodes only, opening `omega` and `Active(_, omega)` not exposed, recovery branch vacuous. |

## Proof-plan recommendation

### What can be proved with reasonable effort in the present restricted runtime

1. **Theorem 59** — prove first, after fixing empty-list L-Finish. This is a finite ten-tag case split plus parent/removal and relied-guard lemmas.
2. **Structural Theorem-63 ordering** — after redesigning episode containment and reachability, provider-before-consumer and consumer-before-provider-close are reasonable inductions over the supplied global trace. Equation 58 is a direct L-Begin evaluator lemma. Static provider-value constancy will be easy but should be labeled as a consequence of immutable component data, not the full paper argument.
3. **Structural Theorem-64 coherence** — after a correct episode-opening type, Equation 59 and the first Reloading exit split are straightforward from the evaluator. Prove this separately from terminal recovery.

### What requires redesign before proof should be attempted

4. **Theorem 61** — redesign both the episode start and Definition 60. Use a trace-indexed family of actual component instances, distinct-name pairwise independence, and generators for every reachable list suffix/step and yielded inverse. Make foreign replay partial or prove success at replay states. This is the hardest proof, but becomes a reasonable induction once those definitions are right.
5. **Corollary 62** — after the corrected Theorem 61, this should be a short L-Unload corollary. It should not be proved independently against the current suffix type.
6. **Full Theorem 64** — combine the structural exit theorem with corrected Corollary 62, and add the paper's open-final-episode case and explicit opening view `omega`.
7. **Full substantive Theorems 63/64** — require the larger calculus redesign if CP2 intends paper fidelity rather than a structural scheduler fragment: mutable per-fiber `sigma`, capability-limited reads of declared coeffects through the committed view, and proof that effects are confined to their own table/ambient world.

**Recommended proof order after redesign:** package Lemmas 54–57 (or honest restricted counterparts) → Theorem 59 → Equation 58 and structural Theorem 63 → Theorem 61 → Corollary 62 → full Theorem 64. The paper's numbering puts 61/62 before 63; the structural ordering proof itself does not depend on temporal recovery, while Theorem 64's abort branch does.

**Approval recommendation:** require corrected executable semantics and corrected/non-vacuous theorem types before any CP2 reconsideration. Once corrected, I would demand proofs of Theorem 59, Equation 58/provider ordering, and the structural Equation-59/exit lemma before CP2 approval because they are tractable and would validate the trace encodings. It is defensible to leave the redesigned Theorem 61/Corollary 62 and full recovery branch of Theorem 64 statement-only for this checkpoint if their types survive another adversarial countermodel pass.

## Residual risks

- Even after the immediate statement repairs, the static-table/registry-separated fragment cannot substantiate the paper's claim that installed effects were computed from one stable coeffect resolution.
- Nested registration is absent from iterator execution, so later Progress and Confluence cannot cover the paper's parent/child cascade without changing `StepEffect` or adding a typed registration result channel.
- The exact-equality Section-4 model still lacks the paper's `approximately equal`/observational transport; `worldState` equality is only a restricted instance.
- No supporting equivariance or vestigial-entry theorem is present. This will matter as soon as registration-generated names and confluence are added.
- The clean build attests total typechecking, not truth of exported `Type` aliases. CP1 already demonstrated why countermodel review remains necessary.

```acceptance-report
{
  "criteriaSatisfied": [
    {
      "id": "criterion-1",
      "status": "satisfied",
      "evidence": "Concrete BLOCKER/MAJOR/MINOR findings cite DGamma.Calculus, DGamma.Metatheory, DGamma.CalculusChecks, README, and NOTES; rule-by-rule audit, residual risks, and a proof-plan recommendation are included."
    }
  ],
  "changedFiles": [
    "review-cp2-round1.md"
  ],
  "testsAddedOrUpdated": [],
  "commandsRun": [
    {
      "command": "git archive 6e4fc6d | tar -x ... && idris2 --build dgamma.ipkg",
      "result": "passed",
      "summary": "Fresh archive rebuilt all 8 package modules with Idris 2 0.8.0."
    },
    {
      "command": "idris2 --source-dir src -o eval-checks src/EvalChecks.idr && ./build/exec/eval-checks",
      "result": "passed",
      "summary": "Submitted scenario checks evaluated to (True, (True, True))."
    },
    {
      "command": "idris2 --source-dir src -o rule-probe src/RuleProbe.idr && ./build/exec/rule-probe",
      "result": "passed",
      "summary": "Review-only clean-archive probe printed True, confirming stale-target empty-program LFinish."
    },
    {
      "command": "anchored escape-hatch scan over clean-archive src",
      "result": "passed",
      "summary": "No code-level escape hatches; all 8 modules use %default total."
    }
  ],
  "validationOutput": [
    "Idris 2 version 0.8.0",
    "Clean archive build: 8/8 modules passed",
    "Scenario booleans: recovered=True, no-active-coeffects=True, final-wellFormed=True",
    "Rule probe: stale empty consumer incorrectly finished Active with target=None"
  ],
  "residualRisks": [
    "Static provider tables and registry-separated steps make spatial/resolution claims substantially weaker than the paper.",
    "Nested registration, observational transport, Lemmas 54-57, Progress, and Confluence remain absent.",
    "Statement-only aliases typecheck even when false or vacuous; another countermodel pass is required after redesign."
  ],
  "noStagedFiles": true,
  "diffSummary": "Review-only: added review-cp2-round1.md; no source or package files edited.",
  "reviewFindings": [
    "blocker: src/DGamma/Metatheory.idr:239-247 - AllComponentsIndependent quantifies every constructible component and forces exact world to be subsingleton, hollowing out temporal recovery.",
    "blocker: src/DGamma/Metatheory.idr:213-304 - episode predicates accept arbitrary installed suffixes rather than maximal episodes beginning at L-Begin.",
    "blocker: src/DGamma/Metatheory.idr:366-374 - providerVisibilityTheorem is false because wellFormed does not connect a view's key to the named provider table.",
    "blocker: src/DGamma/Metatheory.idr:383-433 - orderingTheorem accepts an unrelated provider episode and omits material Theorem-63 clauses.",
    "blocker: src/DGamma/Metatheory.idr:537-575 - resolutionCoherenceTheorem is false on accepted Unloading suffixes and omits the open-episode/original-view cases.",
    "major: src/DGamma/Calculus.idr:423-429 - Reloading [] emits LFinish without target equality; executable probe confirms stale activation.",
    "major: src/DGamma/Calculus.idr:22-34,371-377 - immutable tables plus registry-separated steps trivialize value constancy and prevent effects from consuming the resolution protected by Theorem 64.",
    "major: src/DGamma/Metatheory.idr:159-189 - replay totalizes off-origin iteration failure to identity.",
    "major: src/DGamma/CalculusChecks.idr:91-141 - happy path omits four rule tags and never challenges relied/LUnload ordering.",
    "minor: src/DGamma/Metatheory.idr:85-93 - same-action determinism is valid but only proves deterministic evaluation of one fixed pure-function call."
  ],
  "manualNotes": "Final verdict: REJECT. Theorem 59 is the only global statement type judged faithful/non-vacuous as submitted."
}
```
