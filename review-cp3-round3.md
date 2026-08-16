# Checkpoint 3 adversarial review — round 3 (closing round)

**Target:** `18512de2410e48fc34953b813aad9079574e0f39` (`strengthen CP3 registration deletion and canonical premises`)
**Scope:** paper Section 4.4; all round-2 findings; whole-project statement/documentation/build audit
**Mode:** review only. No Idris source, package file, README, NOTES, or tracked test was edited. All probes were under `/tmp`; this report is the sole review artifact.

## Closing status

The old round-2 attacks are individually blocked and the strengthened types are non-vacuous. However, a new **registration-disciplined reachable cross-subtree cycle refutes Lemma 68**, exact deletion still produces a false Lemma-72 result when an external O-Retire occurs inside the episode, and Confluence still lacks the paper's fresh-name renaming/provenance relation. These are false statement types, not the pre-approved proof debts.

# Final verdict: REJECT

## Baseline

- Confirmed exact requested HEAD.
- Pre-review status contained only the pre-existing untracked `paper/` directory.
- Read `review-cp3-round1.md` and `review-cp3-round2.md` in full first.
- Read paper Section 4.4 in `paper/cordis-paper.txt`, including Lemmas 68/70/72 and Theorem 73 with their proofs.
- `idris2 --version`: **Idris 2 0.8.0**.
- Fresh `git archive 18512de` clean build: **passed, 12/12 modules**.

## 1. All three round-2 reachable countermodels replayed

All three action sequences still execute to their old quiet, successful, well-formed endpoints. An external checker mirrors the three conjuncts of `RegistrationStepDiscipline`: parent Reloading at child insertion, no later insertion of the name, and child retirement before the first submitted parent-recovery boundary.

| Round-2 attack | Replay | Why the new premise fails |
|---|---|---|
| inactive-parent child insertion | `discipline=False`, `quiet=True`, `noFailed=True`, `wellFormed=True` | parent Reloading diagnostic is `False`; a separate negative Idris probe fails exactly on `ReloadingPhase (Inactive Nothing)` |
| name reuse after O-Remove | same final flags; name 0 has two O-Inserts | the first root insertion's `NoLaterInsertion 0` is contradicted by the later child insertion |
| retired-parent/open-child | same final flags | insertion sees `parentReloading=True`, but `retirePrecedesFirstRecovery=False` |

Thus each old trace fails the intended new premise, not an unrelated reachability/evaluator condition.

A typed non-vacuity probe also constructs a checked trace

```text
O-Insert 0 Root; L-Begin 0; O-Insert 1 (ChildOf 0)
```

and a complete `RegistrationDiscipline` inhabitant. The premise itself is not vacuous.

## 2. BLOCKER — new disciplined cross-subtree countermodel to Lemma 68

**File:** `src/DGamma/CP3.idr:164-303,416-429`

The new discipline still does not imply `SupportWellFounded`. A checked 20-action trace uses fresh names `X=0, A=1, C=2, B=3, D=4` and two keys:

1. insert root X providing key A; insert roots A and B depending on A and B respectively;
2. activate X; begin A;
3. while A is Reloading, insert child C providing B; activate C; finish A;
4. begin B against C;
5. retire C; retire/leave X; leave/unload A; unload/remove X;
6. while B is still Reloading, insert child D providing A.

Every action is accepted by `checkedApplyAction`. No name is reused. C is retired before A's first L-Leave, and D's parent has no recovery step in the remaining empty suffix. Both child insertions see Reloading parents. The executable final diagnostics are:

```text
[discipline, wellFormed, C<B, D<A, not(B<C), not(A<D),
 parent(C)=A, parent(D)=B, supported(A), supported(C),
 supported(B)||supported(D)]
=
[True, True, True, True, True, True, True, True, False, False, False]
```

Precedence alone is the acyclic graph `C -> B` and `D -> A`. Parent edges add `A -> C` and `B -> D`. Therefore the submitted `SupportPath` relation contains

```text
A -> C -> B -> D -> A
```

Retiring C does not remove this cycle: paper Equation 62 and `SupportPath` read parent/dependency/provision fields, not retirement.

This is the requested cross-subtree-adoption variant satisfying the registration-discipline premise. Consequently `supportWellFoundedTheorem` remains a **false type**.

### Other new support attacks

- Deep grandchild chain: a three-level checked trace has `discipline=True`, is quiet/well formed, supports all three names, and has no precedence edge. No counterexample there.
- Reinsert after O-Retire without O-Remove: rejected by operational freshness.
- Reinsert after O-Remove: operationally possible but rejected by `NoLaterInsertion`.
- Immediate descendant-provider cycle: with the parent genuinely Reloading, O-Insert is rejected because the already-active provider's declared provision conflicts.

These failures do not save Lemma 68 from the staggered cross-subtree trace.

The new trace is not quiescent, so it does **not** directly refute `supportAtQuiescenceTheorem`; all three old Lemma-70 endpoints now fail the discipline premise as intended.

## 3. Identity deletion and partial-keep replay

**File:** `src/DGamma/CP3.idr:1487-1516`

The round-2 identity bug is fixed:

- the unchanged generic identity constructor fails exactly at `KeepAction`'s new `Not (deletable action)` argument;
- a partial variant that keeps the episode's L-Begin but drops its body fails at the same field;
- a positive total probe proves that if the original head is deletable, every `ActionSubsequence` witness consumes that original head without consuming a survivor action; specialized with `DeleteEpisodeOwner Refl`, the selected L-Begin is structurally forced out.

This is a genuine repair, not a regression guard that merely moved the mismatch.

## 4. BLOCKER — Lemma 72 now deletes selected external O-Retire

**File:** `src/DGamma/CP3.idr:1522-1654`

`EpisodeDeletedActor.DeleteEpisodeOwner` marks **every** selected-owner action in the closed episode deletable. That includes root O-Retire. Exact filtering therefore forces the external retirement out, while `controlsPreservedOutside` still compares the selected fiber when `R=[]`, including its retirement flag.

Minimal checked trace:

```text
O-Insert 0 Root; L-Begin 0; L-Finish 0;
O-Retire 0; L-Leave 0; L-Unload 0
```

It is registration-disciplined, quiet, successful, semantically total, and has no dependent or registered episode. Exact episode filtering leaves only the pre-episode O-Insert. Runtime comparison prints:

```text
original: [wellFormed, quiet, noFailed, retired, inactive]
          [True, True, True, True, True]
survivor: [True, False, True, False, True]
```

The effect state is unchanged, but the survivor is unretired. Hence `ControlEquivalentOutside [] originalFinal survivorFinal` is impossible.

The paper proof exposes the intended qualification. At `paper/cordis-paper.txt:2273-2275` it says the deleted steps of n “write no field but theta_n.” Literal O-Retire writes `tau_n`; therefore the proof is silently talking about selected **lifecycle** steps, not every selected-owner rule. `EpisodeDeletedActor` must retain external orchestration (or the result relation must change).

A second endpoint overconstraint remains: `RegisteredNamesWithdrawn` requires each R-name to be present/vestigial in the original final. The hypotheses permit a later original O-Remove of an already-retired, never-activated child, in which case it is absent from both endpoints. The relation needs a vestigial-or-already-absent original case.

Thus the identity hole is closed, but `deletionTheorem` is still a **false statement type**.

## 5. Lemma-72 hypothesis field check

The specific round-2 premise omissions are otherwise repaired:

- `NoRegisteredEpisode` now rejects every R-owned L-Begin, covering both open and closed episodes;
- `NoDependentClosingEpisode` examines precedence at each located consumer episode's start rather than only in the final registry;
- `TraceComponentsTotal` covers every O-Inserted component occurrence in the whole trace;
- `RegisteredNamesDuring` is bidirectional and includes insertion-before-retirement evidence;
- `RegistrationDiscipline` supplies the trace-level no-rebirth/retirement protocol;
- all three trace segments, effect recovery, outside-R control, and withdrawal are explicit.

The protocol is conservative and satisfiable, but its `ParentRecoveryStep` documentation is inaccurate: the constructors are L-Leave/L-Divert/landing Raise-Divert, while Table 1 executes the accumulator only at L-Unload. It is really a “first exit toward recovery” boundary and is stronger than the literal accumulator timing.

## 6. CanonicalInputPlacement field check and positive instance

The round-2 canonical placement omissions are repaired:

- `RootInputsBeforeLifecycle` ranges over O-Insert, O-Retire, and O-Remove at every live root, including unsupported roots;
- combined support order, uniqueness, ordered contiguous blocks, and lifecycle coverage remain present;
- `CanonicalEndpointRelation` can represent a nonempty withdrawal list with exact effects and full outside-list controls.

A total probe constructs an actual empty reconciliation-normal-form `CanonicalSchedule`, including `LinearizesSupport`, `CanonicalInputPlacement`, endpoint relation, and all empty-trace Confluence premises. It typechecks. The submitted nonempty reconciliation aggregate also remains twelve-for-twelve true. The strengthened package is not globally uninhabitable.

## 7. BLOCKER — Confluence still omits registration identity and Lemma-56 renaming

**File:** `src/DGamma/CP3.idr:1334-1442,1656-1687`

`SameExternalOrchestration` intentionally compares only root actions and skips child registrations. Yet `confluenceTheorem` concludes exact-name, exact-domain `SystemEquivalent leftFinal rightFinal`. Paper Theorem 73(2) explicitly compares results **after a renaming as in Lemma 56**.

Two checked traces have the same root input and differ only in the fresh internal child name:

```text
left:  O-Insert 0 Root; L-Begin 0; O-Insert 1 (ChildOf 0);
       L-Finish 0; L-Begin 1; L-Finish 1
right: O-Insert 0 Root; L-Begin 0; O-Insert 2 (ChildOf 0);
       L-Finish 0; L-Begin 2; L-Finish 2
```

Both endpoint vectors are:

```text
[wellFormed, quiet, noFailed, rootActive, childActive,
 rootSupported, childSupported]
= [True, True, True, True, True, True, True]
```

Domain flags are `[child1-left, child1-right, child2-left, child2-right] = [True, False, False, True]`. A bijection swapping 1 and 2 gives the paper result. Exact `SystemEquivalent` is impossible because `FiberControlMaybeRelated` has no Just/Nothing constructor.

There is an independent provenance failure. `RegistrationDiscipline` checks timing/no-rebirth/retirement but not that a parent iterator yielded a registration of a particular component. An empty parent program can “register” either an empty child or `providerComponent`; both checked same-root-input traces satisfy the timing discipline and finish quiet, but their ambient provider flags are respectively `False` and `True`. These are not Definition-47 executions, but the theorem admits them.

The schedule-local withdrawal list does not repair the theorem's final third result, which remains exact `SystemEquivalent`. `canonicalTrace` itself also has no registration-discipline/tree-correspondence field. `confluenceFromCanonicalSchedules` only handles zero withdrawals and literal canonical-final equality.

Therefore `confluenceTheorem` remains a **false type**, independently of its pre-approved missing constructive proof.

## 8. Erratum #3 documentation audit

`NOTES.md` accurately quotes the critical Lemma-68 proof step: a subtree fiber is “registered by an activation of m or of one of m's descendants, hence at a step after the L-Begin of m.” It also accurately contrasts that with printed O-Insert, which requires only a currently fresh name and a present parent. The three original countermodels and the fact that the operational rule itself remains unchanged are disclosed precisely.

Two corrections are still needed:

1. Calling Reloading + no-rebirth + retirement “the paper-intent repair” is too strong. The paper explicitly permits name reissue after O-Remove; no-rebirth is a conservative unstamped-name specialization. Retirement-before-exit is relevant to Lemma 70, not sufficient to prove Lemma 68.
2. The new cross-subtree trace shows that even the three-premise repair does not establish the paper's registration-rank argument. The proof excludes one descendant-provider pattern but not a staggered cycle alternating two parent subtrees and two precedence edges.

The selected-O-Retire issue is a separate likely paper erratum/ambiguity: Lemma 72's literal deletion phrase includes O-Retire, while its proof assumes all deleted selected steps write only lifecycle `theta` and Theorem 73 must preserve orchestration inputs.

## 9. CP3StatementChecks

The round-2 identity-style guards are now real projections:

- Lemma 68 is applied with reachability, registration discipline, and acyclicity; both `combinedWellFounded` and `uniqueSupportSolution` are projected;
- Lemma 70 separately requires the discipline;
- canonical uniqueness, combined order, coverage, all-root placement, external inputs, block order, outside controls, and withdrawals are projected;
- all three deletion segments, effects, outside controls, and withdrawal are projected.

This repair passes. Residual risk: the module cannot guard fields that do not exist—selected deletion being lifecycle-only, canonical registration provenance, or a Lemma-56 bijection. It also has no constructor-level guard specifically projecting `KeepAction`'s `Not deletable`, although the external negative probe confirms the constructor changed.

## 10. Whole-project documentation audit

The correspondence table has 70 substantive rows. Previously approved Section 3 and CP2 rows preserve their accepted proved/partial/stated distinctions and disclose the known specializations: finite Definition-32 approximation, partial Lemma-38 transport, partial coeffect undos, finite static iterators, host-level registration, trace-anchored full-effect monoids, exact effect equality, and dictionary alignment.

CP3 wording is materially improved: Lemmas 68/70/72 and Theorem 73 are labeled **under repair/review**, not faithful or proved. The final Status also calls them candidate statements. Therefore the old round-2 documentation overclaim is fixed.

Remaining documentation debt:

- no Lemma-56 renaming specialization/omission is disclosed;
- `ParentRecoveryStep` is described as executing the accumulator although L-Unload is the executing rule;
- the three-clause protocol is called paper-intent despite global no-rebirth being stricter than the paper;
- the newly demonstrated cross-subtree, selected-O-Retire, arbitrary-child provenance, and already-absent-R defects are absent from NOTES/Status.

The cautious “under review” labels prevent a false claim of acceptance, but the project cannot receive final acceptance while those statement types remain false.

## 11. Whole-project status counts

Counts below use correspondence-table rows; “complete” means an executable definition or proved theorem at the status claimed.

| Section | Rows | Complete/proved | Partial | Stated-only rows |
|---|---:|---:|---:|---:|
| 3.1 effects | 22 | 22 | 0 | 0 |
| 3.2 coeffects | 10 | 10 | 0 | 0 |
| 3.3 unified context | 11 | 6 | 2 | 3 |
| 4 calculus/metatheory | 27 | 16 | 6 | 5 |
| **Total** | **70** | **54** | **8** | **8** |

There are **11 source `TODO(proof)` declaration sites**: 3 in Unified, 3 in Metatheory, and 5 in CP3. Because Thm 64, Thm 66, and Lemma 70 have proved partial cores but statement-only final aliases, declaration-site counts overlap the row-level “partial” category.

Pre-approved honest debts remain: temporal recovery (Thm 61/Cor 62/recovery branch of Thm 64), Progress induction, and constructive Confluence/canonicalization. Additional open Section-3 aliases are Lemma 35 and Theorems 40/42. The rejection is not based on those honest debts; it is based on false Lemma-68/Lemma-72/Confluence statement types.

## 12. Clean build, runtime aggregates, scans, and hygiene

- Fresh archive build: **12/12 passed**.
- Submitted runtime aggregate:

```text
[True, True, True, True, True, True,
 True, True, True, True, True, True]
```

- All 12 package modules contain exactly one `%default total`.
- Anchored source scans found no `believe_me`, `assert_total`, postulate, `%unsafe`, unsafe FFI, `%default partial`, partial/covering declaration, or named metavariable hole.
- 11 source `TODO(proof)` sites; 15 textual source+README+NOTES hits. No TODO is accepted as an inhabitant.
- `git diff --check` and report whitespace scan passed.
- No staged files. Final untracked paths are the pre-existing `paper/` and this requested report.

## Probe evidence summary

All probe sources were outside the repository.

| Probe | Result | Evidence |
|---|---:|---|
| all three round-2 trace replays | passed | old endpoints reproduced; each intended discipline conjunct identified |
| `DirectChildExpectedFailure` | rejected as intended | exact `ReloadingPhase (Inactive Nothing)` mismatch |
| `RegistrationDisciplineNonVacuity` | passed | complete typed discipline inhabitant for a checked nested insertion |
| cross-subtree support probe | passed | checked 20-action trace; discipline/well-formed/edge/parent flags establish mixed cycle |
| deep/reuse/immediate-cycle variants | passed | deep chain disciplined/acyclic; reuse and immediate cycle attempts rejected as described |
| round-2 identity replay | rejected as intended | exact `Not deletable` mismatch |
| partial L-Begin keep replay | rejected as intended | same mandatory-deletion field |
| deletion structural lemma | passed | deletable head must be consumed without survivor |
| selected O-Retire runtime | passed | original retired endpoint vs forced unretired survivor |
| canonical positive probe | passed | actual empty canonical schedule and Confluence premises typechecked |
| fresh-name Confluence runtime | passed | two quiet supported endpoints; domain `[True,False,False,True]` |
| arbitrary-child runtime | passed | same empty parent/input, empty vs provider child, ambient `False` vs `True` |
| submitted aggregate runner | passed | twelve `True` values |

## Per-round-2-finding disposition

| Round-2 finding | Closing disposition |
|---|---|
| three reachable attacks refute Lemmas 68/70 | **Old attacks fixed, finding reopened:** each old trace fails the intended premise, but the new cross-subtree trace satisfies it and still refutes Lemma 68 |
| DeletionResult identity-inhabitable | **Fixed:** identity and partial-L-Begin keep are structurally excluded |
| Lemma-72 hypotheses weaker than paper | **Specific fields fixed:** open R episodes, relevant-time edges, all-trace totality, and retirement provenance are present; **new blocker:** exact predicate deletes selected O-Retire and the endpoint mishandles already-absent R |
| canonical placement/withdrawn endpoints incomplete | **Those fields fixed:** all root steps and withdrawal relation are present; **new blocker:** theorem still lacks registration-tree provenance and Lemma-56 renaming |
| CP3StatementChecks identity/incomplete guards | **Fixed for requested projections:** current guards apply/project real fields |
| documentation overclaims | **Substantially fixed:** CP3 is labeled under review; residual undisclosed/incorrect specializations remain |
| clean build/runtime/scans | **Pass** |

## Final findings

1. **BLOCKER — `src/DGamma/CP3.idr:164-303,416-429`:** a checked, registration-disciplined, no-rebirth cross-subtree trace has acyclic precedence but a mixed `SupportPath` cycle; Lemma 68 remains false.
2. **BLOCKER — `src/DGamma/CP3.idr:1522-1654`:** mandatory exact deletion removes selected external O-Retire and contradicts outside-R retirement control; Lemma 72 remains false.
3. **BLOCKER — `src/DGamma/CP3.idr:1334-1442,1656-1687`:** Confluence skips internal fresh names but concludes exact-domain equality without paper Lemma-56 renaming.
4. **BLOCKER — same files:** timing-only registration discipline allows an empty parent program to insert arbitrary child components, yielding divergent same-root-input endpoints.
5. **MAJOR — `RegisteredNamesWithdrawn` at `src/DGamma/CP3.idr:1233-1250`:** original-already-absent R names are unexpressible.
6. **MAJOR — `src/DGamma/CP3.idr:202-219`:** `ParentRecoveryStep` is documented as accumulator execution but represents earlier exit boundaries and omits the actual L-Unload execution rule.
7. **MAJOR — `README.md` Lemma-68/Thm-73 rows and `NOTES.md` Erratum/CP3/Status:** under-review wording is honest, but renaming, cross-subtree failure, selected retirement, and the extra no-rebirth restriction are not fully catalogued.
8. **VERIFIED:** all three old support attacks fail their intended new premise; identity deletion is structurally excluded; all-root placement and nonempty canonical withdrawal fields exist; regression projections are substantive.
9. **VERIFIED:** clean archive 12/12, all runtime aggregates true, no escape hatch/partial module/named hole.

# Final verdict: REJECT

```acceptance-report
{
  "criteriaSatisfied": [
    {
      "id": "criterion-1",
      "status": "satisfied",
      "evidence": "Concrete BLOCKER/MAJOR findings cite DGamma.CP3, CP3StatementChecks, README, NOTES, and paper lines; checked runtime countermodels, expected-failure probes, typed non-vacuity/canonical witnesses, clean build, scans, and residual risks are recorded."
    }
  ],
  "changedFiles": [
    "review-cp3-round3.md"
  ],
  "testsAddedOrUpdated": [],
  "commandsRun": [
    {
      "command": "git archive 18512de | tar -x ... && idris2 --clean dgamma.ipkg && idris2 --build dgamma.ipkg",
      "result": "passed",
      "summary": "Fresh archive rebuilt all 12 package modules under Idris 2 0.8.0."
    },
    {
      "command": "round-2 reachable replay and RegistrationDiscipline diagnostics",
      "result": "passed",
      "summary": "Reproduced all three endpoints; phase, no-rebirth, and retirement provenance reject them respectively."
    },
    {
      "command": "idris2 --check DirectChildExpectedFailure.idr",
      "result": "failed",
      "summary": "Expected rejection exactly at ReloadingPhase for the inactive parent."
    },
    {
      "command": "idris2 --check RegistrationDisciplineNonVacuity.idr",
      "result": "passed",
      "summary": "Constructed a complete typed discipline witness for a checked child insertion during Reloading."
    },
    {
      "command": "cross-subtree, deep-chain, reuse, and descendant-cycle registration probes",
      "result": "passed",
      "summary": "Found the disciplined A-C-B-D mixed cycle; other requested variants behaved as reported."
    },
    {
      "command": "identity and partial-keep deletion negative probes; DeletionStructureProbe",
      "result": "passed",
      "summary": "Negative probes were rejected at Not deletable; positive structural forced-deletion lemma typechecked."
    },
    {
      "command": "DeletionRetireRuntime, RenamingCountermodelRuntime, ArbitraryChildCountermodelRuntime",
      "result": "passed",
      "summary": "Exposed selected-retirement control mismatch, fresh-name exact-domain mismatch, and arbitrary child-component divergence."
    },
    {
      "command": "idris2 --check CanonicalPositiveProbe.idr",
      "result": "passed",
      "summary": "Constructed an empty reconciliation canonical schedule and complete empty-trace Confluence premises."
    },
    {
      "command": "CP3 runtime aggregate runner",
      "result": "passed",
      "summary": "All eleven individual CalculusChecks values plus allRuleChecks evaluated True."
    },
    {
      "command": "escape-hatch, partiality, TODO, module-totality, diff, staged-file, and whitespace scans",
      "result": "passed",
      "summary": "No escape hatch/partial declaration/named hole; 11 source TODO sites; 12 total modules; no staged files."
    }
  ],
  "validationOutput": [
    "Clean archive build: 12/12 passed.",
    "Submitted runtime checks: [True, True, True, True, True, True, True, True, True, True, True, True].",
    "Cross-subtree cycle: discipline/wellFormed/C<B/D<A/parent edges all True; all four cycle members unsupported.",
    "Identity and partial-L-Begin keep rejected at KeepAction Not deletable.",
    "Selected retirement: original [True,True,True,True,True], survivor [True,False,True,False,True].",
    "Fresh-child domain: [True,False,False,True].",
    "Typed registration-discipline and canonical positive witnesses passed."
  ],
  "residualRisks": [
    "Lemma 68 remains false under the submitted discipline due a staggered cross-subtree mixed cycle.",
    "Lemma 72 remains false because exact deletion removes selected external retirement and cannot express already-absent R names.",
    "Confluence remains false without yielded-registration provenance and Lemma-56 renaming.",
    "Pre-approved temporal recovery, Progress induction, and constructive canonicalization remain open."
  ],
  "noStagedFiles": true,
  "diffSummary": "Review-only: added review-cp3-round3.md; no tracked project source, documentation, package, or test file edited and no commit.",
  "reviewFindings": [
    "blocker: src/DGamma/CP3.idr:164-303,416-429 - disciplined reachable cross-subtree cycle refutes Lemma 68.",
    "blocker: src/DGamma/CP3.idr:1522-1654 - selected O-Retire is mandatorily deleted, falsifying outside-R control.",
    "blocker: src/DGamma/CP3.idr:1334-1442,1656-1687 - exact Confluence omits fresh-name renaming and yielded-registration provenance.",
    "major: src/DGamma/CP3.idr:1233-1250,202-219 - already-absent R and recovery-boundary semantics are misrepresented.",
    "major: README.md and NOTES.md - candidate wording is cautious, but remaining specialization/erratum gaps are not fully disclosed.",
    "verified: old round-2 attacks are blocked, deletion identity is excluded, canonical all-root/withdrawal fields and statement projections are real, build/runtime/scans pass."
  ],
  "manualNotes": "Final verdict: REJECT. The rejection is for false CP3 statement types, not for the explicitly pre-approved missing proofs."
}
```
