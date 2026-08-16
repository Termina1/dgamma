# Checkpoint 3 adversarial review — round 2 (final)

**Target:** `4a0f411457540e7913ddb737b8a401924f108c58` (`repair CP3 support and confluence statements`)
**Scope:** CP3 statement repairs for paper Definition 67, Lemma 68, Definition 69, Lemmas 70/72, Theorems 66/73, Equation 53 and Equation 62; whole-project documentation/build/escape-hatch audit
**Mode:** review only. No source edit or commit; all probe sources and archive builds are under `/tmp`.

## Baseline and round-1 replay

- Confirmed `HEAD` is exactly requested commit `4a0f411`.
- The pre-review working tree contained only the pre-existing untracked `paper/` directory. This requested report is the only review-created repository file.
- Read `review-cp3-round1.md` in full. Per instruction, accepted Ordering/Theorem 63 was not re-audited.
- Replayed the exact round-1 `SupportCountermodel.idr` against a clean archive of `4a0f411`. Idris rejects it at the old theorem application, with the first mismatch exactly:

  ```text
  PrecedenceAcyclic natEq mixedState
  versus
  ReachedFromEmpty ... mixedState
  ```

  at the `mixedAcyclic` argument. Thus the arbitrary-snapshot attack is blocked precisely by the newly inserted reachability argument; no earlier field/type mismatch masks that guard.

## BLOCKER — the new reachability guard does not establish Lemma 68 under name reuse

**Files:** `src/DGamma/CP3.idr:126-247,1129-1144`; `src/DGamma/Calculus.idr:924-934`; paper Lemma 68

A reachable variant of the round-1 mixed cycle exists in this calculus. The sequence uses the paper-permitted removal/reissue behavior and the mechanization's explicit `OInsert child (ChildOf parent)` action:

1. insert root provider `0` and root consumer `1`;
2. activate `0`, then activate `1` against `0`;
3. retire/leave `0`; leave/unload `1`; unload/remove `0`;
4. reinsert the same name `0` as a child of still-present `1`;
5. activate child `0`, then activate parent `1` against `0`.

Every step is accepted by `checkedApplyAction`. The final state has parent edge `1 -> 0` and precedence edge `0 -> 1`, hence a combined `SupportPath 1 1`, while precedence alone remains acyclic. The closed executable probe printed:

```text
Just [True, True, True, True,
      False, True, False, False,
      False, False, True, True, True, True]
```

in the order: well-formed, quiet, no failures, current Active totality diagnostic; four precedence edges `00,01,10,11`; support membership `0,1`; Active `0,1`; child-parent shape and root-parent shape. Thus the final state recreates the exact empty-support/two-Active countermodel **through a checked trace from the empty registry**.

The paper's Lemma-68 proof ranks a name by “the step that registered” it and argues a subtree provider is registered by an activation of its ancestor. That argument does not survive removal/reissue, and in this mechanization a child-parent `OInsert` is an unrestricted explicit orchestration action, not necessarily a registration yielded by the parent's activation. `ReachedFromEmpty` records only a trace; it records neither a per-live-entry non-reused birth identity nor the ancestry/activation provenance needed by the paper proof. In fact name reuse is not necessary: `OInsert 1 Root consumer; OInsert 0 (ChildOf 1) provider; activate 0; activate 1` reaches the same mixed cycle directly; its flags were `[wellFormed, quiet, noFailed, edge01, support0, support1, active0, active1] = [True, True, True, True, False, False, True, True]`.

Consequences under the acceptance contract:

- `supportWellFoundedTheorem` is a **false statement type**: its result contains `SupportWellFounded`, contradicted by the reachable combined cycle. A typed probe packaged an exact `ReachedFromEmpty` and `SupportPath 1 1` for the same dynamically produced final state (`isJust` for the combined package evaluated `True`); precedence inspection shows its sole edge is `0 -> 1`, and the round-1 total acyclicity proof depends only on those unchanged component declarations.
- The same state is quiet, successful, and its two submitted components are semantically total on provision. A separate total Idris probe inhabited `ComponentTotalOnProvision providerComponent` and `ComponentTotalOnProvision consumerComponent` by inversion on every `ProgramFinishes`; it compiled and ran. Therefore the repaired `supportAtQuiescenceTheorem` remains false as well: least support is empty while both fibers are Active.
- This also invalidates documentation claims that reachability alone repaired the first round-1 blocker.

The repair needs an actual restriction/invariant, not merely the current reachability wrapper: e.g. forbid explicit child insertion except as the parent activation's registration primitive; forbid name reuse in the theorem's live genealogy; use generation-stamped names; or strengthen the premise with `SupportWellFounded`/the registration-provenance property directly.

## BLOCKER — `DeletionResult` still admits the unchanged original trace

**File:** `src/DGamma/CP3.idr:1162-1190,1273-1306`; paper Lemma 72

`ActionSubsequence deletable original surviving` says only that every *dropped* action satisfies `deletable`. `KeepAction` has no premise that the kept action is non-deletable and there is no exactness/coverage condition requiring a deletable action to be dropped. Therefore every trace has an identity witness, recursively using `KeepAction ... Refl`.

This makes the redesigned Lemma-72 result trivial whenever `R = []`, the common case where the selected episode registers no fibers. A review-only total Idris probe defines, for **every** located closed episode:

```idris
identityDeletionResult :
  (episode : LocatedClosedEpisode ... selected global) ->
  DeletionResult ... global selected episode []
```

It takes `survivingBefore`, `survivingEpisode`, and `survivingAfter` to be the three unchanged original segments; inhabits all three `ActionSubsequence`s by keeping every action; uses reflexive effect/control relations; and eliminates `RegisteredNamesWithdrawn []` vacuously. The probe compiled and ran. In particular, it keeps L-Begin, every selected-actor action, and L-Unload in `[b,u]`, the opposite of paper Lemma 72's “deleting the steps that act on n in [b,u]”.

`RegisteredNamesWithdrawn` prevents identity only for nonempty `R`; it does not require deletion of the selected actor, and even for nonempty `R` the selected episode steps can still all be kept. The result needs an exact filter/bidirectional characterization: kept actions are precisely the non-deletable ones (or constructors that force deletion whenever the predicate holds), separately for the before/episode/after predicates.

This independently fails the acceptance rule that a repaired statement must not be trivially inhabitable.

## Additional reachable attack — parent retirement leaves a child Active

The same root modeling gap gives an even smaller Lemma-70 counterexample, independent of a mixed support cycle. With empty-dependency/empty-provision/empty-program components:

```text
OInsert 0 Root; LBegin 0;
OInsert 1 (ChildOf 0); LBegin 1; LFinish 1; LFinish 0;
ORetire 0; LLeave 0; LUnload 0
```

is a fully checked trace. The final flags are:

```text
[wellFormed, quiet, noFailed, parentRetiredInactive,
 childUnretiredActive, supportParent, supportChild]
= [True, True, True, True, True, False, False]
```

Precedence is empty (hence acyclic), and both components satisfy semantic Definition 69 vacuously because their provision is empty. The final state is reached from empty and quiet, yet the unretired Active child is unsupported because its parent is retired. Paper Lemma 70's parent argument says the parent's accumulator retires names it registered (Definition 47). Here `OInsert child (ChildOf parent)` is an external action unrelated to the parent's accumulator, so that argument is unavailable. Thus `supportAtQuiescenceTheorem` is false even if Lemma 68 were repaired separately.

## CanonicalSchedule field audit against Equation 62 / Theorem 73(1)

**Files:** `src/DGamma/CP3.idr:910-1118`; paper Theorem 73(1), Equation 62

### Fields that pass

- `LinearizesSupport.orderUnique`, `orderSound`, and `orderComplete` genuinely make `supportOrder` a duplicate-free enumeration of the executable support set.
- `supportPathsOrdered` quantifies `SupportPath`, the nonempty transitive closure of both `PrecedenceEdge` and `ParentSupportEdge`. The combined closure, not merely direct precedence, is therefore ordered.
- `LocatedOpenEpisodeBlock` plus `ActorLifecycleOnly`, `NoLifecycleBy` before/after, final Active status, and the global decomposition encode one final open actor-only contiguous episode. `blocksFollowOrder` ties those blocks to list order. `LifecycleActorsCovered` excludes lifecycle history of unsupported actors. Taken together, the round-1 uniqueness/contiguity/one-block defects are repaired.

### BLOCKER — orchestration placement still omits part of the paper condition

`CanonicalInputPlacement.rootInputFirst` (`CP3.idr:1069-1077`) mentions only the `OInsert` of each **supported** root fiber. Paper Theorem 73 and its proof move **every orchestration step at every orchestrator-inserted fiber** before every lifecycle step, including O-Retire/O-Remove and root fibers outside A. The current type permits, for example, the sole supported root's open episode followed by O-Insert/O-Retire/O-Remove of an unused root fiber: all current canonical fields hold, but those root orchestration steps were not moved before the lifecycle block as the paper requires.

The child field likewise records only a child's `OInsert` before its own lifecycle actions; it does not itself state the paper's classification/order for every non-root orchestration action. Checked applicability supplies some of that ordering operationally, but it does not repair the missing all-root-input quantification.

This is a remaining Theorem-73(1) statement omission, so the comments at `CP3.idr:1089-1092,1353-1357` and README's “faithfully stated” claim still overstate the type.

### Explicit-registration inconsistency

The no-nested-registration specialization classifies every `OInsert`, including `OInsert child (ChildOf parent)`, as an orchestration input that `SameOrchestration` must retain. But `RegisteredNamesDuring` simultaneously treats that same external `OInsert` as a registration made by the selected episode, and `DeletionResult` permits deleting all actions owned by that child. In the paper, a nested registration is inside the lifecycle effect map and is *not* an external orchestration input. The mechanization cannot treat one explicit action as both without making deletion and “same orchestration” pull in opposite directions. The reachable parent/child attacks above are the operational consequence.

Relatedly, `CanonicalSchedule.canonicalEndpoint` requires full `SystemEquivalent`, hence exact domain agreement, and carries no set of withdrawn names. That is coherent only if the declared no-nested specialization forces `R=[]`. But the submitted Lemma-72 encoding explicitly admits nonempty `R` via child O-Inserts. When that path is exercised, the package cannot express Theorem 73(1)'s endpoint “up to the names whose entries the reduction withdraws”.

## Equation-53 control equivalence audit

**Files:** `src/DGamma/CP3.idr:591-833`; paper Equation 53

**Pass, as a documented stronger finite specialization.** Field by field:

- domain: `FiberControlMaybeRelated` relates only Nothing/Nothing or Just/Just;
- immutable `d,p,e`: the shared `component` index preserves dependencies, provisions, and the complete static program exactly;
- `pi` and `tau`: parent and retirement equalities are explicit;
- `theta`: constructors preserve lifecycle variant; Inactive/Unloading outcomes, Reloading remaining iterator, committed view, and accumulator are all retained;
- function fields: accumulators are compared pointwise;
- effect side: `SystemEquivalent.effectsEquivalent` compares ambient state and every per-name table exactly, which is stronger than the paper's open observational relation and is explicitly documented.

No Equation-53 control field is still omitted. Exact component/iterator/accumulator equality is stronger than the paper's relation-up-to-equivalence, but it is not uninhabitable in this deterministic static-list specialization. A review-only reconciliation probe constructed `ControlEquivalent full full` at the submitted full-stack reconciliation endpoint via `systemEquivalentReflexive`; it compiled and printed `True`.

## Further Lemma-72 faithfulness defects

**File:** `src/DGamma/CP3.idr:1204-1351`

In addition to the generic identity inhabitant:

1. `NoRegisteredEpisode` (`lines 1221-1231`) forbids only a `LocatedClosedEpisode`. Paper Lemma 72 says no registered fiber “have an episode”, which includes an episode still open at the endpoint. The checked parent/child trace above leaves exactly such an open child episode while this predicate would see no closed child episode.
2. `NoDependentClosingEpisode` tests `PrecedenceEdge` only in `finalState`. A dependent whose closing episode occurred and whose entry was later removed is absent from that graph, making the hypothesis vacuous despite the forbidden closing episode in the supplied global trace. Name reuse makes the mismatch worse.
3. `RegisteredNamesDuring` identifies external `OInsert ChildOf` inputs as the paper's accumulator-linked registrations, but the model contains no evidence that the selected accumulator will retire them. Nevertheless `RegisteredNamesWithdrawn` demands that they be retired, Inactive, empty in the original final state and absent in the survivor. The open-child execution demonstrates why that conclusion does not follow.
4. `deletionTheorem` and `confluenceTheorem` quantify `ComponentsTotalOnProvision` only over their final registries (`CP3.idr:1338,1376-1377`). Paper Lemma 72/Theorem 73 require every component in the sequence to be total. A component removed before the endpoint, or an earlier incarnation of a reused name, is outside the submitted premise even though its episode is in `global`.

These are proposition-shape defects, not merely missing replay proofs.

## CP3StatementChecks audit

**File:** `src/DGamma/CP3StatementChecks.idr`

Several guards are substantive projections: Lemma 70's new premise sequence (`lines 15-27`), support-order uniqueness/combined closure, lifecycle coverage, input package, the full control relation, episode subsequence, outside-R control, and withdrawal.

Coverage is incomplete and one check is vacuous:

- `supportLemma68Guard` (`lines 32-35`) is the identity function on the theorem alias. It projects neither `ReachedFromEmpty`, `combinedWellFounded`, nor `uniqueSupportSolution`; any replacement type would pass this “guard”.
- no check projects `blocksFollowOrder`, so deleting the repaired ordering of the episode blocks would leave the module compiling;
- deletion checks do not project `beforeDeletion`, `afterDeletion`, or `effectsPreserved`, despite NOTES claiming every required deletion field is projected;
- `deletionSubsequenceGuard` cannot detect the identity bug because `ActionSubsequence` itself is the permissive relation.

The module is useful but is not the comprehensive regression lock described in `NOTES.md:613-615`.

## Documentation audit

**Files:** `README.md:47-123`; `NOTES.md:551-644`

- The correspondence table does now contain a distinct Lemma-68 row, and Definition 69 correctly distinguishes semantic component totality from the weaker Active-state diagnostic. The finite Progress and no-nested/exact-name Confluence specializations are named. Previously approved Section 3/CP2 rows preserve their proved/partial/stated distinctions; I found no regression in those rows.
- The syntactic status of each open declaration is accurate: it is a statement-only `Type`, not a postulate or exported inhabitant. The recovery, Progress, and constructive sorting debts remain explicitly listed.
- **False overclaim:** README `118-120` and NOTES `589-599,624-626` describe reachability as the essential repaired support premise and classify Lemmas 68/70 as valid statements with proof debt. The checked direct-child, reuse, and retired-parent/open-child traces show both propositions remain false.
- **False overclaim:** README `122` says Lemma 72 is “faithfully stated” with exact deletion. `ActionSubsequence` admits the generic unchanged trace, `NoRegisteredEpisode` ignores open episodes, and final-state-only dependent lookup is weaker than the paper hypothesis.
- **False overclaim:** README `123`, CP3 comments, and NOTES `565-570,627-628` say Theorem 73's canonical package is faithful. All combined-order/block fields are now present, but all-root orchestration placement is not.
- NOTES `608` says the trivial old `DeletionResult` was removed and `613-615` says every required regression field is projected. The generic identity inhabitant and missing statement-check projections refute both claims.
- The final `## Status` is mechanically accurate about which aliases have inhabitants, but not semantically truthful: false/trivial CP3 statements are labeled faithful/precise and their defects are classified as proof debt only. There are therefore still CP3 “exact”/“faithful” overclaims.

## Clean archive build, runtime aggregates, and scans

- `idris2 --version`: **Idris 2 0.8.0**.
- Fresh `git archive 4a0f411` at `/tmp/dgamma-cp3-round2-clean.cG1avm`; `idris2 --clean dgamma.ipkg && idris2 --build dgamma.ipkg`: **passed, 12/12** package modules rebuilt.
- Submitted runtime runner: all eleven individual `CalculusChecks` flags plus `allRuleChecks` evaluated to:

  ```text
  [True, True, True, True, True, True, True, True, True, True, True, True]
  ```

- All 12 packaged modules contain exactly one `%default total`.
- Anchored scans found no source use of `believe_me`, `assert_total`, postulates, `%unsafe`, unsafe IO/FFI, `%default partial`, `partial`/`covering` declaration, or named metavariable hole. Search mentions in README/NOTES are explanatory prose only.
- There are 11 source `TODO(proof)` declaration sites (three Unified, three Metatheory, five CP3), plus four README/NOTES references: 15 textual hits total. No TODO is accepted by Idris as an inhabitant.
- `git diff --check` and the untracked-report whitespace check passed. No staged files exist. The pre-existing `paper/` directory and this requested report are the only untracked repository paths.

## Probe evidence summary

All probe sources remained outside the repository.

| Probe | Result | Evidence |
|---|---:|---|
| Round-1 `SupportCountermodel` unchanged at HEAD | rejected as intended | first mismatch is exactly old `PrecedenceAcyclic` argument versus new `ReachedFromEmpty` premise |
| `ReachableSupportRuntime` | passed | checked 19-step remove/reuse/reinsert trace; mixed cycle final flags all premises true, support empty, both Active |
| `ReachableSupportEvidence` | passed | exact indexed checked trace, `ReachedFromEmpty`, and `SupportPath 1 1` packaged for one dynamic final; six evidence/runtime checks true |
| `ReachableSupportDirectRuntime` | passed | no-reuse direct child insertion reaches the same quiet mixed cycle |
| `OpenRegisteredEpisodeRuntime` | passed | quiet final has retired Inactive parent, unretired Active child, and empty support |
| `ComponentTotalityProbe` | passed | total inhabitants for semantic Definition 69 on provider and consumer components |
| `DeletionIdentityCountermodel` | passed | generic total identity `DeletionResult ... episode []` for every located closed episode |
| `ControlReconciliationProbe` | passed | full Equation-53 control relation inhabited at submitted reconciliation endpoint |
| clean aggregate runner | passed | twelve submitted runtime values all `True` |

## Per-round-1-finding disposition

| Round-1 finding | Disposition | Round-2 judgment |
|---|---|---|
| BLOCKER: Lemma 70 omitted reached-state/support-well-foundedness | **REOPENED / FAIL** | Old arbitrary snapshot is guarded, but checked direct-child, name-reuse, and retired-parent traces satisfy reachability and still refute Lemma 68 and/or Lemma 70. |
| BLOCKER: canonical package omitted combined parent order, uniqueness, exact blocks, and full control | **PARTIALLY FIXED / FAIL** | Unique combined transitive order, ordered contiguous one-block-per-supported-fiber, coverage, and full control now pass. All orchestration steps at orchestrator-inserted roots are still not required before lifecycle steps. |
| MAJOR: Definition 69 was a current Active-state check | **DEFINITION FIXED; THEOREM QUANTIFICATION INCOMPLETE** | `ProgramFinishes` / `ComponentTotalOnProvision` now state semantic component-level totality and typed witnesses are non-vacuous, but Lemma 72/Thm 73 apply it only to final-registry components, not all trace components. |
| MAJOR: `DeletionResult` was unchanged-trace trivial | **NOT FIXED / BLOCKER** | New segment split still keeps every action because `KeepAction` is unconditional; generic identity inhabitant exists for R=[]; hypotheses also omit open registered episodes. |
| MAJOR: Lemma 68 statement/row absent | **DECLARATION ADDED, SEMANTICS FAIL** | Independent row and alias exist, but `ReachedFromEmpty` is insufficient and the alias is false. |
| Documentation called defective CP3 types exact/faithful | **NOT FIXED** | Lemma 68 row and specializations were added, but README/NOTES now overclaim the false/trivial repaired types. |

Ordering/Theorem 63 remains the accepted round-1 pass and was not re-audited, as instructed.

## Whole-project final debt summary

### Previously declared/pre-approved proof or representation debt

- Definition 32 remains an explicit finite context-tower approximation; Lemma 38 is a partial relational transport core.
- Lemma 35 and Theorems 40/42 remain precisely stated and unproved.
- Finite static-list iterators, host-level rather than nested registration, trace-anchored full-effect monoids, exact full-effect equality, and dictionary alignment remain declared calculus specializations/deviations.
- Theorem 61, Corollary 62, and recovery-combined Theorem 64 still need the temporal actual-accumulator induction.
- Progress/Theorem 66 still needs unloading-chain no-deadlock and the Equation-61 ranked count proof.
- Lemma 71 still supplies only the effect commutation projection; control applicability frames are open. Lemmas 54-57 are not fully packaged individually.
- Constructive deletion/canonical sorting and hence Confluence remain unproved even after their statements are repaired.

### New blocking statement/design debt from this final review

1. Separate external root orchestration from accumulator-linked child registration, or carry explicit registration provenance. External `OInsert ChildOf` is not a valid substitute for paper Definition 47.
2. Repair Lemma 68 against direct child insertion and removal/name reuse: generation-stamped live identities, a genuine registration-order invariant, restricted O-Insert, or an explicit `SupportWellFounded` premise is required.
3. Repair Lemma 70's parent clause: a child must be retired by the parent accumulator, or the theorem must assume that property directly.
4. Replace permissive `ActionSubsequence` with an exact deletion/filter relation; forbid both closed and open episodes of R; state dependent closing against the relevant episode/name generation rather than only the final registry.
5. Quantify Definition-69 totality over every component/name generation occurring in each global trace, not only the endpoint registries.
6. Extend canonical input placement to every orchestration step at every orchestrator-inserted fiber, including unsupported roots and O-Retire/O-Remove.
7. Strengthen `CP3StatementChecks` to project Lemma-68 conclusions, block order, all three deletion segments, and effect recovery; then correct README/NOTES and `## Status`.

## Final findings

1. **BLOCKER — `src/DGamma/CP3.idr:126-247,1129-1144`:** `ReachedFromEmpty` does not make combined support well founded. Checked direct-child and name-reuse traces yield an acyclic-precedence mixed `SupportPath` cycle; a second checked trace yields a quiet unsupported Active child after parent retirement. Lemmas 68 and 70 remain false.
2. **BLOCKER — `src/DGamma/CP3.idr:1162-1190,1273-1306`:** `DeletionResult` is still identity-inhabitable. A total generic probe keeps every action for R=[] and inhabits the result for every located closed episode.
3. **BLOCKER — `src/DGamma/CP3.idr:1221-1243,1327-1380`:** Lemma-72/Confluence hypotheses are weaker than the paper: open R episodes are allowed, dependent closing is checked only in the final registry, explicit child insertion has no accumulator-retirement provenance, and totality quantifies only final-registry components rather than every component in the trace.
4. **BLOCKER — `src/DGamma/CP3.idr:1056-1118`:** canonical order/blocks are repaired, but input placement quantifies only supported-root O-Insert actions, not every root orchestration step required by paper Theorem 73(1); the full-domain endpoint also cannot express nonempty withdrawn-name sets admitted elsewhere.
5. **MAJOR — `src/DGamma/CP3StatementChecks.idr:29-35,37-132`:** the Lemma-68 guard is identity and checks omit block order, two deletion segments, and effect recovery.
6. **MAJOR — `README.md:118-123`; `NOTES.md:551-570,584-628`:** false/trivial CP3 statement types are called repaired, exact, and faithful; final status is not truthful.
7. **VERIFIED — `src/DGamma/CP3.idr:269-293`:** Definition 69 is now a genuine semantic component property; non-vacuous submitted component witnesses typecheck.
8. **VERIFIED — `src/DGamma/CP3.idr:591-833`:** Equation-53 control equivalence retains domain, component/spec/program, parent, retirement, full lifecycle payload, and pointwise accumulators; its stronger exact specialization is satisfiable on reconciliation.
9. **VERIFIED — `src/DGamma/CP3.idr:910-1054,1089-1118`:** Equation-62 combined transitive ordering, uniqueness, per-supported-fiber contiguous open blocks, block order, and lifecycle coverage are substantively encoded.
10. **VERIFIED — build/runtime/totality:** clean archive 12/12; all twelve submitted runtime aggregate values true; no escape hatch, partial module, or named hole.

# Final verdict: REJECT

```acceptance-report
{
  "criteriaSatisfied": [
    {
      "id": "criterion-1",
      "status": "satisfied",
      "evidence": "Concrete BLOCKER/MAJOR findings cite DGamma.CP3, DGamma.CP3StatementChecks, README, and NOTES; typed reachable-support, semantic-totality, identity-deletion, and reconciliation-control probes plus clean build/scans are recorded."
    }
  ],
  "changedFiles": [
    "review-cp3-round2.md"
  ],
  "testsAddedOrUpdated": [],
  "commandsRun": [
    {
      "command": "idris2 --source-dir src --check src/SupportCountermodelRound1.idr",
      "result": "failed",
      "summary": "Expected rejection: the old mixedAcyclic argument mismatches the new ReachedFromEmpty premise exactly."
    },
    {
      "command": "idris2 --source-dir src -o reachable-support-evidence src/ReachableSupportEvidence.idr && ./build/exec/reachable-support-evidence",
      "result": "passed",
      "summary": "Printed six True values; packaged an indexed checked trace, ReachedFromEmpty, and combined SupportPath cycle for one dynamic final."
    },
    {
      "command": "reachable support runtime variants",
      "result": "passed",
      "summary": "Remove/reuse/reinsert, direct-child, and retired-parent/open-child checked traces all reached the reported counterexample finals."
    },
    {
      "command": "idris2 --source-dir src -o component-totality-probe src/ComponentTotalityProbe.idr && ./build/exec/component-totality-probe",
      "result": "passed",
      "summary": "Constructed semantic ComponentTotalOnProvision inhabitants for both submitted counterexample components."
    },
    {
      "command": "idris2 --source-dir src -o deletion-identity-countermodel src/DeletionIdentityCountermodel.idr && ./build/exec/deletion-identity-countermodel",
      "result": "passed",
      "summary": "Generic unchanged-trace DeletionResult for R=[] typechecked and ran."
    },
    {
      "command": "idris2 --source-dir src -o control-reconciliation-probe src/ControlReconciliationProbe.idr && ./build/exec/control-reconciliation-probe",
      "result": "passed",
      "summary": "Constructed the full control relation at the submitted reconciliation endpoint; printed True."
    },
    {
      "command": "git archive 4a0f411 | tar -x ... && idris2 --clean dgamma.ipkg && idris2 --build dgamma.ipkg",
      "result": "passed",
      "summary": "Fresh archive rebuilt all 12 packaged modules under Idris 2 0.8.0."
    },
    {
      "command": "idris2 --source-dir src -o cp3-eval-runner src/CP3EvalRunner.idr && ./build/exec/cp3-eval-runner",
      "result": "passed",
      "summary": "All eleven individual submitted runtime flags plus allRuleChecks evaluated True."
    },
    {
      "command": "anchored escape-hatch, hole, partiality, TODO(proof), module, and %default total scans",
      "result": "passed",
      "summary": "No source escape hatch/named hole/partial declaration; 11 explicit source TODO sites; all 12 modules total."
    },
    {
      "command": "git diff --check; untracked report whitespace check; git diff --cached --name-only; git status --short",
      "result": "passed",
      "summary": "No whitespace errors or staged files; only pre-existing paper/ and requested review report are untracked."
    }
  ],
  "validationOutput": [
    "Clean archive build: passed, 12/12 modules.",
    "Submitted runtime checks: [True, True, True, True, True, True, True, True, True, True, True, True].",
    "Reachable exact reach/cycle package: [True, True, True, True, True, True].",
    "Direct child mixed cycle: [True, True, True, True, False, False, True, True].",
    "Retired parent/open child: [True, True, True, True, True, False, False].",
    "Generic identity DeletionResult: typechecked and ran.",
    "Reconciliation full control relation: True."
  ],
  "residualRisks": [
    "False Lemma-68 and Lemma-70 aliases remain due unrestricted explicit child insertion, parent-registration provenance loss, and name reuse.",
    "Lemma 72 remains trivially identity-inhabitable and omits open registered episodes/relevant-time dependency tracking.",
    "CanonicalSchedule still omits all-root-orchestration placement from Theorem 73(1).",
    "README/NOTES describe the above statement defects as repaired proof debt.",
    "Pre-approved temporal recovery, Progress induction, and constructive Confluence proofs remain open."
  ],
  "noStagedFiles": true,
  "diffSummary": "Review-only: added review-cp3-round2.md; no Idris source, package, README, NOTES, or tracked test file edited and no commit.",
  "reviewFindings": [
    "blocker: src/DGamma/CP3.idr:126-247,1129-1144 - checked reachable direct-child/name-reuse/parent-retirement traces refute Lemmas 68 and 70 despite ReachedFromEmpty.",
    "blocker: src/DGamma/CP3.idr:1162-1190,1273-1306 - permissive ActionSubsequence makes DeletionResult generically identity-inhabitable for R=[].",
    "blocker: src/DGamma/CP3.idr:1221-1243,1327-1380 - Lemma-72/Confluence omit open registered episodes, use final-state dependency edges, and quantify totality only over final registries.",
    "blocker: src/DGamma/CP3.idr:1056-1118 - CanonicalInputPlacement omits non-insert root orchestration steps/unsupported roots, and the endpoint cannot express admitted withdrawn names.",
    "major: src/DGamma/CP3StatementChecks.idr:29-132 - Lemma-68 check is identity and several claimed projections are absent.",
    "major: README.md:118-123; NOTES.md:551-628 - false/trivial CP3 statements are called exact/faithful/repaired.",
    "verified: src/DGamma/CP3.idr:269-293,591-833,910-1054 - Definition 69, full control relation, and repaired combined-order/block fields are substantive."
  ],
  "manualNotes": "Final project-review verdict: REJECT. Ordering remains accepted and was not re-audited; declared proof debts are not the reason for rejection—the remaining statement types are false, trivial, or incomplete."
}
```
