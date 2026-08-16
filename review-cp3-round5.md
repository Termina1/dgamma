# Checkpoint 3 adversarial review — round 5 (intended closing round)

**Target:** `2798ee5c1c0335e5ef272638ad24c693eb935f65` (`repair CP3 nested registration nonvacuity`)
**Scope:** paper Section 4.4; all round-4 repairs and historical CP3 countermodel families; full-premise non-vacuity; whole-project documentation/build/escape-hatch audit
**Mode:** review only. No Idris source, package, README, NOTES, or tracked test is edited; probe sources remain under `/tmp`. This report is the sole review artifact.

## Baseline and incremental log

- Confirmed exact requested HEAD `2798ee5`.
- Pre-review tracked tree is clean; `paper/` is the only pre-existing untracked path.
- Read `review-cp3-round1.md` through `review-cp3-round4.md` in full first.
- Read paper Section 4.4, including Equation 53, Lemmas 56/68/70–72, Equation 62, and Theorem 73.
- `idris2 --version`: **Idris 2 0.8.0**.
- Fresh `git archive 2798ee5` at `/tmp/dgamma-cp3-round5.HEcUH5`; `idris2 --clean dgamma.ipkg && idris2 --build dgamma.ipkg`: **passed, 12/12 modules**.

Further adversarial results will be appended incrementally.

### Round-4 vacuity repair and full-premise non-vacuity

Review-only typed probes now establish all of the following.

- `CP3StatementChecks.positiveParentRegistrationYield` is compiled as package module 10/12 and its concrete fields were independently reconstructed in `Round5PositiveProbe.idr`: nonempty parent program `[step]`, current `Reloading [step]`, `Elem ... Here`, deterministic tag/catalog, ranks `0 < 1`, and child component all elaborate. This is a genuine child-yield inhabitant, not a projection from an assumed witness.
- The old empty-parent construction in `EmptyParentExpectedFailure.idr` is rejected before any rank reasoning: its attempted nonempty `sourceStep :: sourceContinuation` cannot equal `Reloading []`. Independently, submitted `emptyParentCannotRegisterGuard` typechecks and eliminates a hypothetical witness from `sourceBelongsToProgram : Elem step []`.
- `Elem` does **not** over-restrict duplicate programs: the probe constructs a parent program `[step, step]`, a first-stage yield whose membership proof is deliberately `There Here`, and a second-stage `Reloading [step]` yield. Both typecheck.
- The explicit-host model also admits repeated use of one still-live tagged head: a checked trace `O-Insert parent; L-Begin parent; O-Insert child1; O-Insert child2` and its complete `RegistrationDiscipline` inhabitant typecheck; all four checked evaluator calls print `True`. This is permissive (one source occurrence can license multiple names) rather than vacuous.
- A checked six-action nested trace `O-Insert parent; L-Begin parent; O-Insert child; L-Finish parent; L-Begin child; L-Finish child` supplies the **full Lemma-70 premise chain**: `ReachedFromEmpty`, aligned checked trace, `RegistrationDiscipline`, precedence acyclicity, quiet/no-failure endpoint, and semantic endpoint component totality. `lemma70FullPremises` applies any inhabitant of the exact submitted theorem alias to those premises. The same trace constructs a real `LocatedOpenEpisodeBlock` whose parent body is `[O-Insert child, L-Finish parent]`, with `ActorYieldedRegistrationStep`, installedness, and no-earlier/no-later lifecycle witnesses. Thus the round-4 actor-only canonical-block incompatibility is repaired substantively.
- A separate checked root trace `O-Insert; L-Begin; L-Finish; O-Retire; L-Leave; L-Unload` supplies the **full Lemma-72 premise chain**: aligned empty-start trace, registration discipline, well-formed start, quiet/no-failure final, all-trace semantic totality, a genuine `TraceIndependent` witness (the `Unit` name type makes distinct actors impossible), located closed episode, exact empty `R`, no dependent closing episode, and no registered episode. `lemma72FullPremises` applies the submitted theorem alias to every argument and obtains its exact `DeletionResult` type.
- That same nonempty trace, paired with itself, supplies the **full Theorem-73 premise chain**: both aligned/discipline/quiet/no-failure/totality/independence sides plus a real `SameExternalOrchestration`, identity generated-name bijection, and ordinal-inverse registration correspondence. `theorem73FullPremises` applies the exact `confluenceTheorem` alias and reaches its exact `ConfluenceResult` type. No premise conjunct of Lemma 70, Lemma 72, or Theorem 73 is globally impossible.
- Replaying the round-2 generic identity deletion definition unchanged fails exactly at `KeepAction`'s `Not (deletable (transitionAction transition))` argument: Idris reports equality `?x = ?x` versus the required function to `Void`. This is the intended structural rejection, with no earlier mismatch.

These probes are under `/tmp/dgamma-cp3-round5.HEcUH5/src` only.

### Historical countermodel replay (incremental)

**Round-2 direct-child support probe — rejected at the intended source-phase conjunct.** Reconstructed `DirectChildExpectedFailure.idr` under `/tmp/dgamma-cp3-r5-cont/archive/src` with the old inactive parent, a real nonempty tagged program, and every later catalog/rank equality supplied. `idris2 --check` fails exactly at `MkParentRegistrationYield`'s `parentAtYield` proof: the required `fiberLifecycle parentFiber = Reloading [step] id EmptyView` reduces to `Inactive Nothing = Reloading ...`. Thus this old reachable mixed-cycle family cannot satisfy `RegistrationStepProvenance`/`RegistrationDiscipline`; it is rejected specifically by the live parent-`Reloading` premise, not by an empty program, lookup, catalog, or evaluator mismatch.

**Round-2 remove/reissue support probe — rejected at the intended strict-rank conjunct.** `NameReuseRankProbe.idr` reconstructs the decisive final incarnation of the old checked trace: the reissued provider is yielded as a child of the consumer, while the consumer depends on a key provided by that child. Assuming every other source/catalog/rank/provision/dependency conjunct, `yieldedRankIncreases` gives `rank(consumer) < rank(provider)` and `precedenceRankIncreases` gives `rank(provider) < rank(consumer)`; the total probe composes them to `LT rank(consumer) rank(consumer)` and eliminates it with `succNotLTEpred`. It typechecks at HEAD. Therefore paper-permitted raw-name remove/reissue is not rejected merely for reusing the name (global `NoLaterInsertion` is gone); this historical support countermodel is rejected exactly because the final parent-plus-precedence cycle cannot satisfy the shared protocol's two strict-rank laws.

**Round-2 retired-parent/open-child support probe — rejected at the intended inverse-retirement conjunct.** `RetiredParentProvenanceProbe.idr` replays the decisive checked suffix shape after child insertion: parent L-Finish, parent O-Retire, then parent L-Leave, with no O-Retire for the distinct child. Its total eliminator covers both constructors of `ChildRetirementProvenance`. `ParentDoesNotRecover` contradicts `ParentLeaves` at the exact L-Leave; `ChildRetiredBeforeParent` cannot choose L-Finish or L-Leave as the child's retirement, cannot confuse the distinct parent's O-Retire with the child's, and cannot skip L-Leave because that step is the first recovery boundary. The probe typechecks. Thus the old quiet unsupported-live-child endpoint is rejected specifically at `ChildRetirementProvenance` in the child O-Insert's `RegistrationStepDiscipline`, not at reachability, phase, source membership, or operational applicability.

**Round-3 cross-subtree disciplined support probe — rejected at the intended protocol-rank conjunct.** `CrossSubtreeRankProbe.idr` assumes every old A/C/B/D source-program membership, deterministic tag/catalog equality, component-rank equality, and provision/dependency membership. The two yielded child edges force `rank(A) < rank(C)` and `rank(B) < rank(D)`; the two precedence edges force `rank(C) < rank(B)` and `rank(D) < rank(A)`. The total probe composes all four to irreflexive `LT rank(A) rank(A)` and typechecks. Hence the historical checked timing/retirement-disciplined cycle still cannot inhabit the current `RegistrationProvenance`/`RegistrationDiscipline`: its exact failing conjunction is the shared `RegistrationProtocol`'s strict yielded-plus-precedence rank laws, not source phase, catalog determinism, freshness, or retirement.

**Round-3 selected-O-Retire deletion probe — rejected at the intended lifecycle-only conjunct.** `RetireDeletionExpectedFailure.idr` attempts the historical deletion evidence for selected `O-Retire` at `R=[]` using the only selected-owner constructor, `DeleteEpisodeLifecycle Refl Refl`. `idris2 --check` rejects the second proof exactly as `True` versus `False`: `isLifecycleAction (ORetire selected)` computes to `False`. There is no `DeleteRegisteredActor` alternative at the empty registered list. Thus exact filtering must keep the external retirement write; the old survivor with `tau=False` cannot be produced by `episodeDeletion`.

**Round-3 fresh-child-name Confluence probe — rejected at the intended occurrence-renaming conjunct.** `ChildRenamingExpectedFailure.idr` asks an identity `RegistrationCorrespondenceByRenaming` to send a left `LocatedGeneratedRegistration 1 0 component` to a right occurrence `2 0`. `idris2 --check` fails exactly when `forwardRegistration` returns the identity-renamed child/root indices rather than child 2. The paired `ChildRenamingSwapProbe.idr` defines the involutive bijection fixing root 0 and swapping 1/2; with that bijection the same `forwardRegistration` projection has exactly the desired `LocatedGeneratedRegistration 2 0 component` type and compiles. Thus the old exact-domain argument cannot reach the theorem: its identity-name choice fails the generated-registration correspondence premise, while the paper Lemma-56 swap is admitted and the conclusion is `SystemEquivalentByRenaming`, not exact-name `SystemEquivalent`.

### Faithfulness adjudication (incremental)

**Nested-registration source/rank and multi-license — sound conservative repair, with a documented-model caveat rather than a countermodel.** Paper Definition 47 makes one application/iteration registration primitive draw one fresh name; `ParentRegistrationYield.parentAtYield` plus `sourceBelongsToProgram : Elem sourceStep parentProgram` is therefore an honest finite-list witness that the explicit host O-Insert is attached to a real current iterator stage. The separate component rank is not a rule printed by the paper and is stronger than Lemma 68's attempted dynamic argument; `NOTES.md:93-119` accurately declares it an explicit host representation delta necessitated by Erratum #3. The round-5 duplicate and repeated-head witnesses reveal one remaining over-approximation: because O-Insert does not consume the head, one source occurrence/tag can license several fresh names of the same catalogued component. That is not literally one Definition-47 application.

This permissiveness does **not** reopen support cycles under the submitted premises. Every admitted root component has a protocol rank; every yielded parent edge strictly raises that rank; every precedence edge strictly raises it; and `SupportPath` is generated solely by those two edge kinds. Multiple names licensed by one source all carry the same child component/rank, so duplicating the target vertex cannot reverse or flatten an edge. Any alleged cycle, including one using two such names, still composes strict rank increases to `LT r r`; `NameReuseRankProbe.idr` and `CrossSubtreeRankProbe.idr` are the two- and four-edge typed instances. The same discipline separately demands an O-Retire for each generated child before parent recovery. Therefore multi-license is semantically permissive relative to the paper's iterator multiplicity, but not an unsound Lemma-68/70 premise and not a blocker. Residual documentation risk: README/NOTES disclose finite explicit tagged registration generally but do not call out this one-head/many-name over-approximation explicitly.

**BLOCKER — role-changing raw-name reissue makes `CanonicalSchedule` false for an admitted quiet trace.** The round-4 change from fixing every historical external name to fixing only live endpoint roots removes one over-restriction in the cross-trace bijection, but it does not compose with Theorem 73's canonical root-input placement. `RoleChangingRuntimeProbe.idr` executes the checked trace

```text
O-Insert 0 Root parent; L-Begin 0;
O-Insert 1 (ChildOf 0) child; O-Retire 1; O-Remove 1;
O-Insert 1 Root child; L-Finish 0; L-Begin 1; L-Finish 1
```

and prints `True` for well-formedness, quiet, success, support/Active status of both final roots, and final `parent(1)=Root`. `RoleChangingTypedProbe.idr` independently compiles exact indexed states/transitions for all nine actions, `AlignedTransitions`, the concrete tagged/ranked `RegistrationProtocol`, the complete `RegistrationDiscipline` (the child retirement is immediate in the insertion suffix), all-trace Definition-69 totality, and definitional final quiet/no-failure proofs. Empty keys, Unit world, and identity steps make independence semantically trivial; self-comparison supplies the identity occurrence bijection and the same external projection.

Yet no `CanonicalSchedule ... trace` can satisfy its fields. The original child occurrence at raw name 1 must be handled by `originalRegistrationAccounted`. It cannot take the withdrawn branch: `endpointNamesWithdrawn` would require final name 1 vestigial or absent, while the original final has a present unretired Active root. It therefore must survive as an exact `LocatedGeneratedRegistration 1 0 child` in the canonical trace. `canonicalRegistrationDiscipline` forces a parent L-Begin before that child insertion. Meanwhile `sameInputs` retains the later external `O-Insert 1 Root child`, and `allRootInputsFirst` forces that root insertion before every lifecycle step, hence before the parent's L-Begin and child insertion. Freshness then forbids the surviving child insertion unless the root incarnation is retired/removed first. Such retirement/removal after L-Begin violates `allRootInputsFirst`; before L-Begin it is classified as root orchestration, but the original O-Retire/O-Remove happened while name 1 was a child and is internal, so `SameExternalOrchestration` cannot add the required root actions or a second root insertion. The fields are jointly inconsistent.

This is precisely the child-to-later-live-root reissue order; the reverse external-to-later-child order does not have this canonical-placement conflict. Paper Lemma 56 speaks about fresh registration generations, while the submitted withdrawal set and canonical occurrence accounting are keyed by raw names. Generation-stamped identities, occurrence-keyed withdrawals, or a theorem premise forbidding role changes across root/generated generations is required. The current README/NOTES claim that legal raw-name reissue is handled occurrence-wise is therefore substantively false for canonicalization.

**`WithdrawnNameResult.NameAlreadyAbsent` is faithful, not a weakening of Lemma 72.** At the selected episode's close, Definition 47 makes each R entry vestigial in the original and absent in the replay. Paper Lemma 72 then carries the suffix; it explicitly discusses later original O-Retire/O-Remove steps owned by R and deletes their replay counterparts because the survivor has no such fiber. After an original O-Remove, the correct endpoint pair for that name is absent/absent, even though the proof's earlier sentence overstates the invariant as “vestigial ... for every t.” The theorem conclusion requires effect agreement and control agreement only outside R, so it does not require original-final presence. `AlreadyAbsentWithdrawalProbe.idr` constructs `NameAlreadyAbsent Refl Refl` for two empty endpoints and typechecks. The new constructor is therefore the necessary faithful completion of the paper's suffix argument (and arguably repairs a minor proof-wording slip), not a trivializing alternative: it still requires absence at both endpoints.

### Final Lemma-72 / Equation-53 / Equation-62 / Theorem-73 field audit

**Lemma 72 (`src/DGamma/CP3.idr:1894-2067`) — field-complete modulo the already-declared explicit-host specialization; no additional false/trivial result found.** `ActionSubsequence` is now exact in both directions (`KeepAction` requires `Not deletable`, `DeleteAction` requires deletable) on all before/episode/after segments. `EpisodeDeletedActor` deletes selected lifecycle only, which is the necessary Erratum-4 proof-intent reading, and all R-owned actions. `RegisteredNamesDuring` is bidirectional and requires each insertion's later inverse retirement in the selected closed interval; `NoRegisteredEpisode` excludes open as well as closed R episodes; `NoDependentClosingEpisode` evaluates the selected precedence edge at each candidate consumer episode start; `TraceComponentsTotal` covers every inserted component occurrence; and discipline/independence/empty-start/quiet/success premises are explicit. The result names the selected episode and R, returns an actually checked surviving trace, exact effect recovery, complete Equation-53 control agreement outside R, and both faithful withdrawal endpoint alternatives. Identity/partial keep and selected-O-Retire attacks are structurally excluded. The raw-name formulation conservatively rejects some later-reissue episodes and may delete a later same-raw-name dormant generation; that is the same generation-model limitation exposed by the canonical blocker, not a separate false Lemma-72 conclusion.

**Equation 53 (`CP3.idr:925-1286` and renaming at `1155-1286`) — complete stronger specialization.** Domain is preserved by the `Maybe` relation; the shared component index retains `d,p,e` and the complete finite program; parent and retirement have explicit equalities/renamed relations; all lifecycle variants retain outcome, remaining iterator, accumulator pointwise, and committed view; effect tables are compared at every name/key and ambient state exactly. `SystemEquivalentByRenaming` transports domain, parent/view names, every control payload, tables, and ambient world through one genuine bijection. Exact function/list/effect equality is stronger than the paper's observational relation but is the consistently declared finite exact specialization and is inhabited by the round-5 full-premise trace.

**Equation 62 / canonical blocks (`CP3.idr:1290-1477,1771-1848`) — complete apart from raw-generation collision.** `LinearizesSupport` is duplicate-free, sound/complete for A, and orders every transitive `SupportPath` combining immediate parent and precedence edges. Each supported name gets one located final open episode with exact decomposition, installed body, no earlier/later lifecycle, final Active status, and a body allowing only own lifecycle plus own yielded child insertions. `blocksFollowOrder` fixes global block order; coverage excludes lifecycle history outside A. Every live root O-Insert/O-Retire/O-Remove precedes every lifecycle transition; each supported child insertion precedes all its lifecycle actions. Canonical endpoint withdrawals, effects, outside-R controls, and registration-occurrence accounting are explicit. No earlier round-1/2 packaging omission remains.

**Theorem 73 result (`CP3.idr:1600-1848,2069-2120`) — endpoint/correspondence packaging is otherwise substantive, but the raw-name role-changing blocker is decisive.** External root actions match in exact order. Generated registrations are located by dependent prefixes, mapped both ways under parent/component-preserving renaming, and ordinal inverse laws enforce occurrence multiplicity rather than mere existence. `ConfluenceResult` contains both canonical forms, the final occurrence correspondence, and direct full endpoint equivalence by renaming; it does not derive the endpoint through a tautological canonical-final equality. The extra `SameOrchestrationModuloGenerated` tree witness is a documented stronger host premise compensating for registration not being returned by `runStepEffect`. However, `CanonicalRegistrationCorrespondence` accounts/withdraws by raw child name while root placement classifies the current incarnation; the admitted child-to-live-root reissue trace above makes those otherwise valid fields inconsistent. That remaining gap makes the statement false in substance and is a final blocker.

### Whole-project documentation audit

**The 70-row README table is truthful for Sections 3, CP2, Ordering, and declared proof status.** Section 3.1's 22 rows retain the approved executable/proved claims, including every-intermediate Theorems 16/20 and arbitrary adjacent-swap Corollary 21. Section 3.2's 10 rows explicitly say the isolation/interception tokens prove table projections rather than full-context equality. Section 3.3 does not disguise debt: Definition 32 is a finite approximation/deviation, Lemma 38 only a relational core, and Lemma 35/Theorems 40/42 are stated unproved. Section 4 correctly distinguishes raw Preservation and Ordering as proved, Theorem 64 as conditional on terminal recovery, Theorem 61/Corollary 62 and Progress as stated/partial, Definition 69 as component-semantic/all-trace, and Lemmas 54–57 as not individually packaged. All paper rows have a corresponding status; no proved/stated swap or missing specialization was found outside CP3.

**The three historically critical errata/deviations are recorded precisely.** `NOTES.md:45-54` explains why Definition 32's negative occurrence is not an Idris inductive fixed point and refuses a literal claim. `NOTES.md:451-486` records the composite-accumulator independence countermodel and the per-yield/reachable-continuation generated-monoid repair; README Definition 60 reflects the repaired full generator set rather than the old composite premise. `NOTES.md:93-119` quotes the invalid Lemma-68 nested-registration step, distinguishes the printed O-Insert rule from yielded provenance, records all three old reachable attacks and the cross-subtree phase-only failure, and labels tags/catalog/ranks as an explicit host delta rather than a paper rule. Erratum #4's selected-retirement ambiguity is also accurately documented. The finite iterator, exact full-effect equality, dictionary alignment, and partial coeffect undo specializations are disclosed.

**BLOCKER documentation consequence — `README.md:123`, `NOTES.md:114-119,608-618,683-693,716-722`.** README says occurrence/ordinal correspondence works “across legal reissue” and that only live root generations need be fixed. The role-changing trace proves the canonical package does not handle all paper-legal reissue: occurrence correspondence itself survives, but raw-name withdrawals/root placement make child-to-later-live-root canonicalization impossible. NOTES similarly says occurrence evidence “handles each birth,” presents live-root fixing as the downstream repair, and lists only constructive deletion/sorting as next work. The cautious “under repair/review” labels are honest about acceptance status, but these concrete semantic claims and the final debt/Next list are now incomplete. README/NOTES also omit the one-head/many-name over-approximation. Documentation cannot be accepted until it records the generation-stamping/role-change restriction or the statement type is repaired; this is a consequence of the substantive blocker, not a cosmetic row-label issue.

**NOTES debt accounting is otherwise precise.** The statement-only list matches the exported bare `Type`s and never calls them postulates; temporal accumulator induction, unloading-chain/count Progress, Lemma-71 control frames, and constructive deletion/canonicalization are separated from proved cores. The final Status correctly distinguishes fully proved, partial, merely stated, and deviations. Its only closing-round defect is failure to include the newly exposed proposition-shape debt and its current “Next” line therefore assumes proof implementation can start before canonical raw-generation repair.

### Final runtime / totality / escape-hatch audit

- Reused the already-recorded fresh `git archive 2798ee5` build result (**12/12 passed**); no drift exists because HEAD remains exactly `2798ee5c1c0335e5ef272638ad24c693eb935f65` and tracked sources are untouched.
- A review-only `Round5AggregateRunner.idr` in `/tmp/dgamma-cp3-r5-cont/archive/src` evaluated the eleven individual `CalculusChecks` regressions plus `allRuleChecks` to `[True, True, True, True, True, True, True, True, True, True, True, True]`.
- All 12 packaged `src/DGamma/*.idr` modules contain exactly one `%default total`.
- Anchored source scans found no `believe_me`, `assert_total`, postulate, `%unsafe`, unsafe FFI/primitive, `%default partial`, `%default covering`, partial/covering declaration, or named metavariable hole.
- There are 11 explicit source `TODO(proof)` declaration sites: three in `Unified`, three in `Metatheory`, and five in `CP3`. README has three correspondence references and NOTES one explanatory reference. No TODO is accepted by Idris as an inhabitant.
- `git diff --check` passed; no staged files exist; the report has no trailing whitespace. Repository status remains the pre-existing untracked `paper/` plus this requested untracked report only. Every probe source/executable is outside the repository under `/tmp`.

## Per-round-4-finding disposition

| Round-4 finding | Round-5 closing disposition |
|---|---|
| `yieldedRankIncreases` made every child yield impossible | **FIXED.** Actual program membership is part of the law; a concrete nonempty yield, empty-parent rejection, duplicate-position witness, and full Lemma-70/73 premise chains are inhabited. |
| Canonical actor-only block excluded child O-Insert | **FIXED for ordinary nested registration.** `ActorYieldedRegistrationStep` admits provenance-linked insertion and a located nonempty canonical block is constructed. **Reopened only for a different issue:** child-to-later-root raw-name reissue makes canonical root placement impossible. |
| Registration correspondence was occurrence-existence, not multiplicity/generation bijection | **Multiplicity fixed.** Located dependent occurrences plus forward/backward ordinal inverses reject identity renaming and admit the 1/2 swap. **Generation identity still incomplete:** withdrawals and root roles remain raw-name keyed, causing the new blocker. |
| `RegisteredNamesWithdrawn` omitted original-absent/absent | **FIXED and faithful.** `NameAlreadyAbsent` typechecks and matches the paper suffix after original O-Remove. |
| Def-47/protocol/tree documentation claims were vacuous or overstated | **Non-vacuity fixed; legal-reissue claim reopened.** Concrete yields/full premises exist, but README/NOTES now overstate support for all legal role-changing reissue and omit multi-license. |
| `CP3StatementChecks` child guards projected an empty domain | **FIXED.** The positive yield is constructed and the key result fields are projected; no regression-guard vacuity remains. |
| Recovery boundary was mislabeled as accumulator execution | **FIXED.** Source and NOTES now say it enters recovery and the accumulator executes later at L-Unload. |
| Fresh-name endpoint renaming and selected O-Retire survival | **REMAIN FIXED.** Historical probes fail exactly at identity occurrence correspondence and lifecycle-only deletion respectively; swap/survival witnesses compile. |
| Clean build/runtime/totality | **PASS.** Existing fresh archive 12/12, twelve runtime `True`, all total, no escape hatch. |

## Whole-project final debt summary

### Honest, previously declared/pre-approved proof or representation debt

- Definition 32 is a finite tower approximation; Lemma 38 is only the proved relational composition/stack core. Lemma 35 and Theorems 40/42 remain precise statement-only Section-3 obligations.
- Section 4 uses finite static-list continuations, explicit tagged/catalogued host registration rather than a recursive nested yield, trace-anchored full-effect monoids, exact effect equality, and explicit dictionary alignment.
- Lemmas 54–57 are represented by many structural fragments but are not individually packaged completely.
- Theorem 61, Corollary 62, and the recovery branch of Theorem 64 still need the actual-accumulator temporal induction.
- Progress/Theorem 66 still needs the unloading-chain no-deadlock proof and Equation-61 ranked count induction.
- Lemma 71 has only its effect commutation projection; applicability/control frames remain open.
- Lemma 72's checked deletion induction and Theorem 73's constructive sorting/endpoint proof remain unimplemented. These missing proofs are not themselves grounds for rejection.

### Closing-round statement/design debt (blocking)

1. Replace raw names in canonical registration accounting/withdrawals with generation-stamped occurrences, or explicitly forbid generated-to-live-root role-changing reissue in Theorem 73's premises. `CanonicalSchedule` is false on the checked disciplined trace recorded above.
2. Update README/NOTES: retract “across legal reissue” until that repair exists, record the role-change restriction/countermodel, and disclose that one live tagged source head may license multiple names in the explicit-host over-approximation.
3. After the proposition shape is repaired, add the role-changing trace as a negative/positive regression and only then proceed to constructive canonicalization.

## Final findings

1. **BLOCKER — `src/DGamma/CP3.idr:1583-1848,2069-2120`:** a checked, aligned, ranked/registration-disciplined, total, quiet successful trace reuses name 1 from withdrawn generated child to live external root. `CanonicalRegistrationCorrespondence` cannot withdraw the live raw name and cannot retain its child occurrence under all-root-before-lifecycle placement. Theorem 73's `CanonicalSchedule` result is false.
2. **MAJOR — `README.md:118-123`; `NOTES.md:114-119,587-618,672-722`:** legal-reissue/occurrence-generation repair claims and the final debt plan omit the blocker; documentation is not truthful at final-project level despite honest “under review” labels.
3. **MINOR / declared-model risk — `src/DGamma/CP3.idr:214-249,363-404`; README Def-47/Lem-68 rows:** one source head/tag can license multiple child names before it is consumed. Strict ranks and per-child retirement keep support sound, but this is more permissive than one paper Definition-47 application and is not explicitly documented.
4. **VERIFIED — historical closure:** direct-child fails at parent Reloading; remove/reissue and cross-subtree cycles fail at strict rank; retired-parent fails at inverse-retirement provenance; selected O-Retire fails at lifecycle-only deletion; identity child renaming fails at occurrence correspondence while the swap succeeds.
5. **VERIFIED — Lemma 72 and remaining packaging:** exact action filtering, lifecycle-only selected deletion, absent/absent withdrawal, full Equation-53 relation, combined Equation-62 linearization, nested canonical blocks, and occurrence multiplicity fields are substantive and non-vacuous.
6. **VERIFIED — project quality:** frozen clean archive build 12/12 (reused), all twelve runtime aggregates true, 12/12 modules `%default total`, no escape hatch/unsafe/partial declaration/named hole, and 11 explicit statement-only TODO sites.

# Final verdict: REJECT

The sole reason acceptance cannot be earned is substantive: the final Theorem-73 statement package is false on paper-legal raw-name role-changing reissue. The declared proof debts remain honest and would otherwise be pre-approved.

```acceptance-report
{
  "criteriaSatisfied": [
    {
      "id": "criterion-1",
      "status": "satisfied",
      "evidence": "Concrete BLOCKER/MAJOR/MINOR findings cite DGamma.CP3, README, and NOTES; exact expected-failure probes, typed ranked/provenance/role-changing traces, runtime evidence, field audits, scans, and residual risks are recorded."
    }
  ],
  "changedFiles": [
    "review-cp3-round5.md"
  ],
  "testsAddedOrUpdated": [],
  "commandsRun": [
    {
      "command": "historical expected-failure probes under /tmp/dgamma-cp3-r5-cont/archive/src",
      "result": "passed",
      "summary": "Direct-child, retirement, selected-O-Retire, identity-renaming, strict-rank remove/reissue, and cross-subtree attacks were rejected at the exact intended conjuncts; swap/absent-withdrawal positives compiled."
    },
    {
      "command": "idris2 --source-dir src --check src/RoleChangingTypedProbe.idr; RoleChangingRuntimeProbe",
      "result": "passed",
      "summary": "Compiled a nine-action indexed aligned RegistrationDiscipline/totality witness and printed True for the quiet supported live-root endpoint exposing the canonical raw-generation conflict."
    },
    {
      "command": "git archive 2798ee5 ... && idris2 --clean dgamma.ipkg && idris2 --build dgamma.ipkg",
      "result": "passed",
      "summary": "Previously recorded immutable fresh archive rebuilt all 12 package modules under Idris 2 0.8.0; not redundantly rerun."
    },
    {
      "command": "idris2 --source-dir src -o round5-aggregate src/Round5AggregateRunner.idr && ./build/exec/round5-aggregate",
      "result": "passed",
      "summary": "Eleven individual CalculusChecks regressions plus allRuleChecks all evaluated True."
    },
    {
      "command": "anchored escape-hatch, unsafe, partiality, metavariable, TODO, module-totality, diff, staged-file, and whitespace scans",
      "result": "passed",
      "summary": "No escape hatch/unsafe/partial/named hole; 11 explicit source TODO sites; all 12 modules total; no staged files or whitespace errors."
    }
  ],
  "validationOutput": [
    "Historical replay: each old countermodel rejected at Reloading, strict-rank, retirement-provenance, lifecycle-only, or renaming-occurrence conjunct as applicable.",
    "Role-changing reissue runtime checks: True; typed 9-step aligned trace, RegistrationDiscipline, totality, quiet, and no-failure witnesses compiled.",
    "Runtime aggregate: [True, True, True, True, True, True, True, True, True, True, True, True].",
    "Fresh frozen-archive build already recorded: 12/12 passed."
  ],
  "residualRisks": [
    "CanonicalSchedule is false for generated-child-to-live-root raw-name reissue; generation-stamped accounting or an explicit restriction is required.",
    "README/NOTES overstate support for legal reissue and omit one-head/many-name host permissiveness.",
    "Temporal recovery, Progress induction, Lemma-71 control frames, and constructive deletion/canonicalization remain explicit pre-approved proof debt."
  ],
  "noStagedFiles": true,
  "diffSummary": "Review-only: appended the closing-round report; no tracked source, documentation, package, or test file edited and no commit.",
  "reviewFindings": [
    "blocker: src/DGamma/CP3.idr:1583-1848,2069-2120 - raw-name role-changing reissue makes CanonicalSchedule/Confluence false.",
    "major: README.md:118-123 and NOTES.md:114-119,587-722 - legal-reissue claims and final debt list omit the new statement blocker.",
    "minor: src/DGamma/CP3.idr:214-249,363-404 - one tagged source occurrence may license multiple names; ranks keep support acyclic but the host deviation is undocumented.",
    "verified: historical support/deletion/renaming attacks are blocked at their intended premises; Lemma-72/Eq-53/Eq-62 fields are otherwise substantive.",
    "verified: clean archive 12/12, twelve runtime checks True, totality and escape-hatch scans clean."
  ],
  "manualNotes": "Final verdict: REJECT. The rejection is for one newly demonstrated false Theorem-73 canonical statement, not for any declared missing proof."
}
```
