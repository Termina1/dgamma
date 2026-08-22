# Theorem 73 (Confluence) — CP5 scoping plan, revision 3

Branch: `cp5-thm73-scoping`

Review trail:

- `review-cp5-plan-round1.md` — REJECT, twelve required changes;
- `review-cp5-plan-round2.md` — REJECT, eight required changes.

Scope remains research-only planning and interface elaboration. Accepted
statements and all files under `src/` are immutable. Hole-bearing modules under
`research/DGamma/` are excluded from `dgamma.ipkg` and must never merge unchanged
to `main`.

## Executive estimate

The provisional budget is now **60–100 engineering shifts**. The revision-2
50–90 band is withdrawn. Round 2 changed the risk profile: generic replay
correspondence looks more structural than first estimated, but cross-trace block
sorting and endpoint composition were missing O/A transposition, a simultaneous
schedule/replay package, full canonical replay premises, and typed links into
the accepted deleted-generation scanner. Two apparently strengthened path
interfaces were actually uninhabitable in accepted vestigial cases and had to be
removed.

This range is still provisional. Re-estimate after these gates have proofs, not
holes:

1. A/A, A/O, **O/A**, and O/O local diamonds plus suffix replay;
2. one complete D72 step returning typed deleted-generation classification and
   the next replay bundle;
3. minimal original/reduced support facts sufficient for schedule assembly in
   every vestigial case;
4. bundle-preserving canonical block permutation; and
5. schedule withdrawal membership in the accepted two-trace scanner followed by
   the four-way vestigial endpoint proof.

The final `MkConfluenceResult` assembly remains checked and small.

## 1. Calibration rule: necessary and inhabitable

Every internal field must pass both tests:

1. **Consumer necessity:** which later constructor or induction step projects
   this exact field?
2. **Producer inhabitability:** can deletion/sorting construct it for every case
   admitted by `CanonicalEndpointRelation` and `CurrentEndpointRenaming`,
   including original-present/reduced-absent and cross-trace vestigials?

Revision 2 failed the second test twice:

- unrestricted `CanonicalSupportTransport.supportPathToReduced` turned a legal
  original parent edge ending at a withdrawn retired child into a reduced path
  ending at an absent fiber;
- unrestricted `MappedCanonicalSupportOrders.mappedSupportPathForward` forced a
  renamed target fiber to exist even when accepted current renaming classifies
  it vestigial/absent.

Revision 3 exposes only the schedule facts actually consumed. Arbitrary paths
through unsupported or vestigial nodes are not transported.

## 2. Revised producer/consumer pipeline

| Producer | Output guaranteed by the interface | Immediate consumer |
|---|---|---|
| Relational action/suffix replay | `RelationalReplayCorrespondence`, mapping every actual/yielded generator and iterator stage with map/outcome preservation | structural correspondence composition and `TraceIndependent` transport |
| Any recursive replay state | `ReplayInvariantBundle`: alignment, discipline, empty/well-formed start, endpoint WF, quiet/no-failure, totality, independence, provenance, ranks, `PrecedenceAcyclic`, `SupportWellFounded`, and `SupportMatchesActive` | next deletion or adjacent swap; Lemmas 68/70 |
| Local A/A, A/O, O/A, or O/O commute | `LocalRelationalDiamond` with action/tag/branch preservation and endpoint quotient | `AdjacentSwapResult` suffix replay |
| One D72 iteration | `DeletionChainStep` with replay correspondence, external inputs, exact endpoint/registration accounting, typed `DeletedGenerationClassification` for each withdrawn birth, and next premises | delete-all recursion |
| Delete-all recursion | `ClosingFreeReduction` with a dependent list `(generation ** DeletedGenerationClassification original generation)`, exact endpoint-list equality, registration accounting, and replay capital | shape/order/sorting and one-trace package |
| Support bridge | Minimal `CanonicalSupportTransport`: support truth equality, reduced-linearization→original-linearization, and reduced-placement→original-placement | exact schedule constructor only |
| Closing-free sorting | `SortedClosingFreeTrace` with replay correspondence, full sorted premises, blocks/order/coverage, placement, endpoint, and registration tree | simultaneous one-trace package |
| Deletion + sorting | `OneTraceOrchestrationAccounting` whose endpoint withdrawn list equals the reduction list | simultaneous package |
| Simultaneous one-trace constructor | `IndependentCanonicalSchedule`: public schedule, original/canonical independence, correspondence indexed by `canonicalTrace schedule`, full canonical `ReplayInvariantBundle`, and typed classification for every schedule withdrawal | cross-trace order matching and swaps; accepted-scanner bridge |
| Support-order matching | `MappedCanonicalSupportOrders`: mapped supported membership, mapped left order as a direct `LinearizesSupport` value at the right endpoint, and certified adjacent incomparable swaps | canonical block permutation |
| Bundle-preserving canonical permutation | `CanonicalConvergenceResult` with final replayed trace, replay correspondence, full final bundle, same external inputs, and fixed-bijection canonical endpoint bridge | original endpoint composition |
| Scanner bridge | `AcceptedDeletionScannerCapital`: exact accepted `RegistrationTraceCorrespondence`, left/right schedule-withdrawal membership in `leftDeletedGenerations`/`rightDeletedGenerations`, and original `DeletedClosingRegistration` classifications | four-way `VestigialEndpointGeneration` cases |
| Two enriched schedules + scanner capital + canonical bridge | exact `SystemEquivalentByRenamingModuloVestigial` at the two original finals | checked `ConfluenceResult` constructor |

`composeGenerationBijection`, `composeNameBijection`, and now
`composeRelationalReplayCorrespondence` are complete research proofs.

## 3. Probe-driven corrections

### 3.1 Opaque schedule endpoint reproduced and fixed

Before revision, the round-2 positive attempt failed exactly at:

```text
MkIndependentCanonicalSchedule schedule ... correspondence
Can't solve constraint between sorted.sortedFinal and schedule.canonicalFinal
```

The failure was reproduced against `bde35d8` before edits. The public schedule
returned by an opaque function hid the final/trace used to build the composed
replay correspondence.

Revision 3 moves `IndependentCanonicalSchedule` beside one-trace sorting and
adds the complete `assembleIndependentCanonicalSchedule`. It constructs
`MkCanonicalSchedule` inline with the composed original→reduced→sorted replay
correspondence and `sortedPremises`. This is a fully implemented positive proof,
not a named hole. A separate external probe projecting the simultaneous package
also elaborates.

### 3.2 Vestigial path counterexamples closed by weakening

The fields used by `transportForbidsPermittedVestigialChild` and
`mappedPathsForbidAbsentRenamedTarget` no longer exist. They were not weakened by
adding ad hoc hypotheses; they were removed because no consumer needs an
arbitrary path ending at an unsupported actor.

The corrected positive probe establishes only:

- `linearizationToOriginal` from the minimal support bridge;
- `mappedLeftOrderLinearizesRight` for the actual support list; and
- accepted-scanner membership for a schedule-withdrawn generation.

All three elaborate without asserting endpoint presence for a vestigial name.

### 3.3 O/A orientation

`orchestrationActivationDiamondSpike` now takes a checked early activation,
action/tag equality, O/A branch proofs, actor distinction, child and licensing
parent exclusions, source well-formedness, and independence. An external
positive application elaborates in the formerly missing orientation.

## 4. Proof obligations in dependency order

There remain **23 obligations: O1–O22 proof obligations and O23 validation**.
Grades are S, M, L, XL. They describe risk, not one-shift units.

| ID | Obligation and produced capital | Depends on | Grade and reason |
|---|---|---|---|
| **O1** | Trace/list algebra; external-orchestration reflexivity/transitivity; replay endpoint algebra; proved name/generation/replay-correspondence composition. | accepted CP3/RAR | **M.** Dependent endpoints make routine algebra nontrivial, but shapes are now checked. |
| **O2** | Lift `RelationalReplayCorrespondence` structurally to arbitrary `TraceEffectTransformation` and prove both `TraceIndependent` fields. | O1 | **L.** Round-2 correspondence composition is short and generator/stage maps are explicit; no longer graded XL. |
| **O3** | A/A diamonds for L-Begin and L-Iter/L-Finish with exact moved tags, branches, effects, controls, and early applicability. | O2 | **L–XL.** Tag combinations and failure-aware Advance remain case-heavy. |
| **O4** | Both mixed orientations: A/O and O/A, with early moved-rule applicability, actor/child/parent exclusions, and branch preservation. | O2–O3 | **XL.** O/A is newly scoped and required by whole-block swaps ending in yielded insertion. |
| **O5** | O/O diamonds, particularly yielded O-Insert/O-Insert, with generation scan, freshness, registration positions, and anti-license-cross conditions. | O1–O2 | **XL gate.** A countermodel forces sorting redesign. |
| **O6** | Implement `AdjacentSwapResult` for all four orientations; replay suffix and return same inputs, correspondence, quotient endpoint, and complete next bundle. | O1–O5 | **XL.** Exhaustive RAR replay and invariant reconstruction dominate. |
| **O7** | Executable located closed/open episode scanners, exact begin ordinals, and uniqueness. | GEN | **L.** Finite but heavily indexed under raw-name reuse. |
| **O8** | Select support/parent-maximal close and derive every D72 negative/generation premise. | O7, Lemmas 68/70 | **XL.** Occurrence/generation maximality is not raw-name maximality. |
| **O9** | Enrich one internal D72 call with correspondence, typed `DeletedGenerationClassification` per withdrawn birth, exact registration/endpoint accounting, strict decrease, and next bundle. | O2, O8, D72 | **XL.** Requires internal fold evidence, not a stronger public `DeletionResult`. |
| **O10** | Well-founded delete-all recursion on trace length. | O7–O9 | **L.** Measure is easy; dependent recursion is not. |
| **O11** | Compose deletion results into `ClosingFreeReduction`, preserving dependent typed history and exact endpoint list/accounting. | O1, O9–O10 | **XL.** Classification/ordinal transport across replayed traces is Lemma-72-scale. |
| **O12** | Closing-free shape: one supported open begin ordinal, unsupported lifecycle absence, and elimination of non-paper lifecycle tags. | O7, O11 | **L–XL gate.** Counterexample triggers algorithm/statement review. |
| **O13** | Project/reconstruct Lemma-68/70 capital from each `ReplayInvariantBundle`. | O9 | **S–M.** Round-2 positive projection is complete; remaining work is routine invocation/index plumbing. |
| **O14** | Construct finite duplicate-free support linearization. | O13 | **M–L.** Enumeration and uniqueness are dependent but no cross-endpoint paths are needed. |
| **O15** | Prove minimal `CanonicalSupportTransport`: support truth plus the exact linearization and placement outputs, without unrestricted path transport. | O11, O13–O14 | **L–XL gate.** Must be tested against both `VestigialNameWithdrawn` and `NameAlreadyAbsent`. |
| **O16** | Preserve root input order; place generated births; compose external input and generated-registration accounting with exact withdrawal equality. | O1, O6, O11 | **L–XL.** Root and generated events obey different constraints. |
| **O17** | Sort actor blocks using A/A, A/O, O/A, O/O; every certified step consumes and returns a `ReplayInvariantBundle`; build `SortedClosingFreeTrace`. | O6, O12–O16 | **XL.** Whole-block replay is a major induction. |
| **O18** | Construct `IndependentCanonicalSchedule` simultaneously and project accepted `CanonicalSchedule`. | O11, O15–O17 | **S–M assembly.** The constructor is already fully implemented given the hard classification input; hard accounting stays in O11/O16/O17. |
| **O19** | Prove only supported-order correspondence: mapped membership and a second right-endpoint `LinearizesSupport`, then certified adjacent incomparable permutation. | O14–O18 | **L–XL.** Must reason around unsupported intermediates without mapping them. |
| **O20** | Execute O19 permutation with enriched canonical capitals; each step receives/returns full bundles; produce `CanonicalConvergenceResult`. | O2–O6, O18–O19 | **XL, expanded.** Includes newly explicit bundle threading and O/A replay. |
| **O21** | Build `AcceptedDeletionScannerCapital` from both typed histories and accepted `RegistrationTraceCorrespondence`; prove O21 four-way endpoint cases and exact fixed-bijection original equivalence. | O11, O18, O20 | **XL, expanded.** Scanner membership and vestigial classification are now honestly included. |
| **O22** | Assemble schedules and O21 equivalence into `ConfluenceResult` and inhabit `confluenceTheorem`. | O18, O21 | **S.** Checked constructor already exists. |
| **O23** | Negative vestigial/O-A regressions, sequential spike/package checks, adversarial reviews, docs, and release branch excluding research holes. | O1–O22 | **M–L.** Review gates remain mandatory. |

## 5. Dependency phases and 60–100 budget

These are overlapping critical-path bands; common RAR/scanner infrastructure is
counted once in the total estimate.

| Phase | Obligations | Provisional band |
|---|---|---:|
| A — replay algebra/independence | O1–O2 | 5–9 |
| B — four local orientations and suffix replay | O3–O6 | 10–18 |
| C — scanners, selection, enriched D72 | O7–O9 | 7–13 |
| D — recursion and typed cumulative history | O10–O11 | 8–15 |
| E — shape, support order, minimal support bridge | O12–O15 | 7–13 |
| F — orchestration accounting and block sorting | O16–O18 | 9–16 |
| G — supported mapped order, canonical replay, scanner/O21 | O19–O21 | 12–23 |
| H — outer theorem and validation | O22–O23 | 2–5 |

Plan **60–100 total** after reuse/overlap. Re-estimate after O4, O9, O15,
O20, and O21. Any public statement repair invalidates the band.

## 6. Mathematical gates and architecture decisions

| Gate | Pass criterion | Failure consequence |
|---|---|---|
| **G1 replay independence** | O2 proves both Definition-60 fields from the generic correspondence. | Enrich internal replay further or evaluate a direct canonical evaluator; public premise changes require statement review. |
| **G2 four-way local commute** | A/A, A/O, O/A, O/O cover every adjacent crossing generated by block sorting. | Redesign sorting to avoid the failing crossing; never invert source-sensitive diamonds by assertion. |
| **G3 activation shape** | Closing-free supported blocks contain only L-Begin/L-Iter/L-Finish plus yielded insertions. | Counterexample and canonical algorithm/statement review. |
| **G4 minimal support bridge** | Direct linearization/placement outputs are proved for all accepted withdrawal cases without arbitrary path transport. | Change internal ordering construction; public `CanonicalSchedule` only after counterexample. |
| **G5 scanner-linked endpoint composition** | Every schedule withdrawal maps into accepted left/right deleted scanner sets and closes all vestigial endpoint cases. | Strengthen internal typed scanner history; public endpoint records only after counterexample. |

Actual supervisor decisions arise only after a failed gate: replay Path A versus
direct evaluation; whole-block sorting versus a no-crossing algorithm; further
internal witness enrichment versus public review; and additional budget.
`SameOrchestrationModuloGenerated` remains fixed accepted capital.

## 7. Round-2 required-change closure

| # | Required change | Revision-3 response |
|---:|---|---|
| 1 | Add O/A | Added source-sensitive `orchestrationActivationDiamondSpike`, integrated into O4/O6/O17/O20, and checked a positive external application. |
| 2 | Remove false support paths | `CanonicalSupportTransport` now exposes only support truth, direct linearization, and direct placement. Exact simultaneous schedule assembly still elaborates. |
| 3 | Remove false mapped paths | `MappedCanonicalSupportOrders` now supplies a mapped supported list that directly linearizes the right endpoint plus certified supported incomparable swaps; no arbitrary path map remains. |
| 4 | Exact enriched one-trace producer | Added proved replay correspondence composition, `IndependentCanonicalSchedule` with full bundle/classification, fully implemented simultaneous constructor, and a hole only for deriving hard classification capital. The former opaque mismatch is reproduced and then absent in the positive probe. |
| 5 | Typed deletion classification | Replaced plain history by dependent `DeletedGenerationClassification` values carrying original occurrence, scanner-shaped event, generation equations, and `DeletedClosingRegistration`. |
| 6 | Cross convergence consumes full capitals | Matching/convergence use enriched schedules; `CanonicalConvergenceResult` returns permutation correspondence and final full bundle; O20 explicitly threads `AdjacentSwapResult` bundle per certified step. |
| 7 | O21 scanner links | Added exact `AcceptedDeletionScannerCapital` with `RegistrationTraceCorrespondence`, schedule-withdrawal membership in `leftDeletedGenerations`/`rightDeletedGenerations`, and both closing classifications; O21 consumes it. |
| 8 | Closure/estimate/probes | This matrix replaces revision 2; estimate is 60–100 with O2=L, O13=S–M, O18=S–M, O20/O21 expanded XL. Positive corrected-interface/O-A probes and the original negative vestigial probes are recorded. |

## 8. Retained round-1 closure

The valid revision-2 repairs remain: moved tag/branch payload, generic replay
interface, full `ReplayInvariantBundle`, O/O safety, exact support-state schedule
indices, fixed composed-bijection coupling, external/generated input accounting,
23-obligation count, and mathematical gate framing. Round 3 should verify these
were not regressed while checking the new weakenings.

## 9. Validation and release boundary

Before authorization, external round-3 review must verify:

- the old contradiction probes cannot be reconstructed from corrected fields;
- the simultaneous package positive proof really shares schedule/replay/bundle
  indices;
- O/A conditions suffice for yielded-registration whole-block crossings;
- every cross-trace operational swap starts with and returns a full bundle;
- typed one-trace withdrawals reach the accepted scanner deleted lists; and
- O21 remains fixed to the accepted current-name bijection.

All five spikes must elaborate one Idris process at a time against an exact copy
of release `src/`. Release `dgamma.ipkg` must remain unaware of research modules.
An eventual proof implementation must recreate the accepted interfaces as total,
hole-free `src/DGamma/CP5*` modules and pass adversarial review, package build,
escape scans, and documentation gates. Theorem 73 remains unproved after this
scoping revision by design.
