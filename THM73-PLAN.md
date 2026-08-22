# Theorem 73 (Confluence) — CP5 scoping plan, revision 4

Branch: `cp5-thm73-scoping`

Review trail:

- `review-cp5-plan-round1.md` — REJECT, twelve required changes;
- `review-cp5-plan-round2.md` — REJECT, eight required changes;
- `review-cp5-plan-round3.md` — REJECT, two localized blockers, two majors,
  and one minor.

Scope remains research-only planning and interface elaboration. Accepted
statements and every file under `src/` are immutable. Hole-bearing modules under
`research/DGamma/` remain excluded from `dgamma.ipkg` and must never merge
unchanged to `main`.

## Executive estimate

The provisional budget is now **65–110 engineering shifts**. Revision 3's
60–100 band is withdrawn. Round 3 localized both blockers to cross-trace order
matching/convergence, but showed that the operational left replay needs a second
namespace/state transport and an exact post-permutation schedule, while O21
needs an explicit accepted-scanner producer.

Re-estimate after proof—not interface elaboration—of O4, O9, O15, O19/O20, and
the O21 scanner induction. A public statement repair invalidates this band.

## 1. Three-part calibration rule

Every strengthened field must pass all three checks before becoming an
interface:

1. **Consumer necessity:** name the later constructor/induction that projects
   the exact field.
2. **Producer inhabitability:** construct it in every accepted endpoint case,
   including original-present/canonical-absent and asymmetric cross-trace
   vestigials.
3. **Index discipline:** write a small external positive consumer at the exact
   state, trace, and raw-name namespace where the operational theorem replays.

Round 2 caught violations of producer inhabitability: unrestricted paths through
vestigial names. Round 3 caught an index-discipline violation: the certified
permutation lived at `rightFinal` over right names while the declared operational
consumer replayed the left canonical trace.

Revision 4 retains no unrestricted path transport. Two-sided comparability is
stated only for names proved members of the corresponding support orders.

## 2. Exact producer/consumer pipeline

| Producer | Output guaranteed by the interface | Immediate consumer |
|---|---|---|
| Relational action/suffix replay | `RelationalReplayCorrespondence` mapping actual/yielded generators and iterator stages with map/outcome preservation | structural correspondence composition and `TraceIndependent` transport |
| Any recursive replay state | Full `ReplayInvariantBundle`: alignment, discipline, empty/well-formed start, endpoint WF, quiet/no-failure, totality, independence, provenance, ranks, acyclicity, support well-foundedness, and `SupportMatchesActive` | next deletion or adjacent swap; Lemmas 68/70 |
| A/A, A/O, O/A, or O/O commute | `LocalRelationalDiamond` with action/tag/branch preservation and endpoint quotient | `AdjacentSwapResult` suffix replay |
| One D72 iteration | `DeletionChainStep` with replay/external/endpoint/registration capital, exact withdrawn generations, a `DeletedGenerationClassification` for each, and next premises | delete-all recursion |
| Delete-all recursion | `ClosingFreeReduction` with dependent typed history, exact endpoint-list equality, registration accounting, and replay capital | shape/order/sorting and one-trace assembly |
| Support bridge | Minimal `CanonicalSupportTransport`: support truth plus exact reduced→original linearization and placement outputs | immutable `CanonicalSchedule` constructor only |
| Closing-free sorting | `SortedClosingFreeTrace` with replay correspondence, full bundle, exact blocks/order/coverage/placement, endpoint, and registration tree | simultaneous one-trace assembly |
| Deletion + sorting | `OneTraceOrchestrationAccounting` with exact endpoint withdrawn list | simultaneous assembly |
| Simultaneous one-trace constructor | `IndependentCanonicalSchedule`: schedule, both independence witnesses, exact replay correspondence, full canonical bundle, and total schedule-withdrawal classification | cross-trace matching; scanner induction |
| Supported order matching | `MappedCanonicalSupportOrders`: supported membership in both directions; supported comparability forward/backward; inverse-mapped right order linearizing `leftFinal`; `CertifiedIncomparablePermutation leftFinal leftOrder (map renameBackward rightOrder)` | operational replay of the left canonical trace |
| Bundle-preserving left permutation | `CanonicalConvergenceResult`: enriched `permutedLeftCapital`, exact inverse-mapped target order, left-canonical→permuted replay correspondence, composed endpoint quotient, same inputs, and `CanonicalEndpointBridge` whose left index is exactly the permuted schedule | scanner production and O21 |
| Scanner-discard induction | `deletedClassificationForcesLeftScannerDiscardSpike` / right: exact located occurrence plus same-parent close implies membership in the accepted scanner's indexed deleted list | complete scanner producer |
| Scanner producer | Complete `acceptedDeletionScannerCapitalSpike` from exact `sameInputs` and two enriched schedules; no membership premise | O21 four-way vestigial cases |
| Post-permutation final assembly | Complete `originalEndpointsConvergeSpike`: constructs scanner capital for `permutedLeftCapital`, consumes its exact bridge, and calls O21 | `ConfluenceResult` constructor with the same permuted schedule |

The right-state `mappedLeftOrderLinearizesRight` and right-state
`mappedOrderPermutation` fields from revision 3 were removed: no operational
consumer replays at that index. The accepted right schedule already carries its
own right-state linearization.

`composeGenerationBijection`, `composeNameBijection`,
`composeRelationalReplayCorrespondence`, `assembleIndependentCanonicalSchedule`,
`acceptedDeletionScannerCapitalSpike`, `originalEndpointsConvergeSpike`, and the
outer `ConfluenceResult` assembly have complete bodies in research. Their hard
inputs remain explicitly named proof obligations.

## 3. Probe-driven revision-4 corrections

### 3.1 Left-operational permutation now fits positively

The round-3 negative consumer requested:

```text
CertifiedIncomparablePermutation leftFinal
  (supportOrder leftSchedule)
  (map (renameBackward renaming) (supportOrder rightSchedule))
```

Revision 3 failed at `rightFinal` versus `leftFinal`. Revision 4's external
`leftOperationalPermutationNowFits` projects exactly this type and elaborates.
No trace/state renaming operation is assumed.

The producer interface states both supported comparability directions:

- left `SupportPath` → forward-renamed right `SupportPath`, requiring both names
  in the left support order;
- right `SupportPath` → backward-renamed left `SupportPath`, requiring both names
  in the right support order.

These membership guards prevent both previously refuted vestigial path
applications.

### 3.2 Post-permutation schedule and bridge cannot detach

`CanonicalConvergenceResult` no longer contains an arbitrary
`permutedLeftTrace` plus an independently selectable bridge. It contains an
`IndependentCanonicalSchedule` for the left original trace, target-order
equality, replay correspondence from the input left canonical trace, a composed
`RelationalReplayEndpoint`, and a bridge indexed by this exact permuted schedule.
The schedule itself supplies target block decomposition, block order, lifecycle
coverage, placement, registration accounting, endpoint, full bundle, and both
independence witnesses.

Positive probes project the exact target order and target-indexed bridge and
complete the post-permutation O21 assembly without scanner/bridge premises. A
negative probe trying to reinterpret that bridge at the pre-permutation left
schedule fails on:

```text
convergence.permutedLeftCapital versus leftCapital
```

### 3.3 Scanner producer and classification discipline

`DeletedGenerationClassification` no longer stores a misleading freely chosen
“scanner-shaped event.” It stores the exact original generated-registration
occurrence, exact generation equality, and same-parent `LUnload` occurrence on
the exact suffix.

The two scanner-indexed induction theorems state the precise consequence: under
the accepted `RegistrationTraceCorrespondence` from empty indices, this
classification forces the located generation into the left/right final
`indexedDeletedGenerations`. Their proofs must inspect the correspondence at the
located occurrence: queued/matched surviving branches carry `NoParentUnload` and
contradict the stored close; the remaining branch is the scanner's own discard
branch using its exact `registrationEventAt`.

`acceptedDeletionScannerCapitalSpike` is a complete constructor body applying
those inductions to each schedule withdrawal. External left and right consumers
project accepted deleted-set membership **without taking scanner capital as a
premise**.

### 3.4 Retained endpoint calibration probes

Both vestigial variants still elaborate:

1. one-trace original-present/reduced-absent retired child through simultaneous
   schedule assembly;
2. asymmetric cross-trace left vestigial/right-renamed-absent through the new
   left-operational permutation.

The source-sensitive O/A application also remains externally callable.

## 4. Proof obligations in dependency order

There remain **23 obligations: O1–O22 mathematical/proof obligations and O23
validation/release**. Grades are S, M, L, XL.

| ID | Obligation and produced capital | Depends on | Grade and reason |
|---|---|---|---|
| **O1** | Trace/list algebra; external-input algebra; replay-endpoint algebra; proved name/generation/replay-correspondence composition. | accepted CP3/RAR | **M.** Dependent endpoints remain nontrivial, though interfaces elaborate. |
| **O2** | Lift generic `RelationalReplayCorrespondence` structurally to both `TraceIndependent` fields. | O1 | **M–L.** Composition is proved; remaining work is structural transformation lifting. |
| **O3** | A/A diamonds for L-Begin and L-Iter/L-Finish with moved tags, branches, effects, controls, and early applicability. | O2 | **L–XL.** Advance outcomes remain case-heavy. |
| **O4** | Both mixed A/O and O/A orientations with early applicability and actor/child/licensing-parent exclusions. | O2–O3 | **XL gate.** Required by yielded-registration block crossings. |
| **O5** | O/O diamonds, especially yielded O-Insert/O-Insert, with source freshness, generations, registration positions, and anti-license crossing. | O1–O2 | **XL gate.** Counterexample forces sorting redesign. |
| **O6** | Implement `AdjacentSwapResult` for all orientations; suffix replay returns correspondence, composed endpoint, same inputs, and complete next bundle. | O1–O5 | **XL.** Exhaustive RAR replay/invariant reconstruction. |
| **O7** | Executable closed/open episode scanners, exact begin ordinals, and uniqueness. | GEN | **L.** Finite but indexed under raw-name reuse. |
| **O8** | Select support/parent-maximal close and derive all D72 negative/generation premises. | O7, Lemmas 68/70 | **XL.** Occurrence/generation maximality is not raw-name maximality. |
| **O9** | Enrich one D72 call with replay/endpoint/registration capital, exact classifiers, strict decrease, and next bundle. | O2, O8, D72 | **XL.** Requires internal fold evidence, not public-result strengthening. |
| **O10** | Well-founded delete-all recursion on trace length. | O7–O9 | **L.** Measure is easy; dependent recursion is not. |
| **O11** | Compose deletions into `ClosingFreeReduction`; transport typed occurrence/classification history and exact endpoint/accounting. | O1, O9–O10 | **XL.** Lemma-72-scale ordinal transport. |
| **O12** | Closing-free shape: one supported open begin ordinal; unsupported lifecycle absence; eliminate non-paper tags. | O7, O11 | **L–XL gate.** Counterexample triggers algorithm review. |
| **O13** | Project/reconstruct Lemma-68/70 capital from every bundle. | O9 | **S–M.** Positive projection elaborates. |
| **O14** | Construct finite duplicate-free support linearization. | O13 | **M–L.** Enumeration and uniqueness only. |
| **O15** | Prove minimal one-trace support truth/linearization/placement bridge in every vestigial case. | O11, O13–O14 | **L–XL gate.** No unrestricted path claim is available. |
| **O16** | Preserve root input order; place generated births; compose external/generated registration accounting with exact withdrawals. | O1, O6, O11 | **L–XL.** Root and generated actions obey different constraints. |
| **O17** | Sort actor blocks via all four local orientations, threading a complete bundle at every adjacent step; build `SortedClosingFreeTrace`. | O6, O12–O16 | **XL.** Major whole-block induction. |
| **O18** | Assemble and project `IndependentCanonicalSchedule`. | O11, O15–O17 | **S.** Constructor body is proved; hard capital belongs upstream. |
| **O19** | Prove supported membership plus two-sided supported comparability transport, inverse-mapped right linearization at `leftFinal`, and the left-operational certified permutation. | O14–O18 | **XL.** Cross-state/namespace theorem must avoid all unsupported vestigials. |
| **O20** | Execute O19 on the left canonical trace; every swap consumes/returns full bundles; construct enriched target-order `permutedLeftCapital`, composed endpoint quotient, and exact permuted→right bridge. | O2–O6, O18–O19 | **XL.** Explicit post-permutation schedule/block/bridge capital is mandatory. |
| **O21** | Prove both exact scanner-discard inductions; use the complete scanner producer; prove four-way vestigial original equivalence at the fixed accepted bijection. | O9–O11, O18, O20 | **XL.** Raw-name reuse, scanner indices, and occurrence alignment remain Lemma-72-scale. |
| **O22** | Assemble permuted schedule, right schedule, and O21 equivalence into `ConfluenceResult`; inhabit `confluenceTheorem`. | O20–O21 | **S.** Complete composition body elaborates. |
| **O23** | Consumer-index probes, both vestigial regressions, O/A, sequential checks, reviews, docs, and release exclusion of holes. | O1–O22 | **M–L.** External review gates remain mandatory. |

## 5. Dependency phases and 65–110 budget

Phase ranges overlap; common RAR and scanner induction infrastructure is counted
once in the total.

| Phase | Obligations | Provisional band |
|---|---|---:|
| A — replay algebra/independence | O1–O2 | 4–8 |
| B — four local orientations and suffix replay | O3–O6 | 10–18 |
| C — scanners, selection, enriched D72 | O7–O9 | 8–15 |
| D — recursion and typed cumulative history | O10–O11 | 8–15 |
| E — shape, support order, minimal support bridge | O12–O15 | 7–13 |
| F — orchestration accounting and one-trace block sorting | O16–O18 | 9–16 |
| **G — left operational order, enriched permutation, scanner/O21** | **O19–O21** | **18–30** |
| H — outer theorem and validation | O22–O23 | 2–5 |

Plan **65–110 total** after reuse/overlap. The upper range acknowledges 25 named
research holes after making final scanner/O21 composition explicit; hole count is
not a proof-size metric.

## 6. Mathematical gates and decisions

| Gate | Pass criterion | Failure consequence |
|---|---|---|
| **G1 replay independence** | O2 proves both Definition-60 fields from generic correspondence. | Enrich replay or evaluate a direct canonical evaluator; public changes require review. |
| **G2 four-way local commute** | A/A, A/O, O/A, O/O cover every crossing generated by block sorting. | Redesign sorting to avoid the failing crossing. |
| **G3 activation shape** | Closing-free supported blocks contain only L-Begin/L-Iter/L-Finish plus yielded insertions. | Counterexample and algorithm/statement review. |
| **G4 one-trace support bridge** | Direct linearization/placement outputs hold in all accepted withdrawal cases without arbitrary paths. | Change internal ordering; public schedule only after counterexample. |
| **G5 left-operational comparability** | O19 proves supported two-sided transport and left-state permutation while both vestigial probes remain inhabitable. | Redesign matching/permutation; never replay right-index evidence on a left trace. |
| **G6 target-coupled permutation** | O20 constructs the exact enriched target schedule, composed quotient, full bundle, and its bridge. | Enrich the result further or redesign block replay. |
| **G7 scanner-linked endpoint composition** | The exact scanner inductions place every schedule withdrawal in accepted deleted lists and close all four endpoint cases. | Strengthen internal occurrence/index capital; public statement only after counterexample. |

`SameOrchestrationModuloGenerated` remains fixed accepted capital. Supervisor
decisions are requested only after a failed gate or public-statement pressure.

## 7. Round-3 finding closure map

| Finding | Round-3 defect | Revision-4 resolution |
|---:|---|---|
| **1 blocker** | Right-state/right-name permutation could not replay left canonical trace. | Removed unused right operational theorem. Added support-membership-guarded comparability both ways, inverse-mapped right linearization at `leftFinal`, and exact left-state certified permutation. The former negative consumer now elaborates positively. |
| **2 blocker** | Arbitrary replayed trace and independent bridge; no target blocks/order/schedule. | `CanonicalConvergenceResult` now owns enriched `permutedLeftCapital`, exact target order, source→target correspondence, composed quotient, and a bridge indexed by the target schedule. Complete post-permutation assembly uses this schedule; detached pre-permutation bridge probe is rejected. |
| **3 major** | `AcceptedDeletionScannerCapital` had consumers but no producer. | Added complete `acceptedDeletionScannerCapitalSpike` from `sameInputs` plus two enriched schedules. External left/right withdrawal consumers invoke it directly and take no scanner premise. |
| **4 major** | 60–100 and O19/phase G understated corrected work. | Re-estimated 65–110; O2=M–L, O18=S, O19/O20/O21=XL, phase G=18–30. |
| **5 minor** | “Scanner-shaped event” comment hid missing event/index equality. | Removed the arbitrary event fields/comment. Classification now stores exact occurrence and same-parent close; two explicit correspondence inductions state the exact accepted deleted-list consequence using the scanner's own `registrationEventAt`. |

## 8. Retained prior-review closure

The following externally checked repairs remain intact: source-sensitive O/A;
minimal one-trace support transport; absence of both unrestricted path maps;
simultaneous schedule/replay/full-bundle assembly; typed cumulative deletion
history; fixed composed-bijection coupling; exact external/generated accounting;
all four local orientations in downstream sorting signatures; both vestigial
interface variants; and exactly 23 obligations.

## 9. Validation and release boundary

Before proof authorization, external round-4 review must verify:

- the left-operational consumer at `leftFinal` passes exactly;
- supported comparability guards cannot reconstruct unrestricted vestigial paths;
- post-permutation target schedule/order/blocks/quotient/bridge share indices;
- the detached pre-permutation bridge attempt fails for the intended reason;
- left and right scanner membership project without scanner premises;
- both vestigial variants and the O/A application still elaborate; and
- the fixed current-name bijection is unchanged through O21 and outer assembly.

All five spikes must elaborate sequentially, one Idris process at a time, against
an exact copy of release `src/`. Release `dgamma.ipkg` must remain unaware of
research modules. Any proof implementation must recreate accepted interfaces as
total, hole-free `src/DGamma/CP5*` modules and pass adversarial review, package
build, escape scans, and documentation gates. Theorem 73 remains unproved by
design after revision 4.
