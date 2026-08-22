# Theorem 73 (Confluence) — CP5 scoping plan, revision 6

Branch: `cp5-thm73-scoping`

Review trail:

- `review-cp5-plan-round1.md` — REJECT;
- `review-cp5-plan-round2.md` — REJECT;
- `review-cp5-plan-round3.md` — REJECT;
- `review-cp5-plan-round4.md` — REJECT;
- `review-cp5-plan-round5.md` — REJECT, one certificate-pollution blocker and
  four interface/regression majors.

This remains research-only interface scoping. Accepted statements, `src/`,
`dgamma.ipkg`, and `confluenceTheorem` are immutable. Hole-bearing modules under
`research/DGamma/` remain excluded from the package and must not merge unchanged
to `main`.

## Executive estimate

The provisional proof budget is **75–130 engineering shifts**. Revision 5's
70–120 claim is withdrawn: its raw upper bound was 124, and the claimed 0–4
reuse did not justify subtracting four. Revision 6 adds explicit safe-certificate
selection, finite whole-block derivations, transition/registration-occurrence
composition, and a concrete exact scanner fixture.

Mandatory re-estimation gates are:

1. the first complete `operationalAdjacentBlockSwapSpike`, including every
   finite A/A, A/O, O/A, and O/O crossing; and
2. the first complete accepted-correspondence same-name scanner proof matching
   the concrete 6/18 and 9/14 index fixture.

No proof grind is authorized before external ACCEPT and user budget approval.

## 1. Round-6 sealing decision

Revision 6 retains round 5's sound option-(b) core—no cross-endpoint
`SupportPath`, comparability, incomparability, or left linearization transport—
but replaces its polluted O19/O20 boundary.

### 1.1 Why revision 5 was false

`MappedCanonicalSupportOrders` publicly stored a pure
`CertifiedActorPermutation`, and O20 quantified over every value of that record.
A caller could prepend any adjacent swap and its inverse while preserving all
other fields. Actor inequality does not establish local safety: the checked
parent/child mutation `OInsert child (ChildOf parent) ...` followed by the
child's `LBegin` refutes the O/A licensing exclusion.

### 1.2 Sealed-by-operational-evidence shape

The corrected interface has three layers:

1. Public `MappedCanonicalSupportOrders` contains only renamed support-set
   membership both ways. It contains **no permutation certificate**.
2. `CertifiedOperationalCanonicalPermutation` existentially owns one pure actor
   permutation together with its exact target trace, target blocks, final full
   bundle, and an `OperationalActorPermutation` realizing that same certificate.
3. O20 accepts only this operational package. There is no function from an
   arbitrary public pure certificate or reconstructed mapped record to O20.

Every `OperationalActorStep` contains:

- the exact current trace, actor-block decomposition, and
  `ReplayInvariantBundle`;
- `AdjacentActorSwapSafety` at that current state;
- generated-child/licensing exclusions for both block directions;
- an `OperationalAdjacentBlockSwap` indexed by that safety; and
- a `FiniteAdjacentSwapDerivation` whose every transition transposition stores
  an A/A, A/O, O/A, or O/O orientation and its concrete `AdjacentSwapResult`.

A swap/inverse loop is therefore not rejected because it is redundant; it is
rejected unless the caller can construct safety and actual local derivations at
both exact intermediate states. The round-5 pollution producer now fails before
O20.

### 1.3 Honest existence risk

Sealing makes the real mathematical obligation explicit: it remains unproved
that two accepted schedules always admit a safe operational actor permutation
when their full support relations differ through withdrawn intermediates. This
is an O19 XL gate, not a consequence of finite-list membership equality.

## 2. Exact one-step producer

`operationalAdjacentBlockSwapSpike` is now a separate named theorem. Its inputs
are exactly:

- one `AdjacentActorOrderSwap`;
- the current trace;
- its exact `ActorBlockDecomposition`;
- its complete `ReplayInvariantBundle`; and
- `AdjacentActorSwapSafety` derivable for that pair at that state.

Its output must include a finite derivation enumerating the Cartesian crossing
of the two actor blocks. Each node classifies the transition pair as A/A, A/O,
O/A, or O/O, supplies the corresponding source-sensitive local diamond, and
stores the complete `AdjacentSwapResult`. Thus the central early-applicability,
generated-child, licensing-parent, freshness, tag, outcome, and suffix-replay
proof cannot be hidden behind an endpoint record.

`NoGeneratedChild` and `generatedChildAtHeadContradictsSafety` expose the exact
pre-O20 rejection boundary. The external parent/child probe proves that a block
body headed by the licensing O-Insert cannot supply the safety required to move
the generated child's block before it.

## 3. Action and registration occurrence capital

Effect-generator correspondence cannot identify a moved O-Insert. Revision 6
adds `ActionRegistrationReplayCorrespondence`:

- every target `LocatedActionOccurrence action` maps to a source occurrence of
  the same dependent action;
- source and target rule tags are equal;
- every target `LocatedGeneratedRegistration child parent component` maps to a
  source occurrence with those exact child, parent, and component indices; and
- birth ordinals are related by an explicit replay-generation bijection.

`AdjacentSwapResult` carries this relation. Finite adjacent derivations compose
it; `OperationalActorPermutation` composes it recursively. The composed
relation is derived by
`operationalPermutationOccurrenceCorrespondence`, not asserted as an O20 field.

`ReplayedCanonicalEndpointBridge` is indexed by that exact occurrence relation.
Its `replayedGeneratedBirthMatched` output exposes the exact canonical-source
occurrence selected by `replayGeneratedRegistrationOrigin` before producing the
right occurrence. Generated-birth matching therefore cannot be justified from
RAR effect maps alone.

## 4. Producer/consumer pipeline

| Producer | Exact output | Immediate consumer |
|---|---|---|
| Relational replay algebra | effect-generator/stage correspondence and endpoint quotient | independence and suffix replay |
| Occurrence replay algebra | action/tag and generated child/parent/component/ordinal correspondence | operational fold and replay→right bridge |
| Local A/A, A/O, O/A, O/O | `LocalRelationalDiamond` with substantive source safety | `AdjacentSwapResult` |
| Adjacent suffix replay | next trace, full bundle, quotient, effect and occurrence correspondence | finite block derivation |
| One whole-block producer | safety-indexed finite orientation derivation, exact next blocks and bundle | recursive operational permutation |
| Delete-all and sorting | enriched `IndependentCanonicalSchedule` | support matching, scanner, and operational selection |
| Cross-trace set match | public membership-only `MappedCanonicalSupportOrders` | simultaneous safe operational selection |
| O19 safe selection | `CertifiedOperationalCanonicalPermutation` | O20 aggregation and bridge |
| O20 aggregation | exact noncanonical target, replay quotient, external inputs, occurrence-indexed bridge | O21 |
| Accepted scanner producer | exact original-schedule deletion classifications | O21 vestigial cases |
| O21 composition | original endpoint equivalence modulo exact vestigial generations | immutable outer result |
| Outer assembly | original left/right canonical schedules and endpoint equivalence | `ConfluenceResult` |

Removed fields remain absent:

- no forward or backward cross-endpoint `SupportPath` transport;
- no cross-endpoint comparability or incomparability;
- no inverse-right `LinearizesSupport leftFinal`;
- no public mapped permutation certificate; and
- no false canonical schedule for the operational intermediary.

## 5. Regression boundaries

### 5.1 Four-fiber evidence is intentionally split

The branch does **not** claim a concrete reachable end-to-end four-fiber run.
Because O19/O20 bodies remain research holes, the retained artifacts are
honestly labeled as two separate checks:

1. **Static endpoint/path tests:** concrete one-intermediate, moved-intermediate,
   and two-intermediate states retain the real support path, unsupported
   withdrawn fibers, accepted endpoint relation, refuted false left
   linearization, and a pure replacement actor target. The licensing-parent
   mutation is admitted by the endpoint relation but refuted by full
   well-formedness.
2. **Abstract accepted-index interface test:**
   `IntermediateVestigialStaticInterfaceRegression` consumes real enriched
   trace indices, scanner-deleted generation evidence, path first/rest, and
   right absence. It proves the withdrawn intermediate is not an actor entry.
   It does not claim to run O19 or O20 concretely.

This split checks that option (b) removed the old false field without
misrepresenting hole-index elaboration as reachability or operational execution.

### 5.2 Exact scanner events and concrete generation reuse

`ScannerEvent` distinguishes nonregistration, discard, queue, and match events
on each side. Every generated event stores its exact
`RegistrationGeneration`; a skip cannot masquerade as a discard.

`TargetDiscardsInterleaved` ties the four exact accepted discards to alternating
positions:

`Left earlier < Right earlier < Left later < Right later`.

`SameRawNameScannerRegression` retains exact deleted-list memberships but now
requires this target-specific positional evidence.

A retained executable fixture applies deleted-registration index updates for the
same raw name at left ordinals 6/18 and right ordinals 9/14. It proves full final
`RegistrationIndexState` equalities and exact deleted lists:

- left: current `(raw,18)`, deleted `[(raw,18),(raw,6)]`;
- right: current `(raw,14)`, deleted `[(raw,14),(raw,9)]`.

A second cross-side event order, R9/L6/R14/L18, computes the exact same per-side
indices and lists. The wrong-generation consumer remains a required negative.

### 5.3 Coupling negatives

Required failures are:

1. revision-5 swap+inverse certificate pollution;
2. wrong operational bridge trace;
3. stale quotient from a different operational package;
4. mixed left canonical capital; and
5. wrong same-name generation.

Required positives include exact one-step intermediate threading, finite
occurrence capital, the complete published-boundary pipeline, static
one/moved/two-intermediate mutations, licensing-parent exclusion, and exact
scanner fixture equalities.

## 6. Proof obligations in dependency order

There remain **23 obligations: O1–O22 proof obligations and O23 validation**.
Grades are S, M, L, XL.

| ID | Obligation | Depends on | Grade |
|---|---|---|---|
| **O1** | Trace/list/external-input/endpoint algebra plus generation-bijection, effect replay, and action/registration-occurrence identity/composition. | accepted CP3/RAR | **M–L.** Occurrence composition is now partly complete. |
| **O2** | Lift generic replay correspondence to both `TraceIndependent` fields. | O1 | **M–L.** |
| **O3** | A/A diamonds for Begin and Iter/Finish with exact tags, outcomes, effects, controls, and applicability. | O2 | **L–XL.** |
| **O4** | A/O and O/A including early applicability and generated-child/licensing-parent exclusions. | O2–O3 | **XL gate.** |
| **O5** | O/O, especially yielded Insert/Insert with generation and freshness discipline. | O1–O2 | **XL gate.** |
| **O6** | Complete adjacent suffix replay and the exact finite whole-block producer; compose effects, occurrences, endpoints, full bundles, and external inputs. | O1–O5 | **XL gate, expanded.** First mandatory re-estimation point. |
| **O7** | Executable closed/open episode scanners and occurrence uniqueness. | GEN | **L.** |
| **O8** | Select generation-aware support/parent-maximal D72 candidate. | O7, Lemmas 68/70 | **XL.** |
| **O9** | Enrich one D72 call with exact typed classifications and recursive capital. | O2, O8, D72 | **XL.** |
| **O10** | Well-founded delete-all recursion. | O7–O9 | **L.** |
| **O11** | Compose typed deletion history and exact endpoint/registration accounting. | O1, O9–O10 | **XL.** |
| **O12** | Closing-free supported open-block shape. | O7, O11 | **L–XL gate.** |
| **O13** | Project Lemma-68/70 capital from every bundle. | O9 | **S–M.** |
| **O14** | Construct finite duplicate-free support linearization. | O13 | **M–L.** |
| **O15** | Minimal one-trace support truth/linearization/placement bridge under vestigials. | O11, O13–O14 | **L–XL gate.** |
| **O16** | Root/generated input placement and exact registration accounting. | O1, O6, O11 | **L–XL.** |
| **O17** | Initial one-trace block sorting with all four orientations, occurrence capital, and full bundle threading. | O6, O12–O16 | **XL.** |
| **O18** | Assemble `IndependentCanonicalSchedule`. | O11, O15–O17 | **S.** Complete wrapper. |
| **O19** | Prove renamed actor-set matching and simultaneously choose an inhabitable `CertifiedOperationalCanonicalPermutation`; no arbitrary pure certificate boundary. | O6, O14–O18 | **XL gate.** Safe-permutation existence remains unproved. |
| **O20** | Fold the sealed operational package into exact replay/occurrence/quotient capital and construct the occurrence-indexed replay→right bridge. | O1, O6, O18–O19 | **L–XL.** No public certificate quantification. |
| **O21** | Prove both accepted scanner-discard inductions with exact events/ordinals and complete four-way vestigial endpoint composition. | O9–O11, O18, O20 | **XL gate.** Second mandatory re-estimation point. |
| **O22** | Assemble original schedules and O21 equivalence into `ConfluenceResult`; inhabit `confluenceTheorem`. | O20–O21 | **S.** Wrapper checked. |
| **O23** | Pollution, licensing, intermediate mutations, occurrence coupling, scanner, detachment, package, review, and release-isolation validation. | O1–O22 | **M–L.** |

## 7. Phase totals and 75–130 arithmetic

| Phase | Obligations | Raw band |
|---|---|---:|
| A — replay and occurrence algebra/independence | O1–O2 | 4–8 |
| B — four orientations, suffix replay, whole-block producer | O3–O6 | 12–21 |
| C — selection and enriched D72 | O7–O9 | 8–15 |
| D — recursive typed deletion history | O10–O11 | 8–15 |
| E — shape/support/minimal bridge | O12–O15 | 7–13 |
| F — one-trace accounting and sorting | O16–O18 | 9–16 |
| G — sealed operational matching, occurrence bridge, scanner/O21 | O19–O21 | 25–37 |
| H — outer theorem and validation | O22–O23 | 2–5 |

The rows sum exactly to **75–130**. No undocumented overlap subtraction is
applied. Reuse may reduce the observed cost, but it is not removed from the
authorization envelope before the two mandatory gates produce measured data.

## 8. Round-5 finding closure map

| Finding | Revision-6 resolution |
|---:|---|
| **1 blocker — public certificate pollution** | Removed the certificate from `MappedCanonicalSupportOrders`. O20 consumes only `CertifiedOperationalCanonicalPermutation`, which owns exact safety and realized recursion. The reviewer's producer is a required negative. |
| **2 major — no one-step producer** | Added `AdjacentActorSwapSafety`, generated-child rejection, orientation-classified `FiniteAdjacentSwapDerivation`, and separately stated `operationalAdjacentBlockSwapSpike`. |
| **3 major — occurrence capital dropped** | Added action/tag/generated child-parent-component-ordinal replay correspondence to `AdjacentSwapResult`, finite derivations, recursive folds, and bridge indices. |
| **4 major — four-fiber overclaim** | Relabeled code and plan as separate static and abstract accepted-index interface tests. No reachable operational fixture is claimed. |
| **5 major — weak scanner interleaving** | Replaced side-only events with constructor-and-generation events, exact targeted ordering, full 6/18 and 9/14 final-index equalities, reordered cross-side fixture, and wrong-generation negative. |
| **Estimate defect** | Replaced 70–120 with exact raw 75–130; no overlap deduction. |

## 9. Seven exact round-6 changes

| # | Required change | Resolution |
|---:|---|---|
| 1 | Seal pollution | Membership-only mapped record; operational evidence package; old pollution probe rejected. |
| 2 | Exact one-step producer and licensing rejection | Separate theorem with finite four-orientation derivation; parent/child contradiction occurs at `NoGeneratedChild`, before O20. |
| 3 | Action/registration correspondence | Composed action/tag and generated child/parent/component/ordinal relation indexes the bridge and source occurrence output. |
| 4 | Operational fixture or honest relabel | Honest static/interface split in code comments and this plan. |
| 5 | Strong scanner regression | Exact event kind/generation positions, full concrete index/list equalities in two cross-side orders, wrong-generation negative. |
| 6 | Estimate | Exact 75–130 rows; gates after first block swap and accepted scanner proof. |
| 7 | Closure validation | All mutation, threading, detachment, full-pipeline, hole-count, build, immutable-blob, and isolation checks are mandatory. |

## 10. Validation and release boundary

Before proof authorization, external round-6 review must verify:

- the revision-5 swap/inverse dependent producer cannot reach O20;
- parent/child licensing is rejected at the one-step safety boundary;
- every finite derivation node carries an exact orientation and
  `AdjacentSwapResult`;
- exact action/registration occurrences compose through the operational fold
  and are consumed by the bridge;
- one/moved/two-intermediate static variants still pass and licensing-parent
  endpoint mutation remains excluded by the full bundle;
- all three coupling detachments and wrong-generation substitution fail;
- the complete published-boundary pipeline elaborates;
- all five spikes elaborate serially;
- the named research-hole count is reconciled after revision 6;
- the exact release package builds 207/207; and
- `src/`, `dgamma.ipkg`, and the immutable CP3 blob remain unchanged from
  `34b21c9`.

The five spikes now contain **27 deliberate named research holes**: canonical
6, cross-trace 4, deletion 7, local 8, and renaming 2. The round-5 count was 25;
the two new holes are the separately scoped one-step block producer and sealed
safe-permutation selector. No old hole disappeared or was silently renamed into
an assumption.

Production remains hole-free and research-unreachable. Theorem 73 remains
unproved by design after revision 6.
