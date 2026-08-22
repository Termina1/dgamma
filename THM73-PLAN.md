# Theorem 73 (Confluence) — CP5 scoping plan, revision 7

Branch: `cp5-thm73-scoping`

Review trail:

- rounds 1–6: REJECT;
- `review-cp5-plan-round6.md`: one wrong-birth bridge blocker and two producer-boundary majors.

This remains research-only interface scoping. Accepted statements, every file
under `src/`, `dgamma.ipkg`, and `confluenceTheorem` are immutable. Hole-bearing
modules under `research/DGamma/` remain excluded from the release package and
must not merge unchanged to `main`.

## Executive estimate

The provisional raw proof budget is **82–142 engineering shifts**. Revision 6's
75–130 is withdrawn rather than silently retained: accepted-generation bridge
matching, a nonempty Cartesian whole-block witness, independent O7/O8/O9 gates,
and separate O10/O11 producers add measurable work.

Mandatory re-estimation gates remain:

1. the first complete singleton and general
   `operationalAdjacentBlockSwapSpike`, including its exact Cartesian labels;
2. the first complete O7 scan plus O8 maximal selector plus O9 enriched D72
   step; and
3. the first complete accepted-correspondence same-name scanner proof matching
   the concrete 6/18 and 9/14 fixtures.

No proof grind is authorized before external ACCEPT and user budget approval.

## 1. Retained revision-6 sealing

Round 6 confirmed that the sealing design survives every tested attack:

- public `MappedCanonicalSupportOrders` contains membership only;
- a pure polluted certificate cannot reach O20;
- an outer sealed package cannot be rebuilt around a polluted inner
  certificate;
- `AdjacentActorSwapSafety` cannot detach from its exact current
  trace/blocks/bundle;
- a generated child contradicts the licensing safety before O20; and
- wrong trace, stale quotient, mixed schedule, and wrong occurrence-relation
  substitutions remain rejected.

Revision 7 preserves these types. O19 still returns
`CertifiedOperationalCanonicalPermutation`, existentially coupling its selected
actor permutation to the exact operational recursive realization. Safe-selector
existence for schedules whose support relations differ through withdrawn
intermediates remains an explicit XL mathematical risk.

## 2. Accepted-generation bridge matching

### 2.1 Round-6 defect

The bridge exposed the exact replay→canonical-left source occurrence but allowed
any canonical-right occurrence with the same renamed child, parent, and
component. Under raw-name reuse, another birth can have the same action while
representing a different original generation.

### 2.2 Revision-7 equation

`ReplayedCanonicalEndpointBridge` now consumes the full left and right
`CanonicalSchedule`s. For every replayed generated occurrence it returns:

1. the exact canonical-left occurrence selected by
   `ActionRegistrationReplayCorrespondence`;
2. a canonical-right occurrence with renamed child/parent and equal component;
   and
3. the erased equation

```text
generationForward (generatedGenerationBijection sameInputs)
  (registrationGeneration
    (canonicalToOriginal (canonicalRegistrationTree leftSchedule)
      sourceOccurrence))
=
registrationGeneration
  (canonicalToOriginal (canonicalRegistrationTree rightSchedule)
    rightOccurrence)
```

The direction is deliberate:

`replayed target → canonical-left source → original-left generation → accepted
forward bijection → original-right generation`.

The positive producer probe constructs exactly this dependent tuple. The
round-6 alternate same-action right-birth reconstruction now fails at the
original-generation equation, not at an incidental import or trace index.

## 3. Nonempty Cartesian whole-block derivations

### 3.1 Zero-node removal

`FiniteAdjacentSwapDone` remains the recursion terminator for an exhausted
finite fold. It no longer inhabits a nontrivial `OperationalAdjacentBlockSwap`.
That record now requires `WholeBlockSwapDerivation`, whose first field is a
`NonEmptyFiniteAdjacentSwapDerivation` exposing a real orientation, local
diamond, and `AdjacentSwapResult`.

### 3.2 Exact selected-block indexing

The whole-block witness is indexed by the exact:

- `AdjacentActorOrderSwap`;
- current source trace;
- source `ActorBlockDecomposition`;
- current `ReplayInvariantBundle`;
- `AdjacentActorSwapSafety`; and
- target trace.

Every adjacent node is labeled by a pair of zero-based positions in the selected
left and right located blocks. `TraceActionTagAt` ties those positions to the
node's concrete transition action and tag, distinguishing repeated Iter steps.
The witness additionally proves:

- every in-bounds left/right position pair occurs;
- every labeled node uses in-bounds positions of those selected blocks;
- crossing-position pairs are unique; and
- node count equals the product of the two nonempty block transition counts.

Thus it represents the Cartesian crossing rather than a phantom derivation
indexed only by endpoint traces.

### 3.3 Weak→strong calibration

The positive single-crossing probe constructs a whole-block witness from one
real orientation/diamond/result when both blocks contain exactly one transition.
It proves the strengthened interface does not require a second node and does not
exclude the singleton boundary case. The old zero-node producer is a required
negative and now fails because `FiniteAdjacentSwapDerivation` cannot replace
`WholeBlockSwapDerivation`.

## 4. Independent deletion-chain gates

Revision 6's exact 27-hole count hid O7 and O9 inside O8's selector hole. Revision
7 exposes five independently testable producers and keeps legacy consumers as
complete wrappers.

### O7 — executable occurrence scan

`closingEpisodeOccurrenceScanSpike` takes explicit initial/final state handles
and a checked trace. It returns `ClosingEpisodeScan` containing dependent
located closed occurrences, unique opening ordinals, completeness, and an empty
scan→`NoClosingEpisodes` proof.

### O8 — maximal candidate selection

`selectMaximalClosingEpisodeSpike` consumes the exact O7 scan and full
canonicalization premises. Its selected branch returns a
`DeletableClosingEpisode` tied to an ordinal in that scan; its empty branch is
separate from deletion enrichment.

### O9 — enriched one-step D72 adapter

`enrichDeletionChainStepSpike` consumes one exact O8 candidate and returns
`DeletionChainStep`, including D72, replay/effect/occurrence capital, typed
classification, registration accounting, the next full bundle, and strict
length decrease.

`chooseClosingStepSpike` is now a complete O7→O8→O9 wrapper with no hole.

### O10/O11 split

`deleteClosingEpisodesCoreSpike` performs only well-founded recursion and
returns `ClosingFreeTraceCore`: closing-free trace, next premises, same external
inputs, replay correspondence, and typed history.

`assembleClosingFreeAccountingSpike` separately constructs cumulative endpoint
and canonical-registration accounting from that exact core. The old
`deleteAllClosingEpisodesSpike` is a complete O10→O11 wrapper.

## 5. Scanner and static regression retention

All revision-6 scanner and static results remain:

- scanner events retain constructor kind and exact generation;
- target-specific interleaving is tied to exact discard positions;
- same-name births are left 6/18 and right 9/14;
- full final index and exact deleted-list equalities hold for all three retained
  cross-side orders:
  - L6, R9, L18, R14;
  - R9, L6, R14, L18;
  - L6, R9, R14, L18;
- wrong-generation substitution is rejected; and
- one-, moved-, and two-intermediate four/five-fiber artifacts remain honestly
  labeled static/interface tests, not reachable O19/O20 executions.

## 6. Exact producer/consumer pipeline

| Producer | Exact output | Immediate consumer |
|---|---|---|
| Replay/occurrence algebra | effect plus action/tag/generated-generation correspondence | diamonds, deletion, operational fold, bridge |
| Local A/A, A/O, O/A, O/O | source-sensitive `LocalRelationalDiamond` | `AdjacentSwapResult` |
| Adjacent suffix replay | next trace, endpoint, both correspondences, next full bundle | nonempty Cartesian derivation |
| Whole-block producer | safety-indexed nonempty exact block-position crossing | operational actor recursion |
| O7 scanner | unique complete located closing occurrences | O8 selector |
| O8 selector | scan-indexed maximal deletable candidate or empty | O9/closing-free branch |
| O9 adapter | enriched `DeletionChainStep` | O10 recursion |
| O10 recursion | `ClosingFreeTraceCore` | O11 accounting |
| O11 accounting | `ClosingFreeReduction` | sorting |
| One-trace sorting | `IndependentCanonicalSchedule` | O19 and scanner producer |
| O19 | membership match plus sealed operational permutation | O20 |
| O20 | noncanonical execution, composed replay/occurrence/quotient, generation-coupled bridge | O21 |
| O21 | endpoint equivalence modulo exact vestigial generations | outer wrapper |
| O22 wrapper | original schedules plus equivalence | immutable `ConfluenceResult` |

No cross-endpoint `SupportPath`, comparability, incomparability, or false left
linearization has been reintroduced.

## 7. Proof obligations and independently testable status

There remain **23 obligations**. Every row names an independent hole-bearing
producer or is explicitly marked complete/record-only.

| ID | Obligation | Producer status | Grade |
|---|---|---|---|
| **O1** | Trace/external-input/endpoint/generation and occurrence algebra. | **5 named holes**; occurrence composition helpers complete. | **M–L.** |
| **O2** | Transport both `TraceIndependent` fields. | **2 named holes.** | **M–L.** |
| **O3** | A/A diamonds with exact tags/outcomes/effects/controls. | **1 named hole.** | **L–XL.** |
| **O4** | A/O and O/A with applicability and licensing exclusions. | **2 named holes.** | **XL gate.** |
| **O5** | O/O with exact freshness/generation discipline. | **1 named hole.** | **XL gate.** |
| **O6** | Adjacent suffix replay and nonempty Cartesian whole-block producer. | **2 independently callable named holes.** | **XL gate.** |
| **O7** | Executable complete/unique closing-occurrence scan. | **1 named hole**, explicit state-handle API. | **L–XL gate.** |
| **O8** | Scan-indexed maximal deletable candidate. | **1 named hole.** | **XL gate.** |
| **O9** | Enriched one-step D72 producer. | **1 named hole.** | **XL gate.** |
| **O10** | Well-founded delete recursion to `ClosingFreeTraceCore`. | **1 named hole.** | **L–XL.** |
| **O11** | Cumulative endpoint/history/registration accounting. | **1 named hole**; O10→O11 wrapper complete. | **XL.** |
| **O12** | Closing-free supported open-block shape. | **1 named hole.** | **L–XL.** |
| **O13** | Project reached-state/Lemma-68/70 capital from bundles. | **Complete record projections; no hole.** | **S–M.** |
| **O14** | Duplicate-free support ordering. | **1 named hole.** | **M–L.** |
| **O15** | Minimal support truth/placement bridge under vestigials. | **1 named hole.** | **L–XL gate.** |
| **O16** | Root/generated input placement and orchestration accounting. | **1 named hole.** | **L–XL.** |
| **O17** | One-trace block sorting with full recursive capital. | **1 named hole.** | **XL.** |
| **O18** | Assemble `IndependentCanonicalSchedule`. | **1 named hole** with complete simultaneous result record. | **S–M.** |
| **O19** | Renamed actor matching plus sealed safe operational selector. | **2 independently callable named holes.** | **XL gate.** |
| **O20** | Aggregate operational replay/occurrence/quotient and generation-coupled bridge. | **1 named hole**; fold composition helpers complete. | **L–XL.** |
| **O21** | Two accepted scanner inductions and four-way vestigial composition. | **3 named holes.** | **XL gate.** |
| **O22** | Build immutable `ConfluenceResult`. | **Complete wrapper; no hole.** | **S.** |
| **O23** | Adversarial validation and release isolation. | **Record/probe-only; no proof hole.** | **M–L.** |

## 8. Exact hole reconciliation

Revision 7 contains **30 deliberate named research holes**:

- canonical sort: 6;
- cross-trace: 4;
- deletion chain: 10;
- local diamonds: 8;
- renaming/O21: 2.

The count increased 27→30 because:

- O7 scan, O8 selection, and O9 enrichment replace one combined selector hole
  (**+2**); and
- O10 recursion and O11 accounting replace one combined delete-all hole
  (**+1**).

Forward and reverse mapping is exact:

- O1=5, O2=2, O3=1, O4=2, O5=1, O6=2;
- O7=1, O8=1, O9=1, O10=1, O11=1, O12=1;
- O13=0 complete, O14=1, O15=1, O16=1, O17=1, O18=1;
- O19=2, O20=1, O21=3, O22=0 complete, O23=0 validation.

These values sum to 30. No table obligation is silently hidden inside another
hole.

## 9. Phase arithmetic: 82–142

| Phase | Obligations | Raw band |
|---|---|---:|
| A — replay/occurrence algebra and independence | O1–O2 | 4–8 |
| B — four orientations, suffix replay, Cartesian block producer | O3–O6 | 14–24 |
| C — independently gated scan, maximal selection, enriched D72 | O7–O9 | 10–18 |
| D — split recursion and cumulative accounting | O10–O11 | 9–17 |
| E — shape/support/minimal bridge | O12–O15 | 7–13 |
| F — one-trace accounting and sorting | O16–O18 | 9–16 |
| G — sealed matching, accepted-generation bridge, scanner/O21 | O19–O21 | 27–41 |
| H — outer theorem and validation | O22–O23 | 2–5 |

The rows sum exactly to **82–142**. No overlap deduction is applied.

## 10. Round-6 finding closure

| Finding | Revision-7 resolution |
|---:|---|
| **1 blocker — wrong same-action right birth** | Bridge consumes both schedules and requires accepted original-generation equality. Actual-direction positive passes; Probe 24 reconstruction fails at that equation. |
| **2 major — zero-node/unindexed block derivation** | Added nonempty head, exact selected-block position labels, Cartesian completeness/soundness/uniqueness/count, singleton positive, and zero-node negative. |
| **3 major — O7/O9 hidden inside selector** | Added independent O7 scan, O8 selection, O9 D72, O10 core recursion, and O11 accounting producers; legacy functions are complete wrappers. |

## 11. Seven exact round-7 changes

| # | Required change | Resolution |
|---:|---|---|
| 1 | Couple bridge by accepted generation | Full left/right schedules plus canonical→original and accepted-generation equation; duplicate-birth reconstruction rejected. |
| 2 | Nonempty block-indexed Cartesian derivation | `WholeBlockSwapDerivation`; single-crossing/singleton positive and zero-node negative. |
| 3 | Split O7/O8/O9 and preferably O10/O11 | Five separate producer gates; two complete compatibility wrappers. |
| 4 | Retain sealing/coupling negatives | Old/outer pollution, safety detachment, generated-child, wrong trace, stale quotient, mixed schedule, wrong occurrence all retained. |
| 5 | Retain scanner/static tests | Three scanner orders, wrong generation, honest one/moved/two-intermediate tests retained. |
| 6 | Reconcile/re-estimate | Exact 30-hole two-way map and exact raw 82–142 sum. |
| 7 | Release hygiene | Immutable production/CP3, research isolation, external 207/207, and index hygiene remain required. |

## 12. Validation and release boundary

External round-7 review must verify:

- Probe 24 cannot replace the right birth without the accepted-generation
  equation;
- the equation's forward direction composes with the actual replay fold and both
  canonical registration trees;
- `FiniteAdjacentSwapDone` cannot inhabit an actor-step output;
- a real one-node crossing inhabits the interface for singleton blocks;
- Cartesian labels remain tied to exact current blocks/safety;
- O7/O8/O9 and O10/O11 are independently callable and wrappers contain no holes;
- all retained sealing, detachment, scanner, static, and full-pipeline probes;
- exactly 30 named holes and the reverse obligation map;
- all five spikes elaborate serially;
- exact release build reaches 207/207; and
- `src/`, `dgamma.ipkg`, and CP3 remain byte-identical to the accepted baseline.

Production remains hole-free and research-unreachable. Theorem 73 remains
unproved by design after revision 7.
