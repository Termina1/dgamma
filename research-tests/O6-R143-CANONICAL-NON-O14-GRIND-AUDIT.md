# O6 R143 — CanonicalSort non-O14 grind audit

## Class choice

**Choice: CanonicalSort non-O14, because its four accessible producers construct the canonical schedules consumed by CrossTrace, so it is earlier in the dependency graph; O14 remains parked.**

## Start coordinate

R143 started from `13abcd01c243d774609450b98f06fc3fcc3667de` on
`cp5-thm73-scoping`. The tracked tree was clean. The only untracked paths were
the permitted `paper/cordis-paper.pdf`, `paper/cordis-paper.txt`, and
`review-o6-body-adversarial.md`; the review file is not to be modified, staged,
deleted, or committed.

The R140–R142 audits and `THM73-PLAN.md` were read before class selection. A
fresh direct check of `CP5ConfluenceCanonicalSortSpike.idr` passed with Idris 2
0.8.0 before the first commit. Production and immutable surfaces remain frozen.

## Work log

O15 was opened first by paper obligation order; its body remains untouched.
Before attempting the body, fresh-checked producer capital established:

- retired or absent endpoint entries are outside executable support;
- raw-withdrawn names are unsupported on both endpoint sides;
- supported actors are outside the withdrawal list;
- exact correlated forward/backward fiber lookup packages outside withdrawals;
- component and parent projection from `FiberControlRelated`; and
- forward transport of precedence, parent, and combined support edges when the
  involved actor names are outside withdrawals.

The path lift exposed the known withdrawn-intermediate risk as a concrete O15
surface contradiction. The tracked `R6FourFiberStatic` fixture was extended in
lemma-sized commits. It now proves that `[Alternate, Upper, Lower]` is a genuine
`LinearizesSupport` for the reduced endpoint: the only reduced support path is
`Alternate -> Upper`. The accepted original endpoint still has the path
`Lower -> Middle -> Upper`, where retired unsupported `Middle` is the exact raw
withdrawal. Therefore
`r143CanonicalSupportTransportRefuted` proves `Void` from the current
`CanonicalSupportTransport` result at that endpoint.

This countershape was checked and committed before any surface revision
request, as required. It directly refutes the output record for an accepted
`CanonicalEndpointRelation`. A full refutation of the O15 function telescope
would additionally construct its two operational traces and
`CanonicalRegistrationCorrespondence`; that reachability refinement remains
open, but neither the result record nor the current O15 capital contains an
invariant that rejects the static shape.

## Authorized O15 surface correction

The supervisor authorized revision (A) after reviewing the checked necessity
witness `r143CanonicalSupportTransportRefuted`. The clause mapping is:

| Old O15 bridge surface | Corrected surface |
|---|---|
| `CanonicalSupportTransport ... endpoint` | `CanonicalSupportTransport ... endpoint order`, indexed by the one chosen order |
| `linearizationToOriginal : (order : List name) -> LinearizesSupport reducedFinal order -> LinearizesSupport originalFinal order` | `originalSupportLinearization : LinearizesSupport originalFinal order`, an explicit required/produced witness for the chosen order |
| `inputPlacementToOriginal : (order : List name) -> ...` | `inputPlacementToOriginal : ...` at the record-indexed chosen order |
| O15 producer independent of ordering evidence | O15 producer takes the chosen `order` plus its reduced- and original-endpoint `LinearizesSupport` witnesses; the two exact witnesses derive support-set equality without any universal path claim |
| downstream consumers apply a universal transfer to the reduced ordering | downstream capital is indexed by `orderedSupportNames ordering` and projects the stored original witness |

`supportTruthPreserved` is unchanged. The refuted universal clause is frozen in
the R6 fixture as `R143UniversalCanonicalSupportTransport`, and
`r143CanonicalSupportTransportRefuted` remains the permanent proof that it is
uninhabitable for the accepted countershape.

## Authorized O16 surface correction

The supervisor authorized the standard premise-strengthening repair after the
stored/fold correlation gap was isolated. `ClosingFreeReduction` stores a
`cumulativeRegistrationAccounting` map and `SortedClosingFreeTrace` stores a
`sortedRegistrationTree`, but neither stored map is equated to the exact
`reductionOccurrenceCorrespondence` / `sortingOccurrenceCorrespondence` folds.
Consequently they cannot construct the result's
`AuthenticatedCanonicalRegistrationMap`, whose origin equality is exact.

The checked `assembleOneTraceAccountingFromReplay` theorem is the minimal shape
witness. The O16 mapping is:

| Old O16 producer | Corrected producer |
|---|---|
| reduction + ordering + sorted only | the same three values plus a composed original-to-sorted endpoint |
| no endpoint correlation | exact equality of that endpoint's withdrawn generations with the cumulative reduction endpoint |
| arbitrary stored registration maps implicitly expected to authenticate | `CanonicalReplayAccountingLaws` indexed by the exact `deletionSortingOccurrenceCorrespondence` fold |
| external-input equality absent | still absent as a premise; derived by transitivity from reduction and sorting |

No broader accounting value or authentication result is accepted. A complete
real full-pipeline dischargeability fixture currently depends on the parked O14
shared-order producer and on the still-open DeletionChain assembly. Per the
authorized fallback, the missing producer of these exact
`CanonicalReplayAccountingLaws` is recorded explicitly in `THM73-PLAN.md` and
must remain a visible theorem-73 obligation rather than being inferred from the
uncorrelated stored trees.

## Attempt accounting

- `canonicalRetiredFiberUnsupported`: 1/3, passed.
- `canonicalAbsentFiberUnsupported`: 2/3; attempt 1 exposed the unconstrained
  `value` family at a `Nothing` lookup, and the fully explicit lookup passed.
- All retained endpoint/edge helpers passed on their first direct source check.
- Initial direct R6 check could not find its research import until the direct
  CrossTrace prerequisite was freshly built; this was an environment-order
  failure, not a proof spelling retained in source.
- The first parent-edge fixture spelling was reverted after a dependent
  nonlinear-pattern diagnostic; it was replaced by producer-owned exact lookup
  facts, matching the canonized doctrine.
- `r143RightOrderSound` attempt 1 was reverted after coverage showed that
  mismatched `Elem` indices were not eliminated automatically; the actor-case
  version passed on its fresh budget.
- `r143CanonicalSupportTransportRefuted`: 3/3; attempt 1 lacked the direct
  CanonicalSort import, attempt 2 exposed a zero-hidden qualification warning,
  and the fully qualified attempt 3 passed.
- O15 hole body: 0/3, semantically stopped before edit.
- O16/O17/O18: 0/3, not opened after the dependency stop.

## Validation and invariants

Every retained helper commit was preceded by a visible fresh check of its
owning spike or fixture. Final release gates are pending the supervisor ruling.
Production remains untouched.

## Status

**Semantic stop at O15.** The current hole census remains 16, split 5/4/6/0/1.
O14 and all parked DeletionChain work remain untouched. No surface has been
revised.
