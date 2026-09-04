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
  and the fully qualified attempt 3 passed. This was the pre-revision necessity
  witness, not an O15 body attempt.
- `canonicalChildPlacementFromForward`: 2/3; the first spelling left the
  dependent `lookupFiber` value family implicit, and the fully explicit result
  type passed.
- `canonicalAccountedGenerationClassified`: 2/3; the first spelling left the
  dependent-pair source of `canonicalElemMapPreimage` polymorphic, and explicit
  `source`/`target`/`project` arguments passed.
- O15 `canonicalSupportTransportSpike`: **1/3, passed and closed** after the
  authorized chosen-order correction.
- O16 `deletionSortingOrchestrationAccountingSpike`: **1/3, passed and closed**
  after the authorized exact-fold-capital correction and fallback review gate.
- O18 `independentCanonicalScheduleSpike`: **1/3, passed and closed** using the
  deletion-history classification extractor. Commit `5b3db7f` says “O17” in its
  subject; that subject is an administrative label slip—the checked definition
  is O18.
- O17 `sortClosingFreeTraceSpike`: **0/3**. It remains the genuine XL stable
  root-hoisting/block-sorting algorithm. No speculative body was charged before
  the mandatory validation stop described below.

## Validation and invariants

Every retained helper and body commit was preceded by a visible fresh direct
check of its owning module or fixture. Final direct evidence after all three
closures established:

```text
Idris 2, version 0.8.0

CP5ConfluenceCanonicalSortSpike.idr direct check: exit 0
CP5ConfluenceCrossTraceSpike.idr direct check: exit 0
R6FourFiberStatic.idr direct check: exit 0
R8FullPipeline.idr direct check: exit 0
R4VestigialSimultaneous.idr direct check: exit 0
seeded/cached `idris2 --build dgamma.ipkg`: exit 0
```

A subsequent genuinely clean package build removed `build/` first and was
terminated by the host with `Killed: 9`, exit **137**. Under the binding rule
that any failed build/check ends implementation after audit, no retry and no O17
attempt was started. This is an infrastructure/OOM release-gate failure rather
than an Idris diagnostic, but it means R143 cannot claim a successful clean full
package build.

Non-Idris post-failure invariants:

- exact start `13abcd01c243d774609450b98f06fc3fcc3667de` is an ancestor;
- production/package/doc diff (`src`, `dgamma.ipkg`, `README.md`, `NOTES.md`)
  from the exact start is empty;
- `src/DGamma/CP3.idr` start/current blob is unchanged at
  `2c697e532e83989de8591fa6a4378747c6a501c0`;
- no added `believe_me`, `assert_total`, postulate, `unsafePerformIO`, `partial`,
  or `covering` declaration occurs in changed Idris lines;
- `git diff --check` passes;
- no exact-name `idris2` process remains; and
- only the three permitted pre-existing untracked files remain.

The research-hole census is now **13**, split explicitly as:

```text
CanonicalSort 2  (parked O14 and open O17)
CrossTrace    4
DeletionChain 6
LocalDiamond  0
Renaming       1
```

## Status

**Three non-O14 CanonicalSort holes closed: O15, O16, and O18.** O15 and O16 use
supervisor-authorized, audited, positively ratified/premise-tracked surface
corrections. O17 remains the honest stable-sort algorithm at 0/3. O14 and all
parked DeletionChain obligations remain untouched. Production and frozen CP3
surfaces are unchanged.

**Release acceptance is partial, not green:** all direct research checks and a
seeded package build passed, but the final clean package build was killed by the
host (exit 137). The next shift must begin at this safe committed boundary by
rerunning that clean build under sufficient memory before opening O17.
