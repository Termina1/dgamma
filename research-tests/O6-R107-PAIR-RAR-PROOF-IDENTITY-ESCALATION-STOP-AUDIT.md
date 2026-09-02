# O6 revision 107: pair-RAR proof-identity escalation STOP-AUDIT

## Scope

Grind shift #115 (overall #169) resumed from accepted HEAD `4d244bf` and opened
only the fourth, explicitly final implementation budget for positional pair
RAR. The revision-106 direct-constructor cure was applied with no source
transition let aliases. It successfully removed action/tag alias opacity and
left one exact boundary: eliminating `AlignedTransitions` reindexes the source
trace to its independently stored erased checked-equation proofs, whereas the
source singleton legs intentionally retain the proofs stored by the original
`Fired` constructors. The complete unit was removed after three attempts.
Field 9 and later work were not opened.

The escalation boundary is now armed: **no fifth pair-RAR implementation budget
is authorized**. The next activity must be a design-only disposable probe
campaign, with no retained proof edit, to settle the exact elaborating source
proof representation.

## Three-attempt record

### Attempt 1 — direct constructors, package first

The A2 shape from revision 106 was reconstructed with:

- exact source `Fired` patterns naming both original checked proofs;
- direct original `Fired` expressions passed to
  `r101ProduceFourAlignedHeadViews`;
- no `sourceLeftStep` or `sourceRightStep` let;
- aligned action/tag names, source-stored checked proofs, and explicit
  `paperActivationStepTransport` / `paperOrchestrationStepTransport` in both
  singleton branches;
- package-owned moved action/tag and checked-equation transport;
- B6 endpoint reindexing and two singleton RARs joined by cons RAR.

The four-head producer and both target transports elaborated. At the direct
source constructor supplied to cons RAR, source alignment had reindexed
`leftOriginalChecked` to the aligned equation while the explicitly written
original action/tag fields remained opaque. Idris reported:

```text
Mismatch between: leftTag and leftOriginalTag.
```

### Attempt 2 — source alignment first

The source alignment elimination was moved before the four-head producer and
before every local source equality. The producer still received the direct
original `Fired` constructors. This confirmed that elimination order alone does
not rewrite the explicitly named original action/tag fields in the final direct
constructor; Idris reached the same `leftTag` / `leftOriginalTag` boundary.

### Attempt 3 — aligned direct action/tag with stored checks

The cons RAR source constructors were then written directly as:

```idris
Fired nameEq keyEq leftAction leftTag leftOriginalChecked
Fired nameEq keyEq rightAction rightTag rightOriginalChecked
```

This removed all remaining action/tag and dictionary opacity. Both singleton
branches and the cons RAR elaborated. The final result comparison isolated only
the two independently stored erased equation proofs:

```text
RelationalReplayCorrespondence ...
  (MoreTransitions
    (Fired nameEq keyEq leftAction leftTag leftOriginalChecked)
    (MoreTransitions
      (Fired nameEq keyEq rightAction rightTag rightOriginalChecked)
      NoTransitions)) ...
vs
RelationalReplayCorrespondence ...
  (MoreTransitions
    (Fired nameEq keyEq leftAction leftTag leftChecked)
    (MoreTransitions
      (Fired nameEq keyEq rightAction rightTag rightChecked)
      NoTransitions)) ...

Mismatch between: rightOriginalChecked and rightChecked.
```

No fourth attempt was made.

## What is now proved about the boundary

The direct-constructor cure is successful for runtime source fields:

- no source transition alias remains;
- source dictionaries reduce to `nameEq` / `keyEq`;
- source action and tag reduce to the aligned names;
- the moved target and endpoint proof spine elaborates;
- both Iter/Iter and Retire/Retire singleton branches elaborate.

The sole unresolved index is proof identity. `AlignedTransitions` stores a
checked equation separately from the proof in the original `Fired` constructor.
Pattern elimination reindexes the expected source trace to the alignment proof.
The source-stored singleton route builds a trace indexed by the original proof.
Idris does not identify these independently stored erased values definitionally.
No proof irrelevance, transition equality, dictionary equality, postulate, or
escape hatch was introduced.

## Mandatory design-only campaign

Before any further implementation edit, disposable probes must settle one of
these exact shapes under independent three-attempt budgets:

1. **Aligned-check direct source probe.** Keep the successful outer source
   alignment and direct aligned `Fired` source constructors, but use
   `leftChecked` / `rightChecked` consistently in the two singleton legs and
   cons result. Re-test the classification witnesses in this direct, no-let
   representation. This is not the failed revision-105 shape: revision 105's
   result was pinned behind original source lets, while this probe's expected
   result has already been reindexed to the alignment proofs.
2. **No source-alignment elimination probe.** Preserve the exact original
   constructor proofs in the result and use only the producer-owned source
   projections/cross equations. This probe must determine whether the common
   dictionaries needed by singleton RAR can be recovered without reindexing the
   whole source trace.
3. **Representation verdict.** If neither exact shape checks, document whether
   a new producer-owned correspondence indexed by the original `Fired` proofs
   is necessary. Do not change `R101FourAlignedHeadViews`, revisions 19–21,
   `ReplayInvariantBundle`, `LocalRelationalDiamond`, or any frozen producer in
   the design campaign.

The first probe is the leading candidate because attempt 3 proved the expected
post-elimination source index is exactly the alignment-proof trace.

## Status

- B6 dispatcher: **complete and frozen**;
- positional pair RAR: **removed; implementation escalation boundary reached**;
- mandatory design-only campaign: **required next**;
- field 9: **append composition retained; population unopened**;
- fields 10–15: **foundations retained; population unopened**;
- body/assembly: **unopened**;
- holes: **20**, split **6/4/8/1/1**.

One shift of the accepted **1–3 shift** band was consumed. A nominal **1–2
shift** remainder is proposed, beginning with design-only probes rather than a
fifth implementation budget.

## Manifest and isolation

```text
NO_FROZEN_SURFACE_CHANGE_REQUIRED
```

The frozen `adjacentSwapSuffixSpike` remains 1183 bytes with SHA-256
`e6d0c2d669355e5b7bef9efea1707f5853c708deb888bafe5770ba40dbd15a41`.
Production `src/`, `dgamma.ipkg`, CP3, revisions 19–21, B6, and all prior capital
remain unchanged. No new hole, escape, staged change, probe, or partial pair-RAR
surface remains.
