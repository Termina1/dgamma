# O6 revision 106: pair-RAR direct-constructor STOP-AUDIT

## Scope

Grind shift #114 (overall #168) resumed from accepted HEAD `da74e48` and opened
only the positional pair RAR under a fresh three-attempt budget. The authorized
source-stored-check cure was applied. It exposed two further consequences of
retaining the exact source transitions behind local let aliases. The final
attempt confirmed that source alignment reindexes the B6 dispatch equality to
the aligned action while the let-bound reconstruction remains stuck at the
original constructor field. The entire unit was removed; field 9 and later work
were not opened.

## Retained successful spine inside all attempts

All attempts preserved the already checked part of the removed unit:

- one elimination of `R101FourAlignedHeadViews`;
- package-owned moved/source cross action and tag equations only;
- explicit transport of both moved checked equations;
- deterministic reindexing of moved-right output and moved-left input/output;
- exhaustive Iter/Iter versus Retire/Retire branch selection;
- two singleton RAR calls followed by cons RAR.

No opaque diamond action/tag projection, detached alignment, proof-irrelevance
axiom, or dictionary equality was used.

## Three-attempt record

### Attempt 1

The two singleton calls were changed to use the checked proofs stored by the
unaliasing source constructors:

```idris
leftOriginalChecked
rightOriginalChecked
```

The singleton source transition now matched the exact result index. The next
argument—the activation classification witness—had been reindexed by source
alignment to the alignment-local erased proof. Idris reported:

```text
PaperActivationStep
  (Fired nameEq keyEq leftAction leftTag leftChecked)
vs
PaperActivationStep
  (Fired nameEq keyEq leftAction leftTag leftOriginalChecked)
```

### Attempt 2

The activation and orchestration witnesses were transported explicitly through
`paperActivationStepTransport` / `paperOrchestrationStepTransport`. This removed
the witness proof mismatch. The surrounding RAR source index still used the
fully typed local alias `sourceLeftStep`, whose action/tag fields did not reduce
after the alignment elimination. Idris then isolated:

```text
Mismatch between: leftTag and leftOriginalTag.
```

### Attempt 3

Both transported moved checks and singleton calls were changed to use the
original action/tag constructor fields. This showed why that direction cannot
close while the let aliases remain: `sourceActionSame` from the B6 dispatch had
correctly been reindexed by source alignment to `leftAction/rightAction`, while
the local alias still exposed `leftOriginalAction/rightOriginalAction`.
The decisive diagnostic was:

```text
Mismatch between: leftAction and leftOriginalAction.
```

A fourth attempt was not made.

## Isolated next representation

The next fresh unit should return to attempt 2's aligned action/tag transport,
but remove both local source-step lets completely.

Use the direct exact constructor expressions everywhere an original source step
is required:

```idris
Fired leftNameEq leftKeyEq leftOriginalAction leftOriginalTag
  leftOriginalChecked
Fired rightNameEq rightKeyEq rightOriginalAction rightOriginalTag
  rightOriginalChecked
```

Specifically:

1. pass those direct constructors to `r101ProduceFourAlignedHeadViews`;
2. pass them directly as the source head/tail arguments of
   `consRelationalReplayCorrespondence`;
3. eliminate source alignment before deriving local source equalities so the
   GADT can reindex the constructor fields directly, not through a let alias;
4. use the aligned action/tag names and the source-stored checked proofs in the
   singleton calls;
5. transport the activation/orchestration witnesses explicitly as in attempt 2.

The target side, package cross transport, endpoint reindexing, and both
singleton branches are already past elaboration. This remains a source
constructor-reduction boundary, not a semantic gap.

## Status

- B6 dispatcher: **complete and frozen**;
- positional pair RAR: **removed after three attempts**;
- field 9: **append composition retained; population unopened**;
- fields 10–15: **foundations retained; population unopened**;
- body/assembly: **unopened**;
- holes: **20**, split **6/4/8/1/1**.

One shift of the accepted **1–4 shift** band was consumed. A nominal **1–3
shift** remainder is proposed.

## Manifest and isolation

```text
NO_FROZEN_SURFACE_CHANGE_REQUIRED
```

The frozen `adjacentSwapSuffixSpike` remains 1183 bytes with SHA-256
`e6d0c2d669355e5b7bef9efea1707f5853c708deb888bafe5770ba40dbd15a41`.
Production `src/`, `dgamma.ipkg`, CP3, revisions 19–21, B6, and all prior capital
remain unchanged. No new hole, escape, staged change, probe, or partial pair-RAR
surface remains.
