# O6 revision 67: occurrence fold closes; outer alignment quantity stop

## Scope

Grind shift #75 (overall #129) resumed from the accepted revision-66 boundary
`fd733c2`. It followed the authorized order:

1. structural nonemptiness lemma as its own commit;
2. whole-suffix occurrence-fold retry;
3. global positional ordinal proof;
4. identity generation renaming only after that proof;
5. target-bundle composition in field order; and
6. no final assembly without a closed bundle.

The structural lemma, occurrence origin/tag fold, global ordinal theorem,
generated-registration correspondence, and exact suffix-alignment
reconstruction are retained in five lemma-sized commits. Target field 1 then
exhausted its fresh three-attempt budget at local quantity annotations in the
private outer envelope. Per the grind rules, the complete uncommitted envelope
was reverted and the shift stopped at safe HEAD `f35d9b5`.

No cure 2, frozen declaration change, public-interface change, result
construction, or spike-body edit occurred.

## 1. Structural nonemptiness — `c6c9248`

The authorized theorem is retained:

```idris
0 appendLocatedTransitionNotEmpty :
  (prior : Transitions initial before) ->
  (located : Transition before afterState) ->
  (suffix : Transitions afterState finalState) ->
  appendTransitions prior (MoreTransitions located suffix) =
    NoTransitions {state = initial} -> Void
```

It recurses structurally on `prior`. Both clauses expose
`MoreTransitions = NoTransitions`, so constructor disjointness discharges the
proof without normalizing `transitionCount` beneath an abstract prefix.

Attempt history:

1. parser failure because `prefix` is an Idris fixity keyword and cannot be
   used as that explicit binder;
2. elaborator could not bind the otherwise-unconstrained `state` implicit of
   `NoTransitions`;
3. success after renaming the binder to `prior` and fixing the empty state
   explicitly as `{state = initial}`.

This was committed separately and R16 passed before and after the commit.

## 2. Whole-suffix occurrence origin and tags — `92a28ad`

Attempt 1 closed:

- `locatedChildRegistrationRoundTrip`;
- `noLocatedActionOccurrenceInEmpty`, now applying
  `appendLocatedTransitionNotEmpty` directly to the stored prefix, transition,
  suffix, and decomposition;
- `sealedSuffixActionOrigin`; and
- `sealedSuffixActionTagPreserved`.

The recursive step consumes only the exact source/target heads and sealed tail.
The empty case uses structural nonemptiness and never identifies phantom trace
endpoints. R16 passed before and after commit.

## 3. Global positional ordinal — `4ed7ecc`

`sealedSuffixActionOrdinalPreserved` closed on attempt 1. It composes the
accepted whole-cons positional theorem recursively and eliminates the empty
case structurally. This commit precedes every use of identity generation
renaming. R16 passed before and after commit.

## 4. Generated-registration correspondence — `8f0d259`

Attempt 1 closed:

- `sealedSuffixGeneratedOrigin` via the retained projection conversion;
- exact generated/action-origin coherence via the conversion round trip;
- generated ordinal preservation by applying the global action-ordinal theorem
  and rebuilding `MkRegistrationGeneration child`; and
- `sealedSuffixActionRegistrationReplayCorrespondence`.

Only here, after the committed global ordinal theorem, is
`identityRegistrationGenerationBijection` selected. Cure 2 remains unused.
R16 passed before and after commit.

## 5. Producer-owned suffix alignment — `f35d9b5`

Target bundle field 1 requires alignment of the exact replayed trace. The
frozen suffix seal intentionally does not expose detached alignment. A private
reconstruction theorem therefore invokes the same pointwise producer and
consumes each producer-owned `headAligned` field.

Retained helpers:

- `appendAlignedTransitions`;
- `alignedAppendLeft`;
- `alignedAppendRight`;
- `prependAlignedSingleton`; and
- `replayPointwiseSuffixSpineAligned`.

The last theorem's result is indexed by

```idris
spineReplayedTrace
  (replayPointwiseSuffixSpine nameEq keyEq source aligned
    sourceWellFormed endpoint)
```

so no replayed trace or alignment is caller-selected.

Attempt history:

1. dependent pattern-variable aliases in append splitting and a locally named
   head not definitionally identified with the normalized producer call;
2. source transition aliases and a locally named well-formedness proof had the
   same dependent identity issue;
3. success after patterning the exact outer-dictionary `Fired` form and using
   the exact normalized producer/well-formedness expressions.

R16 passed before and after commit.

## 6. Target field 1 outer envelope: attempt budget exhausted

The reverted private `AdjacentAlignedPointwiseReplay` unit was designed to own:

- replayed suffix final state and trace;
- whole target trace and exact decomposition;
- target whole-trace alignment;
- suffix endpoint; and
- sealed suffix replay.

Its producer derived, in order:

1. decomposed original alignment from `replayAligned` and the exact input
   decomposition;
2. prefix, pair, and suffix alignment by the retained append splitters;
3. source pair-final well-formedness by checked aligned execution;
4. the diamond-owned source/target suffix-start endpoint;
5. the exact pointwise suffix replay;
6. target suffix alignment from `replayPointwiseSuffixSpineAligned`; and
7. whole target alignment from unchanged prefix, `movedPairAligned`, and the
   replayed suffix.

No proof premise was added to the caller boundary.

All three failures were local quantity/mechanical failures, but the fresh unit
budget is exhausted:

1. inferred local syntax `0 prefixAligned = ...` was parsed as an integer-based
   expression (`fromInteger`); Idris requires a type after a local quantity;
2. removing the local quantity made `prefixAligned` runtime, so the erased
   `alignedAppendLeft` helper was inaccessible;
3. after adding exact erased proof-local types, the remaining untyped
   `suffixReplay` local was runtime, so the quantity-0
   `replayPointwiseSuffixSpine` producer was inaccessible:

```text
replayPointwiseSuffixSpine is not accessible in this context.
```

The narrow continuation is mechanical: give `suffixReplay` its exact local
quantity-0 `PointwiseSuffixSpineReplay ...` type (and keep all proof locals
quantity 0). The enclosing producer itself is quantity 0, so its projected
runtime-shaped data remains erased at this theorem boundary. A fresh gate is
required before retry because all three attempts were consumed.

The entire uncommitted outer record and producer were reverted. The retained
suffix-alignment theorem remains checked and producer-indexed.

## Frozen-capital audit

The shift did not modify:

- `JointLocatedConsTargetGenerator`;
- the `e3fab3a` generator-origin section;
- whole-cons or recursive whole-suffix RAR;
- revision-20 public/record interfaces;
- the `35dcbe5` projection conversion;
- `AdjacentSwapResult` or its hidden constructor; or
- `adjacentSwapSuffixSpike` and its frozen signature/body-hole slice.

## Status

- structural nonemptiness: **proved**;
- whole-suffix action occurrence origin/tag: **proved**;
- global positional ordinal preservation: **proved**;
- generated-registration origin/coherence/ordinal: **proved**;
- whole-suffix `ActionRegistrationReplayCorrespondence`: **proved**;
- identity generation renaming: **selected only after global ordinal proof**;
- exact replayed-suffix alignment: **proved**;
- target bundle field 1, whole target alignment: **quantity STOP; outer unit reverted**;
- target bundle fields 2–15: **unopened**;
- final opaque result and spike body: **unopened**;
- holes: **20**, split **6/4/8/1/1**;
- movement against 1–12: **one shift consumed; prior lower bound exhausted, upper remainder 11**.
