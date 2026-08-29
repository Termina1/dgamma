# O6 revision 68: outer alignment closes; target discipline semantic stop

## Scope

Grind shift #76 (overall #130) resumed from accepted revision-67 HEAD
`5c338f2`. The authorized private outer-alignment retry closed on attempt 1 and
is retained at `875cd88`.

Bundle composition then advanced strictly to field 2,
`replayDiscipline`. This exposed a new semantic wall class in the frozen
adjacent interface: `LocalRelationalDiamond` retains the moved actions and
endpoint relation, but not the parent/child exclusion premises needed to
transport `RegistrationDiscipline` across a mixed activation/child-insertion
swap. Per the explicit shift ruling, work stopped at the first new semantic
wall. Fields 3–15 and final assembly were not opened.

Safe retained HEAD before this audit is `875cd88`.

## 1. Outer alignment retry — attempt 1, `875cd88`

The private `AdjacentAlignedPointwiseReplay` envelope owns:

- the replayed suffix final state and exact suffix trace;
- the whole target trace and definitional swapped decomposition;
- whole target `AlignedTransitions`;
- the suffix endpoint; and
- the exact `SealedSuffixReplaySpine`.

`produceAdjacentAlignedPointwiseReplay` accepts no output-shaped capital. It
constructs every field from the original bundle, exact decomposition, diamond,
and the retained pointwise suffix producer.

The accepted quantity recipe was applied proactively:

| Local | Quantity | Role |
|---|---:|---|
| `decomposedAligned` | 0 | original alignment reindexed by exact decomposition |
| `sourcePair` | unrestricted local data | exact two-transition source pair |
| `prefixAligned` | 0 | left append projection |
| `afterPrefixAligned` | 0 | right append projection |
| `sourcePairAligned` | 0 | exact source pair alignment |
| `sourceSuffixAligned` | 0 | exact source suffix alignment |
| `sourcePairFinalWellFormed` | 0 | checked execution well-formedness |
| `startEndpoint` | 0 | diamond endpoint at suffix start |
| `suffixReplay` | 0 | exact `PointwiseSuffixSpineReplay ... suffix (swappedFinal diamond)` |
| `replayedSuffix` | 0 | exact trace projection of `suffixReplay` |
| `replayedSuffixAligned` | 0 | same-producer suffix alignment |
| `targetTrace` | 0 | exact prefix/moved-pair/replayed-suffix concatenation |
| `targetAligned` | 0 | whole target alignment |

The previously untyped runtime local is now exactly:

```idris
0 suffixReplay : PointwiseSuffixSpineReplay name key world error value
  nameEq keyEq suffix (swappedFinal diamond)
```

The unit checked on its first fresh attempt. R16 passed before and after the
lemma-sized commit.

This closes target bundle field 1 without changing any frozen record or public
function type.

## 2. Field 2 statement

The next required field is:

```idris
RegistrationDiscipline protocol nameEq alignedReplayTrace
```

For ordinary actions its step obligation is `()`. For a root `OInsert`, the
rank witness depends only on the preserved action and protocol. For a child
insertion, however, the exact obligation is:

```idris
(ParentRegistrationYield protocol nameEq parent component before,
 ChildRetirementProvenance parent child rest)
```

Both parts are temporal and positional. In particular,
`ParentRegistrationYield` states that the named parent at the insertion's exact
**before state** is `Reloading (sourceStep :: continuation) ...` and that this
current step's yield tag catalogs the inserted component.

## 3. The missing frozen capital

The genuine mixed diamond producers require precisely the exclusions needed by
this field:

```idris
activationOrchestrationDiamondSpike ...
  ((child, parent : name) -> ... ->
    transitionAction right = OInsert child (ChildOf parent) component ->
    Not (transitionActor left = parent))
```

and:

```idris
orchestrationActivationDiamondSpike ...
  childSafe
  parentSafe
```

`review-cp5-r14-scoped.md` already classified these premises as
**consumer-significant** even though the local operational diamond body itself
does not inspect them.

They are not fields of `LocalRelationalDiamond`. Its frozen record retains:

- moved transitions and alignment;
- action/tag equations;
- activation/orchestration branch transport functions; and
- final effect/control/well-formed endpoint evidence.

It does **not** retain `parentSafe`, `childSafe`, distinct owners, or a
registration-discipline transport law. The public constructor
`MkLocalRelationalDiamond` is externally usable (for example by
`R19SuffixFreeFullAdjacentCertificatePositive.idr`), so the adjacent theorem
cannot recover those premises by assuming every supplied record was built by a
particular private producer.

## 4. Why endpoint and occurrence capital do not repair field 2

Consider the mixed source ordering

```text
L-Begin parent ; O-Insert child (ChildOf parent) component
```

and its operationally commuting target ordering

```text
O-Insert child (ChildOf parent) component ; L-Begin parent
```

At the source insertion point, `L-Begin` may have put the parent into the exact
`Reloading` state whose current program step yields `component`, satisfying
`ParentRegistrationYield`.

At the target insertion point the parent is observed **before** `L-Begin`; it
may be `Inactive`. The checked O-Insert rule requires parent presence, not the
protocol's `ParentRegistrationYield`, so the target insertion can still be a
checked transition while its registration-discipline obligation is false.

The genuine A/O producer excludes this case with `parentSafe`. A bare
`LocalRelationalDiamond` does not carry that exclusion.

The other already-closed capital is insufficient:

- final `ControlEquivalent` relates only the pair endpoints, not the two
  insertion-before states;
- `ActionRegistrationReplayCorrespondence` locates actions and preserves
  ordinal/generation data, but does not provide control equivalence at every
  corresponding prefix;
- `SealedSuffixReplaySpine` starts after the moved pair and therefore cannot
  establish the missing pair-local parent state; and
- accepting target `RegistrationDiscipline` as a caller premise would violate
  the producer-owned-capital rule.

Thus this is not a quantity, parser, dictionary, or elaboration identity issue.
It is a missing semantic premise at the frozen local-diamond/adjacent boundary.

## 5. Required design ruling

At least one frozen-surface design change is needed before field 2 can be
proved honestly. Plausible directions are:

1. retain a protocol-quantified registration-discipline transport law in a
   richer producer-owned local-diamond certificate;
2. retain the exact A/O, O/A, and O/O parent/child exclusions in an indexed
   adjacent-swap safety package and require the O6 producer to consume that
   package; or
3. narrow `adjacentSwapSuffixSpike` to an opaque genuine-diamond producer whose
   type prevents manually assembled `LocalRelationalDiamond` values from
   entering the bundle-producing path.

A detached target discipline premise is explicitly rejected. Merely retaining
`AdjacentSwapOrientationEvidence` is also insufficient: that family records
only A/A, A/O, O/A, or O/O classification, not the consumer-significant mixed
parent/child exclusions.

No cure is selected here because all options affect a frozen public/result
boundary or producer architecture and require supervisor review.

## Frozen-capital audit

The shift did not modify:

- `JointLocatedConsTargetGenerator`;
- the `e3fab3a` generator-origin section;
- whole-cons or recursive whole-suffix RAR;
- the `35dcbe5` projection conversion;
- the `4ed7ecc` global ordinal theorem;
- the `8f0d259` whole-suffix occurrence correspondence;
- the `f35d9b5` suffix-alignment theorem;
- revision-20 public/record surfaces;
- `AdjacentSwapResult`; or
- `adjacentSwapSuffixSpike` and its frozen slice.

## Status

- private outer alignment producer: **proved, attempt 1**;
- target bundle field 1 (`replayAligned`): **proved inside private envelope**;
- target bundle field 2 (`replayDiscipline`): **new semantic STOP**;
- target bundle fields 3–15: **unopened by strict field order**;
- final opaque result and spike body: **unopened**;
- holes: **20**, split **6/4/8/1/1**;
- movement against 1–11: **one shift consumed; lower bound exhausted, prior upper remainder 10**.
