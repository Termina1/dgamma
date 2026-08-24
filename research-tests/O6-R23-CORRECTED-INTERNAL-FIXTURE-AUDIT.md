# Revision-23 corrected internal fixture audit

Authorized base: `cp5-thm73-scoping@3c59d9b`.

## 1. Pair selection — fixed before implementation

The selected local pair is **L-Begin 1 / L-Begin 2**, after the globally empty
initial state has executed the fixed external prefix

```text
OInsert 1 Root emptyComponent
OInsert 2 Root emptyComponent
```

and before the checked suffix

```text
LAdvance 1
LAdvance 2
```

Both selected actors are distinct. Both L-Begin transitions are lifecycle nodes,
so they are internal by action shape on both source and moved sides. This is the
exact O19 opening/opening Cartesian case already authenticated by
`genuineO19BeginBeginExternalProducer`; it does not use the weaker stable O17
root/internal cases.

The ordered root-external subsequence is therefore unchanged:

```text
OInsert 1 Root; OInsert 2 Root
```

The adjacent pair and its moved pair contribute no root observation. Pair-local
`SameExternalOrchestration` must be built by four internal-skip constructors
from the checked L-Begin transitions and moved-action equalities. It will not be
accepted as a caller premise.

### Why this replaces R20

R20 selected two distinct root insertions. That pair is a genuine local O5
commutation but is not an O6 splice preserving the immutable external sequence.
It also ended with two fresh clean inactive roots and was therefore not quiet.

The revision-23 component has empty dependencies, provisions, and program. Each
checked L-Begin records the executable empty target view and enters
`Reloading []`. Each checked L-Advance then takes the L-Finish branch and leaves
the actor `Active` at the same target. Consequently the intended source endpoint
is quiet and has no failed fibers without retirement, removal, or failure-shaped
capital.

No auxiliary retirement is needed. If later fixture changes introduce one, every
retirement must be an actual checked trace head and must participate in all
alignment, discipline, totality, occurrence, and replay evidence.

## 2. Construction obligations

Implementation proceeds in this order:

1. define the concrete empty initial state, the two checked root insertions, the
   checked L-Begin/L-Begin pair, and checked L-Advance/L-Advance suffix;
2. construct pair-local external order from internal classifications;
3. construct the source `ReplayInvariantBundle` from executable evidence:
   alignment, registration discipline, initial/final well-formedness, computed
   quietness and no-failure, trace totality, and trace independence;
4. derive provenance, rank, parent-rank, acyclicity, support well-foundedness,
   and support/active matching through the existing checked-trace theorems;
5. only after the source bundle authenticates, construct the local diamond and
   replay the exact suffix through its relational endpoint;
6. transport target fields strictly in `ReplayInvariantBundle` declaration
   order, quietness first after the already-closed first five fields.

A caller-selected quietness, no-failure, domain relation, external relation,
independence witness, or later endpoint invariant is forbidden.

## 3. Constructive source result

`R23CorrectedInternalFixturePositive` now constructs the exact six-node source
trace and its complete `ReplayInvariantBundle`.

The construction is not a Boolean fixture assertion:

- all six transitions use checked evaluator equations;
- the two moved L-Begin transitions form the actual O3 local diamond;
- `r23PairExternalOrder` skips the source and moved pair as lifecycle-internal;
- quietness and no-failure compute on the final two Active/EmptyView fibers;
- transition totality is discharged because `R23Key` is empty;
- `IteratorFreeTrace` proves no reachable iterator stage exists: the only
  L-Advance heads start from `Reloading []`, and `ReachableSuffix [] (step ::
  rest)` is impossible;
- `ActualMapsTotalTrace` proves every actual Equation-54 forward generator is
  total without identifying independently stored dictionaries;
- every two effect outputs are `EffectStateRelated` in this concrete model:
  ambient values are `Unit`, and every `CoeffectContext R23Key R23Value` has an
  empty binding list because `R23Key` is uninhabited;
- those facts construct `r23SourceIndependent` directly, including the
  iterator-stability branch by iterator-stage impossibility; and
- provenance, protocol rank, parent-rank, precedence acyclicity, support
  well-foundedness, and support/active matching are derived through the existing
  reached-from-empty theorems.

The final theorem is:

```idris
r23SourceBundle : ReplayInvariantBundle Nat R23Key Unit Unit R23Value
  r23Protocol r23NameEq r23KeyEq r23SourceTrace
```

Thus the authorized next checkpoint—an authenticated source bundle for a quiet,
non-failed, revision-18-applicable internal crossing—is closed.

## 4. First target replay stop

Target transport cannot yet reach `replayQuiet`, because the first suffix head
cannot be constructed through the available generic lifecycle replayer.

The local diamond correctly exposes:

```idris
ControlEquivalent ... sourcePairFinal (swappedFinal diamond)
```

Revision 17 intentionally replaced ordered list controls with this pointwise
relation. `replayRelatedAdvance`, however, is an older Lemma-72 interface and
still consumes:

```idris
OrderedRegistryControlsRelated
  (bindings (registry sourceBefore))
  (bindings (registry replayedBefore))
```

`R23PointwiseAdvanceReplayNegative` attempts the exact first L-Advance replay
using the endpoint's effects, controls, and target well-formedness. It fails at:

```text
Mismatch between: ControlEquivalent ... and OrderedRegistryControlsRelated ...
```

This is not evidence that the target action is unreplayable, and it does not
justify restoring ordered controls to `RelationalReplayEndpoint`. The concrete
L-Advance/empty-program case should be reconstructed from a target lookup via
`controlEquivalentTargetHasSource`/its source-to-target counterpart, the exact
`FiberControlRelated` lifecycle payload, effect relation, and target
well-formedness, analogously to revision 19's checked cross-state retire
producer. Its output must own the checked target transition and next relational
endpoint; ordered list evidence may not be accepted loose.

The strict whole-bundle field order remains intact. No target field is claimed,
because the checked suffix spine itself has not advanced past its first head.
Quietness/no-failure transport is therefore not yet applicable, although the
R22 pointwise lemmas remain sufficient once the suffix endpoint exists.

## 5. Gate status and next work

This phase closes the source checkpoint and stops at a new declaration-free
producer obligation: a pointwise `CheckedCrossStateAdvanceReplay` for the exact
empty-program L-Finish head, followed by the second head and the sealed suffix
spine. Stop if lifecycle/effect/control reconstruction fails; do not add ordered
controls or any desired target invariant as input capital.

The combined A/B/C/D package remains prepared and unissued. No frozen
declaration, O6 body, manifest, production source, package, or CP3 file changes.
The accepted **25–42 shift** band remains honest; this shift closes fixture
selection/source authentication but exposes the pointwise lifecycle replay
bridge before target quietness.
