# O6 revision 125: joint occurrence design campaign audit

## Scope and coordinate

Design-only shift #123 (overall #177) started from accepted clean HEAD
`6db4d680437b3f13c7c6803a527aeb9948bfeaa2`. It used only exact renamed
copies of `CP5ConfluenceLocalDiamondSpike.idr` under `research-tests/`. No proof
code was added to the real CP5 module. All disposable sources and TTC/TTM files
were removed before this audit was retained.

The campaign followed the authorized ladder in order:

1. a joint prefix/target-occurrence shape with full four-region recursion;
2. after that representation failed at its recursive lift boundary, a shape
   indexed by the original occurrence and its ordinal, whose constructors
   introduced the lifted occurrence directly.

Neither design checked. Per the two-failure binding, no third representation was
forced and no retained-unit design is ratified.

## Probe 1: joint shape plus four-region recursion

The exact-copy probe declared:

- `ProbeJointPrefixOccurrenceShape`, indexed by the exact prefix, exact target
  tail, action, and original target `LocatedActionOccurrence`;
- empty, prefix-head, and prefix-later constructors;
- a recursive four-region view with prefix, moved-right, moved-left, and suffix
  constructors;
- a recursive producer consuming the joint shape once; and
- a one-elimination consumer returning an exact target ordinal.

The prefix-later constructor attempted to own all four requested correlations:

- prefix head/tail;
- exact first target transition via the stored prefix equation;
- tail-global located occurrence;
- original-to-one-step-lifted occurrence equation, plus tag and ordinal
  equalities.

### Attempt history

1. **Infrastructure:** Idris could not infer the action index at
   `ProbeJointHere`; the suffix helper also projected an action-before state
   after discarding its dependent pattern.
2. **Infrastructure:** making action and occurrence explicit exposed constructor
   declaration order: `prefixHead` had already been auto-bound before its later
   explicit binder.
3. **Semantic:** after ordering every explicit binder, the intended homogeneous
   equation was itself ill-typed:

```text
Mismatch between:
  jointOccurrence .actionBeforeState
and:
  tailOccurrence .actionBeforeState
```

The two independently stored located occurrences existentially own their action-
before states. Therefore

```idris
beforeActionOccurrence jointOccurrence =
  MoreTransitions prefixHead (beforeActionOccurrence tailOccurrence)
```

cannot even be stated as ordinary equality until those endpoint indices are
introduced as the same state. This is stronger than the revision-124 proof-
token mismatch: the proposed glue proposition is heterogeneous at the type
level.

## Probe 2: original-occurrence and ordinal indexed shape

The fallback `ProbeJointIndexedOccurrence` indexed the shape by both:

- the complete original located occurrence; and
- its exact `locatedActionOrdinal`.

Its `Here` constructor built the whole and prefix-local occurrences from shared
fields. Its `Later` constructor built the whole occurrence directly as the
one-step lift of a tail occurrence, making the lifted equation a constructor
index rather than a theorem to recover. A recursive one-elimination consumer
attempted to return the exact target ordinal.

The disposable fallback had SHA-256
`d71912d78dcc27693863bb9331f0199ba1ce1932fb4bce5d51836403c3fc770f`
before removal.

### Semantic result

The producer reached the `Later` constructor but could not supply the tail
occurrence at the caller's exact tail trace:

```text
When unifying:
  appendTransitions prefixTail targetTail
and:
  appendTransitions tailBefore (MoreTransitions located tailAfter)
Mismatch between:
  targetTail
and:
  MoreTransitions located tailAfter
```

The whole occurrence decomposition proves equality only after both traces have
been prefixed by a dependent head. Removing that head requires simultaneously
transporting the intermediate state index. Ordinary `Equal` and a separately
constructed tail `LocatedActionOccurrence` do not retain that dependent tail
identity. Indexing by the final ordinal does not repair the lost state index.

## Countermodel-style boundary analysis

The obstruction is representational, not a missing arithmetic fact.
`Transitions` is indexed by both initial and final states. A whole equality

```idris
MoreTransitions h xs = MoreTransitions h ys
```

conceptually determines `xs = ys`, but if `xs` and `ys` were formed through
independently stored existential intermediate states, the desired equality is
heterogeneous before the head equality has reindexed those states. Neither:

- an equation between projections of two independently stored located
  occurrences; nor
- a constructor indexed by an already reconstructed tail occurrence

can introduce this correlation retroactively.

The only plausible next representation must make the **cursor fields**, not two
pre-existing `LocatedActionOccurrence` records, primitive constructor data:

- one shared `actionBefore` and `actionAfter` state;
- the exact located transition and action equation;
- exact tail-before and tail-after traces;
- the prefix head/tail;
- and one dependent whole decomposition whose constructor result builds both
  the whole occurrence and tail occurrence from those shared fields.

In other words, a future candidate must be a cursor/spine GADT whose constructor
result contains both occurrences definitionally. It must not accept either
occurrence as an independent input. This candidate was not authorized after both
campaign probes failed and remains untested. There is no ratified retained-unit
signature at this gate.

## Probe markers and disposal

No success marker was emitted. The honest markers are:

```text
R125_JOINT_OCCURRENCE_SHAPE=failed_after_3
R125_JOINT_INDEXED_SHAPE=semantic_failure
R125_DISPOSABLE_PROBES_REMOVED=passed
R125_RETAINED_DESIGN=not_ratified
```

A malformed shell invocation between probe-1 attempts rebuilt CP5 and then
failed on an unknown command-line flag before invoking the disposable probe. It
is not counted as a probe attempt and produced no semantic or elaboration
result.

## Status

- joint-shape probe: **failed after two infrastructure attempts and one semantic
  attempt**;
- occurrence+ordinal indexed fallback: **semantic failure**;
- cursor/spine alternative: **identified, not tested or authorized**;
- retained proof edits: **none**;
- four-region view/action origin/correspondence/fold/result/body: **unopened**;
- all frozen #121 and earlier capital: **unchanged**;
- holes: **20**, split **6/4/8/1/1**.
