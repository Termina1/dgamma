# O6 revision 58: located cons generator package statement gate

## Scope

Shift #66 (overall #120) resumed from accepted revision-57 HEAD `65062c4` and
started the first of the two authorized private located cons packages. The fresh
three-attempt budget for `LocatedConsReplayGeneratorOrigin` was exhausted before
a commit-worthy declaration existed. The final failure recurred through the
located package itself, exactly triggering the revision-57 ruling: stop, revert,
and gate the cons-RAR statement shape rather than iterate.

All generator-package helpers and declarations were reverted. The second
`LocatedConsIteratorStageOrigin` package, cons RAR, occurrence/ordinal/bundle
composition, and final assembly were not opened. The safe retained boundary is
still `65062c4`; the indexed head eliminator and fully instantiated suffix spine
remain intact.

## Intended package

The attempted private record was indexed by:

- exact source and target heads;
- exact source and target tails;
- actor;
- the original whole-target `TraceEffectGenerator`.

Its fields were:

1. the lifted whole-source generator; and
2. universally quantified `PartialMapsRelated` evidence from that source field
   to the record parameter's original whole-target generator.

The producer classified the target generator's `OccursIn` witness into the six
semantic cases:

- actual `OccursHere` / `OccursLater`;
- iterator-forward `OccursHere` / `OccursLater`;
- iterator-yielded `OccursHere` / `OccursLater`.

Singleton generators/stages were widened under the suffix; tail generators and
stages were prepended under the head. Exact executable-map preservation lemmas
for both lifts were constructive.

## Attempt 1: source origin still projected separately

The first version bound:

```text
sourceSingleton = replayGeneratorOrigin headRAR actor targetSingleton
```

and then separately called:

```text
replayGeneratorMapsRelated headRAR observedKeyEq actor targetSingleton
```

inside the cons package constructor. Idris reported the revision-57
correlation wall unchanged:

```text
Can't solve constraint between:
  headRAR .replayGeneratorOrigin actor targetSingleton
and:
  sourceSingleton.
```

Thus merely wrapping the final lifted generator was insufficient; the
singleton/tail RAR itself also had to be opened once.

## Attempt 2: inner RAR elimination clears source, exposes target lift

A private inner `LocatedReplayGeneratorOrigin` was introduced. Its producer
pattern matched `MkRelationalReplayCorrespondence` once and packaged
`origin actor target` with `maps ... actor target` under that same elimination.
The cons package then matched this inner record before lifting the source.

This cleared the source-origin projection constraint. The next exact mismatch
was the target side:

```text
Can't solve constraint between:
  traceGeneratorRuntimeMap
    (traceEffectGeneratorRuntime
      (widenSingletonGenerator targetTail targetSingleton)) y
and:
  partialEffectMapFor nameEq keyEq action tag before y.
```

The package is parameterized by the original whole-target generator from the
caller. Its construction branch independently reconstructs a singleton target
and widens it. Although both have the same action, checked equation, occurrence
region, and proof-free runtime map, Idris does not definitionally identify the
reconstructed target with the original whole-target parameter at the dependent
record constructor.

## Attempt 3: source-only lift still cannot link reconstructed target

The third version stopped widening/prepending the target in the relation.
Source-only map transports related the lifted source directly to the local
singleton/tail target map. This removed the explicit target-lift expression but
the package constructor still had to equate the local reconstructed target with
its original whole-target parameter. The final exact failure was:

```text
Can't solve constraint between:
  traceGeneratorRuntimeMap
    (traceEffectGeneratorRuntime targetSingleton) y
and:
  partialEffectMapFor nameEq keyEq action tag before y.
```

The right-hand side is the executable map of the original whole-target actual
generator fixed by the record parameter; the left-hand side is the map of the
locally reconstructed singleton generator. The proof-free runtime descriptors
are extensionally the same, but their dependent generator owners are not the
same stored value.

This failure occurs *through* the authorized located package after the source
origin and map proof have already been correlated by one RAR elimination. The
three-attempt budget was exhausted. Per the explicit ruling, no fourth
transport, equality field, target cast, specialized record constructor, or
statement widening was attempted.

## Statement-shape question

The current record asks one package to both:

1. classify an already-bound whole-target generator; and
2. reconstruct a singleton/tail target generator against which the head/tail
   RAR is indexed.

Pattern matching proves the occurrence region, but Idris does not retain an
identity between the original target parameter and the reconstructed local
value strongly enough for the map field.

A possible next design, requiring approval, is a two-stage target localization
GADT whose six constructors introduce the *whole target generator itself* and
its exact singleton/tail local form together. The cons-origin package would
consume that localized target under one elimination, then consume the inner RAR
origin/map package under a second elimination. Its result index would remain the
original whole target, but no independently reconstructed target would cross a
record-constructor boundary. The iterator-stage package would use the analogous
localized target-stage GADT.

Another possibility is to change the cons-RAR helper to eliminate each target
generator directly inside the final `MkRelationalReplayCorrespondence` fields,
but that risks repeating the independent-field correlation wall and is not
authorized without a statement-shape review.

Neither representation is implemented or endorsed here. Detached target maps,
caller-provided equalities, UIP, dictionary identity, and public interface
widening remain forbidden.

## Status

- indexed joint GADT: **closed**;
- dependent joint eliminator: **closed**;
- generic suffix spine: **instantiated and closed**;
- `LocatedConsReplayGeneratorOrigin`: **STOP; no declaration retained**;
- `LocatedConsIteratorStageOrigin`: **unopened**;
- whole-suffix RAR: **unopened this shift; still blocked**;
- occurrence/ordinal/bundle composition: **unopened**;
- final adjacent assembly: **unopened**;
- holes: **20**, split **6/4/8/1/1**;
- estimate: accepted **3–15 shift** band held pending the required cons-RAR
  statement-shape gate.
