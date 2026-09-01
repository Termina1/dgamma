# O6 revision 96: operational equal-owner correction; composition still open

## Scope

Design-only grind shift #104 (overall #158) tested the congruence-free
Iter/Retire route and the missing append composition locator. A concrete
executable checked-pair probe discovered that revision 95's ratified eight-cell
equal-owner table was semantically wrong: retirement prevents every paper
activation rule at the same owner. Only Iter/Iter and Retire/Retire are viable in
both checked orders.

The discovery makes the requested Iter/Retire custom RAR unnecessary. Both that
pre-discovery consumer attempt and the append-RAR exact consumer exhausted their
three-attempt probe budgets and were removed. No retained Idris proof changed.

## Make-or-break Iter/Retire consumer verdict

A disposable same-module probe attempted a complete generator locator for a
singleton target L-Iter across retirement:

- target `ActualForwardGenerator` mapped to a canonical source
  `IteratorForwardGenerator`;
- target iterator-forward mapped through the cross-stage family;
- target iterator-yielded mapped through the same correlated source stage.

### Attempt record

1. The canonical target-stage helper reached the actual/iterator equation but
   needed an explicit case analysis of capability resolution and `runStepEffect`.
   The actual branch also needed an explicit source-generator type.
2. The case-split helper then failed at a hidden `rest` index in `OccursHere` and
   at an untyped projected source stage.
3. Those were repaired. The final actual branch stopped at:

```text
case lookupBinding actor (registry targetBefore) of ...
=
traceGeneratorRuntimeMap (traceEffectGeneratorRuntime targetGenerator) state
```

The target `ActualForwardGenerator` retains independently stored decision
objects/runtime fields. Singleton occurrence equality identifies its transition
with the outer transition but does not definitionally identify the runtime map
expression with the canonical outer map.

The unit exhausted and was removed. Marker:

```text
R96_ITER_RETIRE_COMPLETE_GENERATOR_CONSUMER=failed_after_3
```

This failure is no longer an implementation blocker because the operational
probe below excludes Iter/Retire from the paper-step equal-owner family.

## Operational checked-pair probe

`/tmp/R96EqualOwnerOperationalPins.idr` defined:

- an empty dependent key/value universe;
- an empty-dependency/provision component;
- a total no-op step;
- checked states with `Inactive Nothing`, a three-step `Reloading` continuation,
  and an empty `Reloading` continuation;
- `bothOrders`, which runs `checkedApplyAction` in both orders and requires the
  exact paper tag at every step.

All eight revision-95 candidate cells were pinned by `Refl` on attempt 1:

```text
Iter/Iter       = True
Retire/Retire   = True
Begin/Retire    = False
Retire/Begin    = False
Iter/Retire     = False
Retire/Iter     = False
Finish/Retire   = False
Retire/Finish   = False
```

Marker:

```text
R96_EQUAL_OWNER_OPERATIONAL_PINS=passed
```

### Root cause of the revision-95 error

Although O-Retire preserves component, parent, table, lifecycle, and binding
presence, activation applicability is not retirement-flag independent.
`targetFiber` in executable calculus is:

```idris
targetFiber (MkFiber component parent retiredFlag table lifecycle) fibers =
  if retiredFlag then Nothing else resolveView ...
```

Consequences:

- L-Begin after retirement fails because `beginFiberAction` requires
  `targetFiber = Just view`;
- L-Advance after retirement observes a target mismatch and yields L-Divert,
  not the paper L-Iter or L-Finish tag;
- therefore no mixed activation/retirement pair has the required paper tags in
  both orders.

Revision 95 correctly observed that the L-Advance effect map ignores the flag,
but incorrectly promoted map insensitivity to operational rule applicability.
This is an internal proof-route erratum, not a paper-Theorem-73 counterexample.

## Correct exhaustive table

Rule order:

```text
Begin, Iter, Finish, Insert, Retire, Remove
```

| left \\ right | Begin | Iter | Finish | Insert | Retire | Remove |
|---|---:|---:|---:|---:|---:|---:|
| **Begin**  | X | X | X | X | X | X |
| **Iter**   | X | **V** | X | X | X | X |
| **Finish** | X | X | X | X | X | X |
| **Insert** | X | X | X | X | X | X |
| **Retire** | X | X | X | X | **V** | X |
| **Remove** | X | X | X | X | X | X |

Exactly two ordered cells are viable and 34 are excluded.

The earlier semantic exclusions remain valid:

- Insert needs absence and installs the owner;
- Remove deletes the owner;
- Begin changes Inactive to Reloading;
- only repeated Iter can preserve the paper Iter tag in both positions when at
  least three steps remain initially;
- Finish activates the fiber and blocks another activation;
- Retire/Retire remains checked and idempotent.

The current shift supplies executable positive witnesses for both viable cells
and executable negative witnesses for all six formerly disputed mixed cells.
A generic theorem classifying all 36 abstract checked combinations remains to be
proved before implementation.

## Corrected equal-owner RAR design

The equal-owner branch no longer needs cross-retirement payloads or a custom
actual-to-iterator generator mapping.

### Iter/Iter

Both source actions are L-Advance with L-Iter tags, and revision-21 moved
action/tag fields reverse two identical labels. Determinism of
`checkedApplyAction` from the common initial state reindexes:

```text
swappedMiddle = pairMiddle
swappedFinal  = pairFinal
```

After reindexing, build positional singleton RARs with
`activationSingletonRAR` (`438a892`):

- source left against moved right, starting lookup equality `Refl`;
- source right against moved left, after middle reindexing.

Then use ordinary `consRelationalReplayCorrespondence`.

### Retire/Retire

Use the same deterministic endpoint reindexing and positional
`orchestrationSingletonRAR` (`52cbbde`) twice. O-Retire has no iterator stage and
the singleton producer needs no lookup equality.

The `No distinct` branch remains exactly the accepted revision-93 construction.

## Begin/Finish map design status

The revision-95 identity-map designs for Begin/Finish across retirement are now
retired: those mixed paper pairs are operationally impossible. Begin and Finish
continue to use frozen `activationSingletonRAR` in distinct-owner or positional
contexts only.

## Composition locator attempt

A separate disposable same-module probe designed a generic append RAR:

```text
RAR sourceLeft targetLeft ->
RAR sourceRight targetRight ->
RAR (sourceLeft ++ sourceRight) (targetLeft ++ targetRight)
```

The design contains:

1. dependent append-occurrence view (left or right);
2. generator localization for actual, iterator-forward, and iterator-yielded;
3. left/right generator embeddings with exact map equations;
4. stage localization and embeddings with exact outcome equations;
5. `appendRelationalReplayCorrespondenceProbe`, composing the two RARs.

### Attempt record

1. Idris rejected comma-separated implicit lambda patterns in the map consumer.
2. Nested implicit lambda syntax was also rejected by the parser.
3. Replacing them with inferred underscores reached the dependent declarations,
   then generated hidden trace indices failed in the `AppendGeneratorLeft` and
   `AppendStageLeft` constructors. The stage locator also exposed the standard
   actor/selected pattern-name unification issue.

The unit exhausted and was removed. Marker:

```text
R96_APPEND_RAR_EXACT_CONSUMER=failed_after_3
```

The semantic design remains plausible, but the exact consumer type did not
check. Field 9 therefore remains unreachable at this gate.

The next attempt should split the monolithic append package before retrying:

1. fully explicit `AppendLocatedGenerator` with ordinary explicit
   `name,key,world,error,value` arguments and fully specified
   `traceGeneratorMap {trace = left/right}` applications;
2. generator producer and one-elimination consumer as separate units;
3. an independently typed stage package with `selected` used consistently;
4. only then the four-field RAR wrapper.

This follows the successful revision-92 package split and avoids spending the
wrapper's budget on constructor hidden-index failures.

## Field-9 composition slot

Once an append RAR checks, the exact composition is:

```text
prefixRAR = identityRelationalReplayCorrespondence tracePrefix
pairAndSuffixRAR = appendRAR pairRAR sealedSuffixRAR
wholeRAR = appendRAR prefixRAR pairAndSuffixRAR
```

where:

```text
sealedSuffixRAR = sealedSuffixRelationalReplayCorrespondence sealedSuffix
```

The resulting type is exactly:

```text
RelationalReplayCorrespondence original targetTrace
```

needed by field 9 and `traceIndependentAfterRelationalReplaySpike`. This slot is
statement-level compatible but not yet backed by a checked append consumer.

## Capital inventory

Still live and unchanged:

- `04fda32` owner lookup equality transport;
- `e7a7271` L-Advance actor injectivity;
- R92 runtime package, exact consumer, and stage family;
- `438a892` activation singleton RAR;
- `52cbbde` orchestration singleton RAR;
- `JointLocatedConsTargetGenerator` / `JointLocatedConsTargetStage` and
  prepend/widen exactness;
- `84c1b81` identity-prefix RAR;
- sealed suffix RAR;
- R94 Retire/Retire checked countermodel;
- R96 repeated-Iter operational checked witness.

R95 cross-retirement consumer/payload probe designs are valid local stage facts
but no longer needed for equal-owner paper swaps.

## Manifest delta

```text
NO_FROZEN_SURFACE_CHANGE_REQUIRED
```

Expected retained additions remain private quantity-0 CP5 declarations:

- corrected equal-owner classifier;
- deterministic endpoint reindexing;
- equal-owner pair dispatcher;
- split append generator/stage packages and append RAR;
- final decEq pair dispatcher.

No change to revision-21 constructors or the adjacent signature is indicated.

## Status and estimate

- Iter/Retire make-or-break consumer: **exhausted, then rendered unnecessary by
  operational exclusion**;
- executable viable fixtures: **Iter/Iter and Retire/Retire passed**;
- disputed mixed fixtures: **all six excluded by checked evaluator**;
- corrected 2/36 family table: **operationally pinned; generic classifier open**;
- equal-owner RAR design: **simplified to positional frozen singleton RARs**;
- append locator: **designed but exact package/consumer exhausted**;
- field-9 composition: **type-compatible, not checked**;
- field 9, fields 10–15 population, assembly: **unopened**;
- holes: **20**, split **6/4/8/1/1**.

Recommendation: one more narrowly split design-only append-package shift. If its
exact consumer and corrected generic 2-cell classifier check, re-establish a
**2–8 implementation-shift** band. Until then the band remains suspended.

## Isolation

The adjacent interface remains 1183 bytes with SHA
`e6d0c2d669355e5b7bef9efea1707f5853c708deb888bafe5770ba40dbd15a41`.
Production `src/`, `dgamma.ipkg`, CP3 blob
`2c697e532e83989de8591fa6a4378747c6a501c0`, revision-21 surfaces, fields 1–8,
and revision-93 singleton capital are unchanged. No proof hole, postulate,
escape hatch, or Idris source probe is retained.
