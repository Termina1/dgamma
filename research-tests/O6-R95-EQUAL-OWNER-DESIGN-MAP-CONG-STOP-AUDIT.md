# O6 revision 95: equal-owner design reaches retired-flag map wall

## Scope

Design-only grind shift #103 (overall #157) investigated the equal-owner half of
the pair RAR after revision 94 refuted global owner separation. No retained Idris
proof edit was made. Disposable probes established the finite family table, the
exact one-elimination L-Advance stage consumer across retirement, and lookup
payload producers in both retirement orientations. The first attempted actual
L-Advance map-congruence helper exhausted its three-attempt budget at the
retired-flag normalization boundary, so the design campaign stopped before a
full singleton or pair RAR and before the field-9 composition-slot probe.

## Top-level selected shape

The pair producer must split:

```text
case decEq @{nameEq} (actionOwner leftAction) (actionOwner rightAction) of
  No distinct => accepted revision-93 path
  Yes sameOwner => equal-owner classifier and action-specific RAR
```

The `No` branch is unchanged:

1. `transitionForeignLookup` frames the right owner across source left and the
   left owner across moved right;
2. `activationSingletonRAR` (`438a892`) and
   `orchestrationSingletonRAR` (`52cbbde`) construct singleton RARs;
3. `JointLocatedConsTargetGenerator` and `JointLocatedConsTargetStage` feed the
   cross-cons producer (target Here: right singleton plus source-left prepend;
   target Later: left singleton plus source-right widening).

No distinctness is projected from `TraceIndependent`.

## Exhaustive equal-owner family table

The disposable module `/tmp/R95EqualOwnerEnumeration.idr` defined exactly six
paper rule classes in this order:

```text
Begin, Iter, Finish, Insert, Retire, Remove
```

and normalized all 36 ordered combinations. `exhaustiveMatrix = Refl` checked on
attempt 1; the list comprehension count of excluded cells reduced to 28.

Legend: `V` = viable in both checked orders, `X` = excluded.

| left \\ right | Begin | Iter | Finish | Insert | Retire | Remove |
|---|---:|---:|---:|---:|---:|---:|
| **Begin**  | X | X | X | X | **V** | X |
| **Iter**   | X | **V** | X | X | **V** | X |
| **Finish** | X | X | X | X | **V** | X |
| **Insert** | X | X | X | X | X | X |
| **Retire** | **V** | **V** | **V** | X | **V** | X |
| **Remove** | X | X | X | X | X | X |

The eight ordered viable cells are therefore:

```text
Iter/Iter
Retire/Retire
Begin/Retire, Iter/Retire, Finish/Retire
Retire/Begin, Retire/Iter, Retire/Finish
```

Individual forward/backward `Refl` pins checked for each mixed retirement pair,
plus repeated Iter and repeated Retire.

### Semantic justification of excluded rows/cells

The table is not inferred from the false separation claim:

- O-Insert requires the owner absent and installs it. Every other paper rule
  requires the owner present; a second same-owner insert fails. Therefore no
  insert-involving pair checks in both orders. O/O safety independently rules
  out insert/insert via its inserted-child distinctness function.
- O-Remove requires a present retired inactive owner and deletes it. A following
  activation/retire/remove lacks the owner; a following insert makes the reverse
  insert-first order fail. Therefore no remove-involving pair checks both ways.
- O-Retire preserves component, parent, table, lifecycle, and presence while
  setting only the flag. Activation does not test the retirement flag, so all
  three activation/retire orientations are viable. Retire/retire is idempotent.
- L-Begin requires `Inactive Nothing` and leaves `Reloading`; it therefore cannot
  commute with another activation.
- L-Iter requires a nonempty `Reloading` continuation and consumes its head. Two
  Iter steps are viable when at least two steps remain. Iter/Finish is not
  reversible because Finish requires an empty continuation before it runs.
- L-Finish makes the owner Active; no following paper activation succeeds.

The operational positive fixtures for all eight cells were not completed before
the later map-helper stop. Revision 94 already supplies the Retire/Retire
executable countermodel. Repeated-Iter and mixed activation/retire remain a
required positive fixture campaign rather than frozen proof capital.

## Independent A/A re-verification

The blanket statement “same-owner Begin/Iter/Finish cannot be checked in both
orders” is **false**. The checked A/A submatrix is:

| left \\ right | Begin | Iter | Finish |
|---|---:|---:|---:|
| Begin  | X | X | X |
| Iter   | X | **V** | X |
| Finish | X | X | X |

Only repeated L-Iter survives. This matters because L-Iter and L-Finish share
`LAdvance`; action equality alone is insufficient, and the equal-owner
classifier must retain exact tags.

## Checked cross-retirement L-Advance stage design

A disposable copy of the CP5 module checked the exact consumer:

```text
consumeSingletonAdvanceRuntimePackageAcrossRetireProbe
```

on attempt 1. Its zero-hidden signature preserves the original
`selected,targetStage` indices. It takes:

1. exact source and moved L-Advance checked equations;
2. a quantity-0 `sourcePayload` producer which, for the component/parent/table/
   continuation payload exposed by one elimination of the target
   `SingletonAdvanceRuntimePackage`, returns an existential source retirement
   flag and exact source owner lookup;
3. the original target stage and package.

The body eliminates `MkSingletonAdvanceRuntimePackage` exactly once, eliminates
`selected = actor`, calls `sourcePayload`, and constructs the source
`StageFromAdvance` plus `MkLocatedSingletonAdvanceStageReplay` directly. The
existing `targetOutcomeExact` typechecks unchanged even though source and target
retirement flags differ, proving that iterator outcome does not observe the
flag.

Marker:

```text
R95_CROSS_RETIRE_ADVANCE_ONE_ELIM_CONSUMER=passed
```

No stage equality or dictionary equality is used.

## Checked source-payload producers in both orientations

Two disposable producers checked against exact O-Retire equations:

1. `sourcePayloadAfterCheckedRetireProbe` — Retire/Activation orientation,
   attempt 1. Target activation starts before retirement; source activation
   starts after it. `retireSuccessView`, exact original lookup, and
   `localLookupReplaceSelfO5` construct source lookup with retired flag `True`.
2. `sourcePayloadBeforeCheckedRetireProbe` — Activation/Retire orientation,
   attempt 2. Source activation starts before retirement; target activation
   starts after it. The target lookup is compared with the exact replacement
   lookup, then the old fiber is eliminated before the equality to preserve
   dependent view indices.

Markers:

```text
R95_RETIRE_ACTIVATION_SOURCE_PAYLOAD=passed
R95_ACTIVATION_RETIRE_SOURCE_PAYLOAD=passed
```

Together with the one-elimination consumer, these close the iterator-stage and
exact-outcome half for both mixed orientations and for both Iter and Finish tags.

## Stop: actual L-Advance map congruence across retirement

`singletonAdvanceRAR` also requires `PartialMapsRelated` for the actual forward
transition maps. The attempted helper stated that two exact owner lookups,
`Just fiber` and `Just (retireFiber fiber)`, induce equal
`advanceRuntimeEffectMap`s.

Attempt 1 used direct reduction after rewriting both lookups and failed:

```text
Mismatch between: True and retiredFlag.
```

Attempt 2 factored a fiber-level equality but hit the same mismatch. Attempt 3
split the flag into `False` and `True`; the `False` clause still failed because
Idris retained the opaque `fiberLifecycle (retireFiber ...)`/`fiberComponent
(retireFiber ...)` observations rather than reducing them:

```text
Mismatch between: True and False.
```

The helper and all disposable probe files were removed at budget exhaustion. No
fourth normalization cure was attempted.

This is an elaboration route wall, not a semantic counterexample: the definition
of `fiberAdvanceRuntimeEffectMap` observes lifecycle/component but not the
retirement flag.

## Recommended next design route

Do **not** immediately retry the exhausted congruence helper. A better RAR design
avoids requiring actual-to-actual L-Iter map congruence:

- **Begin/Retire:** L-Begin actual maps are identity and have no iterator stages;
  use a direct non-advance RAR.
- **Finish/Retire:** successful Finish has an empty continuation; its actual map
  is identity and it has no reachable iterator stage. Use a direct non-advance-
  style RAR after an exact empty-continuation observation.
- **Iter/Retire:** map the target actual L-Iter generator to the source
  `IteratorForwardGenerator` produced by the checked cross-retirement stage
  consumer. The iterator forward outcome is the same step map as the actual
  L-Iter map. Target iterator forward/yielded generators use the same correlated
  source stage. This avoids normalizing `retireFiber` under the opaque imported
  map function.
- **Iter/Iter:** actions and tags coincide positionally. Determinism reindexes
  moved middle to source middle; use the frozen activation singleton RAR at each
  position with reflexive starting lookup, then ordinary cons RAR.
- **Retire/Retire:** use the frozen orchestration singleton RAR positionally at
  each step; it requires no lookup equality.

The next design shift should prove the complete custom Iter/Retire singleton RAR
consumer, including target **actual**, iterator-forward, and iterator-yielded
origins, before any retained implementation.

## Composition-slot status

Not checked because the map helper exhausted first. The expected field-9 type
remains:

```text
RelationalReplayCorrespondence original targetTrace
```

with three structural regions:

1. identity prefix (`84c1b81`);
2. decEq-split pair RAR;
3. `sealedSuffixRelationalReplayCorrespondence`.

A generic append-RAR helper is not present in frozen capital. The next design
must check either:

- a producer-correlated append RAR with target prefix/suffix localization; or
- a single whole locator that classifies target generators/stages into identity
  prefix, moved pair, or sealed suffix and then applies prepend/widen exactness.

Consequently field-9 composition compatibility is **not yet proved**.

## Capital inventory and manifest delta

Usable frozen capital:

- `04fda32` — exact lookup transport when lookup equality genuinely holds;
- `e7a7271` — L-Advance actor injectivity;
- `8eecfc7`/`2d71e0f`/`5a21dd3` — runtime package, exact consumer, stage family;
- `438a892` — activation singleton RAR;
- `52cbbde` — orchestration singleton RAR;
- `JointLocatedConsTargetGenerator` / `JointLocatedConsTargetStage` and
  prepend/widen map/outcome exactness;
- `84c1b81` — identity prefix RAR;
- `sealedSuffixRelationalReplayCorrespondence`;
- R45 concrete checked retirement fixture and revision-94 idempotent-retire
  countermodel.

Expected manifest delta remains:

```text
NO_FROZEN_SURFACE_CHANGE_REQUIRED
```

Required additions, if the next design is ratified, are private quantity-0 CP5
helpers: equal-owner classifier, cross-retirement advance RAR, pair dispatcher,
and whole append/localization machinery. No revision-21 constructor or adjacent
signature change is indicated.

## Status and estimate

- 36-cell equal-owner table: **checked as a finite type-level enumeration**;
- semantic exclusions: **analyzed; generic proof pins not yet retained**;
- blanket A/A exclusion: **refuted; only Iter/Iter viable**;
- cross-retire exact stage consumer: **checked**;
- both lookup-payload orientations: **checked**;
- actual map half / complete singleton RAR: **open at exhausted route**;
- pair RAR and composition slot: **unopened**;
- field 9, fields 10–15 population, assembly: **unopened**;
- holes: **20**, split **6/4/8/1/1**.

Recommendation: one further design-only shift for the actual-to-iterator
L-Iter route, complete viable fixtures/exclusions, and append composition slot.
If it checks, re-establish a **3–10 implementation-shift** band. Until then the
previous **2–10** band remains suspended.

## Isolation

The adjacent interface remains 1183 bytes with SHA
`e6d0c2d669355e5b7bef9efea1707f5853c708deb888bafe5770ba40dbd15a41`.
Production `src/`, `dgamma.ipkg`, CP3 blob
`2c697e532e83989de8591fa6a4378747c6a501c0`, revision-21 surfaces, fields 1–8,
and revision-93 singleton capital are unchanged. No proof hole, postulate,
escape hatch, or Idris source probe is retained.
