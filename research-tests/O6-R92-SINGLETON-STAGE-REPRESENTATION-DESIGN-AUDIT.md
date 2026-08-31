# O6 revision 92: singleton-stage representation design campaign

## Scope

Design-only shift #100 (overall #154) resumed from accepted escalation boundary
`a3d397a`. No Idris proof declaration is retained. All probes were appended
transiently to `CP5ConfluenceLocalDiamondSpike.idr`, checked by visible fresh
source elaboration, copied to `/tmp` for inspection, and removed before this
gate. Production, frozen research surfaces, and the adjacent-swap hole are
unchanged.

The objective was to retain the opaque original target `IteratorStage` while
recovering enough exact singleton runtime data to construct
`LocatedSingletonAdvanceStageReplay` without asserting equality with a
reconstructed stage.

## Pinned probes

### Expected failure: exact index identity

The revision-91 failure was reconstructed as
`R92ForbiddenExactStageIdentity`. Its constructor gave both the original stage
and a fully typed rebuilt singleton stage and demanded propositional equality.
Elaboration rejected the equality boundary before generating the constructor:

```text
Can't solve constraint between: ?actor and selected
```

After actor reindexing, the already pinned revision-91 form reaches the sharper
failure:

```text
targetStage
vs
StageFromAdvance nameEq keyEq actor tag checked OccursHere ...
```

Thus a full type ascription makes the equality well-shaped only after actor
transport; it does not make the opaque original stage definitionally identical
to a reconstructed value.

Pin: `/tmp/grind154-b-exact-identity-negative.log`

Result: **expected failure passed**.

### Candidate (c) positive half: opaque header observations

`R92OpaqueSingletonAdvanceHeader` kept `targetStage` only as an index and stored
no reconstructed stage. Its constructor explicitly quantified the full opaque
stage type and owned two erased observations:

```text
selected = actor
r92IteratorStageTag targetStage = tag
```

The producer eliminated `StageFromAdvance`, called
`viewConsStageOccurrence occurs`, constructed both equalities by `Refl` in the
Here case, and eliminated Later via `noOccurrenceInEmpty`. It checked.

Pin: `/tmp/grind154-c-opaque-header-positive.log`

Result: **expected success passed**.

### Candidate (c)/(d) negative half: header/outcome alone is insufficient

A consumer using only actor/tag observations and the opaque target stage still
could not feed the frozen `locateSingletonAdvanceStageReplay`. Once the target
stage was eliminated, Idris correctly distinguished the source checked result
at outer `tag` from the payload's `stageTag`. Direct occurrence and projected
transition-tag eliminations did not preserve the opaque target index and exact
payload simultaneously:

```text
Mismatch between: stageTag and tag.
```

Pins:

- `/tmp/grind154-c-opaque-consumer-positive.log`
- `/tmp/grind154-c-tag-projection-consumer.log`

This also rejects candidate (d) as a standalone observational-outcome package:
the frozen delegate additionally requires exact component, owner lookup,
lifecycle, continuation, accumulator, view, step, rest, and suffix. An outcome
observation cannot synthesize those inputs. Supplying them turns (d) into the
runtime package of candidate (a).

Result: **expected failure passed**.

### Selected candidate (a): producer-indexed runtime package

`R92SingletonAdvanceRuntimePackage` follows the validated revision-71
candidate-1 shape. It is indexed by the original opaque `targetStage` and stores
only producer-owned data, all at quantity 0 in the final probe:

- `selected = actor`;
- component, parent, retired flag, owned table;
- remaining steps, accumulator, dependency view;
- exact target owner lookup under the outer `nameEq`;
- current step, rest, and reachable suffix;
- exact runtime outcome equality from the opaque target stage to an exact
  singleton descriptor assembled from those payload fields.

The package never stores or proves stage equality. Its producer eliminates the
stage once, uses `viewConsStageOccurrence`, exposes the exact fiber/lifecycle,
and constructs the runtime outcome equality by `Refl`. Later is empty.

A separate exact consumer was checked. It eliminates the package constructor
once, cases on its owned actor equality, uses frozen
`singletonAdvanceSourceFoundFromOwnerLookup` (`04fda32`), and constructs the
required source stage plus `MkLocatedSingletonAdvanceStageReplay` from the
package-owned outcome equality. Its result type is exactly:

```text
LocatedSingletonAdvanceStageReplay name key world error value
  (MoreTransitions sourceAdvance NoTransitions)
  (MoreTransitions movedAdvance NoTransitions)
  selected targetStage
```

The original opaque `targetStage` remains the result index throughout. The
consumer neither reconstructs it nor passes it through the frozen locator.

Pins:

- `/tmp/grind154-a-runtime-package-consumer-positive3.log`
- `/tmp/grind154-selected-erased-package.log`
- source snapshot `/tmp/grind154-selected-erased-probe.idr`

Result: **producer and exact one-elimination consumer passed**.

## Candidate comparison

| Candidate | Positive direction | Negative direction | Verdict |
|---|---|---|---|
| (a) Producer-indexed runtime package | Package producer and exact quantity-0 one-elimination consumer check. Opaque stage remains an index; payload/outcome are producer-owned. | Omitting explicit `OccursHere {rest = NoTransitions}` or exact `before/afterState` recreates generated dependent implicit failures, now pinned. | **SELECTED.** |
| (b) Explicit original stage + full type ascription | Full stage type can be stated explicitly. | Equality constructor fails at actor index before transport; after transport, original stage still differs from the rebuilt `StageFromAdvance`. | Reject. |
| (c) Opaque singleton occurrence/header GADT | Actor and tag observations check while stage remains opaque. | Header lacks exact normalized lookup/lifecycle payload needed by the frozen delegate; exact consumer stops at `stageTag`/`tag`. | Useful sub-pattern, insufficient alone. |
| (d) Observational outcome package | Outcome equality is sufficient only after exact runtime payload is also owned. | Frozen `locateSingletonAdvanceStageReplay` consumes payload and exact lookup, not merely outcome; pure observational package cannot call it. | Collapses into (a); reject standalone. |

## Frozen-capital inventory

| Capital | Candidate (a) use | Other candidates |
|---|---|---|
| `singletonAdvanceSourceFoundFromOwnerLookup` (`04fda32`) | **Consumed by exact consumer** to transport the producer-owned moved lookup to the source. | (c)/(d) cannot use it without normalized target payload. |
| `lAdvanceActorInjective` (`e7a7271`) | Not needed: Here constructs `selected = actor` directly under the checked occurrence view. Retained unchanged as valid fallback capital, not removed. | (b) needs actor transport but still fails stage identity. |
| `locateSingletonAdvanceStageReplay` | **Not consumed.** Its equal-tag/exact-payload input shape is the reason header/outcome-only candidates fail. The selected consumer constructs the same public result record directly and honestly. | (c)/(d) fail when attempting to use it. |
| `viewConsStageOccurrence` | **Consumed by producer.** Here provides exact singleton payload; Later is eliminated by `noOccurrenceInEmpty`. | Core of (c); insufficient without payload package. |
| `singletonNonAdvanceRAR` | Not part of the LAdvance package. Remains the subsequent LBegin and orchestration route after the stage family closes. | Unchanged. |
| `SingletonAdvanceStageReplayFamily` / `singletonAdvanceRAR` | Exact consumer result has precisely the family field type; expected downstream consumers remain unchanged. | Unchanged. |

## Manifest delta

Expected implementation delta is internal to
`research/DGamma/CP5ConfluenceLocalDiamondSpike.idr`:

1. a private singleton runtime package with all proof fields quantity 0;
2. a private checked producer;
3. a private exact one-elimination consumer;
4. the already authorized one-clause family wrapper.

`NO_FROZEN_SURFACE_CHANGE_REQUIRED`.

No change is required to:

- `IteratorStage`;
- `LocatedSingletonAdvanceStageReplay`;
- `locateSingletonAdvanceStageReplay` (retained but bypassed for this internal
  producer-owned path);
- `RelationalReplayCorrespondence` or revision-20 map/RAR surfaces;
- `LocalRelationalDiamond`, revision-21 classifiers or safety fields;
- `adjacentSwapSuffixSpike` (1183 bytes, frozen SHA);
- production `src/`, `dgamma.ipkg`, or CP3.

## Recommended implementation order

Give each unit its own fresh budget:

1. private `SingletonAdvanceRuntimePackage` plus its Here/Later producer, copied
   from the quantity-0 checked probe with explicit `OccursHere {rest =
   NoTransitions}` and exact `StageFromAdvance {before} {afterState}` indices;
2. exact package consumer producing
   `LocatedSingletonAdvanceStageReplay` directly, using `04fda32`;
3. one-clause `SingletonAdvanceStageReplayFamily` wrapper;
4. resume the accepted singleton RAR, moved-pair RAR, three-leg whole RAR,
   field-9, fields-10–15, and assembly chain.

Do not revive stage equality, tag-only transport, or a call to the frozen
locator from this selected path.

## Proposed band

Re-establish **2–10 implementation shifts**:

- one shift minimum for the selected package/consumer/family boundary under
  commit-by-unit discipline;
- one or more shifts for singleton RARs, moved-pair/whole RAR, bundle population,
  and final assembly;
- ten remains the prior accepted upper bound because no frozen surface changed
  and all semantic payload/outcome obligations for the new boundary are now
  checked.

The estimate remains subject to the existing stop-audit and body-closure review
boundaries.

## Status

- selected representation: **candidate (a), checked**;
- exact one-elimination consumer: **checked**;
- expected-failure pins: **checked**;
- retained Idris proof changes: **none**;
- frozen surface delta: **none**;
- holes: **20**, split **6/4/8/1/1**;
- field 9 and assembly: **still unopened pending design approval**.
