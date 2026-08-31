# O6 revision 85: field-8 totality transport foundations and correlated stop

## Scope

Grind shift #93 (overall #147) resumed from reviewer-accepted revision 84 at
`e51f630`. It opened only field 8 (`TraceComponentsTotal`) and retained two
lemma-sized foundations. The next one-transition transport unit exhausted its
fresh three-attempt budget and was removed. No field 9–15 or assembly unit was
opened.

## Retained foundations

### Binding lookup presence

`pointwiseLookupBindingPresenceFromBindings` passed on its first fresh attempt
at `87d814c`. Given exact ordered binding-list equality between two dependent
coeffect contexts, it transports the executable `isJust (lookupBinding ...)`
predicate without identifying erased uniqueness certificates.

### Active provision totality

`pointwiseActiveFiberProvidesAll` passed on attempt 3 at `a141f66`:

- the single `FibersControlRelated` elimination retains the shared component;
- `relatedLocatedFiberTablesSame` obtains exact owned-table binding equality
  from located fibers plus `EffectStateRelated`;
- the lookup-presence helper transports each provision-key lookup;
- the resulting `ActiveFiberProvidesAll` proof is constructive and
  actor-local.

Attempts 1–2 were statement-layout failures in erased local equality
annotations (`Bool`/`Type`, then binding-list/`Type`); parenthesizing the entire
`Equal` propositions produced the checked proof. All proof locals are quantity
0.

## Exhausted one-transition unit

The removed `pointwiseTransitionComponentTotal` attempted to transport one
`TransitionComponentTotal` through:

- equal replay/source actions;
- a producer-owned `RelationalReplayEndpoint` between their after-states;
- source transition totality.

Its body recovered the target actor's source fiber through symmetric pointwise
controls, reindexed the source lookup using `cong actionOwner sameAction`, and
prepared to apply the retained active-provision transport.

Attempts:

1. the erased local `sameOwner` equality needed proposition parentheses;
2. the dependent source lookup and source-active equalities needed the same
   statement-level parentheses;
3. elaboration advanced to lifecycle activity transport, then an independently
   reopened case elimination on `targetSourceRelated` lost the exact target and
   source fiber correlation:

   ```text
   Mismatch between: targetFiber and sourceFiber.
   ```

The entire one-transition unit was removed after budget exhaustion. The two
prior foundations remain.

## Exact next cure

Add a separate private correlated projection:

```idris
0 fiberControlActiveSame :
  (leftFiber, rightFiber : Fiber ...) ->
  FiberControlRelated leftFiber rightFiber ->
  isActive (fiberLifecycle leftFiber) =
    isActive (fiberLifecycle rightFiber)
```

Its implementation must eliminate exactly one
`FibersControlRelated` and immediately call the already checked
`pointwiseLifecycleActiveSame`; no independently reopened lifecycle/fiber case.
Then retry the one-transition transport using
`fiberControlActiveSame targetFiber sourceFiber targetSourceRelated` to derive
the source activity proof.

After that closes, field 8 should proceed in the accepted decomposition:

1. append-split source totality into prefix, pair, and suffix;
2. retain prefix totality unchanged;
3. transport the moved pair at its exact checked boundaries using producer-owned
   moved-pair capital and the one-transition theorem;
4. recurse over `SealedSuffixReplaySpine`, using each `headEndpoint` and
   `sameAction` before rebuilding `TraceComponentsTotalStep`;
5. append the three target pieces and populate private bundle field 8.

## Status

- fields 1–7: **closed and frozen**;
- field 8 lookup/table transport foundations: **closed and retained**;
- field 8 one-transition transport: **not retained**;
- field 8 trace decomposition/fold/package field: **unopened**;
- fields 9–15: **unopened**;
- final result/body assembly: **unopened**;
- holes: **20**, split **6/4/8/1/1**.

The accepted remaining band is **held at 1–10 shifts** because field 8 is only
partially developed.

## Isolation

The frozen 1183-byte spike interface and SHA, fields 1–7, revisions 19–21,
registration/yield/generator/RAR capital, production `src/`, `dgamma.ipkg`, and
CP3 remain unchanged. No hole, postulate, escape hatch, detached caller premise,
public surface, package input, or independently supplied replay capital was
added.
