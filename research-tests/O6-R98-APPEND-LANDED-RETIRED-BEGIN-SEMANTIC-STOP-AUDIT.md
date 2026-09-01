# O6 revision 98: append landed; retired-Begin exclusion semantic stop

## Scope

Implementation shift #106 (overall grind #160) resumed from `0122c7d` under
the accepted two-track ruling.

- Track A retained the entire ratified R97 append chain, one fresh checked commit
  per unit.
- Track B retained its first raw-retirement projection unit.
- Track B2 exhausted its independent three-attempt budget at the dependent
  boundary between an exact post-retirement lookup and a let-bound raw
  L-Begin equation. The whole B2 unit was removed immediately.

The semantic-stop rule therefore ended the shift before B3 or any pair-RAR,
field, or assembly work began.

## Track A retained status

### A1 — generator package and producer

Commit `ace6ff4` retains:

- exact left/right occurrence embeddings over `appendTransitions`;
- the fully explicit `R97AppendOccurrenceView`;
- total append occurrence classification;
- `R97AppendGeneratorPackage`;
- `r97LocateAppendGenerator`, covering actual-forward, iterator-forward, and
  iterator-yielded origins.

Fresh direct CP5 and R16 checks passed before commit.

### A2 — three-constructor consumer

Commit `b946575` retains `r97ConsumeAppendGenerator`, the checked
one-elimination consumer for the package established by A1.

Fresh direct CP5 and R16 checks passed before commit.

### A3 — stage package, producer, and consumer

Commit `ce8d357` retains:

- `R97AppendStagePackage`;
- `r97LocateAppendStage`;
- `r97ConsumeAppendStage`.

Fresh direct CP5 and R16 checks passed before commit.

### A4 — producer-owned mapped generator and mapped stage

Commit `be0a439` retains:

- source generator/stage occurrence embeddings and exact map/outcome equations;
- the left/right map-relation consumers;
- `R97MappedAppendGenerator`, whose source generator is independent of the
  observer dictionary while its proof is quantified over
  `(observedKeyEq : DecEq key)`;
- `r97MapAppendGenerator`;
- `R97MappedAppendStage` and `r97MapAppendStage`.

This is the retained cure for repeated locator elimination. No dictionary
identity or detached map premise is introduced.

Fresh direct CP5 and R16 checks passed before commit.

### A5 — generic append RAR

Commit `62dd49d` retains:

```idris
r97AppendRelationalReplayCorrespondence :
  RAR sourceLeft targetLeft ->
  RAR sourceRight targetRight ->
  RAR (sourceLeft ++ sourceRight) (targetLeft ++ targetRight)
```

Both generator and stage projections come from the same producer-owned mapped
package used by the corresponding proof field.

Fresh direct CP5 and R16 checks passed before commit.

### A6 — exact field-9 composition

Commit `a44d184` retains:

- `r97Field9WholeAppendCorrespondence`;
- `r97Field9ConcreteCapitalConsumer`.

The concrete consumer uses exactly:

```text
identityRelationalReplayCorrespondence tracePrefix
pairRAR
sealedSuffixRelationalReplayCorrespondence seal
```

and returns the whole:

```idris
RelationalReplayCorrespondence original
  (appendTransitions tracePrefix
    (MoreTransitions (movedRight diamond)
      (MoreTransitions (movedLeft diamond) replayedSuffix)))
```

Fresh direct CP5 and R16 checks passed before commit.

**Track A is fully retained and closed.**

## Track B retained status

### B1 — raw retirement projection

Commit `e61f5ed` retains the producer-owned indexed family:

```idris
R97CheckedRetireProjection ... before afterState tag checked
```

Its sole constructor fixes, in one elimination:

- `before = MkSystemState ambient source`;
- `tag = ORetireTag`;
- the old fiber and its exact source lookup;
- `afterState = MkSystemState ambient
    (replaceBinding actor (retireFiber oldFiber) source)`;
- the exact checked retirement equation at those indices.

`r97ProjectCheckedRetire` projects `checkedApplyAction` to `applyAction` before
calling `retireSuccessView`, as required by the revision-97 ruling.

It checked on attempt 1. Fresh direct CP5 and R16 checks passed before commit.

## B2 stop: retired Begin exclusion

### Intended statement

The removed unit attempted the honest generic statement:

```idris
lookupFiber actor source = Just oldFiber ->
checkedApplyAction (LBegin actor)
  (MkSystemState ambient
    (replaceBinding actor (retireFiber oldFiber) source)) =
  Just (LBeginTag, afterState) -> Void
```

It destructured `oldFiber`, constructed the exact replaced-owner lookup, and
projected the checked L-Begin equation through `checkedActionProjects` before
lifecycle analysis.

### Attempt record

1. An inferred erased `let 0 raw = checkedActionProjects ...` crossed the
   dependent boundary without a fully explicit type. Idris reported:

   ```text
   No type declaration for ... fromInteger.
   ```

2. The raw `applyAction` equation was given a fully explicit type. Rewriting the
   exact replaced-owner lookup around the result did not affect the expected
   goal because Idris does not rewrite the type of the already let-bound raw
   equality:

   ```text
   Rewriting by lookupFiber ... = Just ... did not change type Void.
   ```

3. Replacing `rewrite` with `case afterFound of Refl =>` still did not reindex
   the independently let-bound raw equation. Idris rejected the final equality
   case as non-impossible:

   ```text
   ... is not a valid impossible case.
   ```

All attempts count. The B2 budget exhausted and the full uncommitted unit was
removed. No B3/B4/B5/B6 work started.

Marker:

```text
GRIND160_B2_RETIRED_BEGIN=failed_after_3
```

### Semantic diagnosis

Projecting `checkedApplyAction` first is necessary but not sufficient. The raw
equation and exact owner lookup must be produced under one dependent elimination;
storing them in separate let bindings reproduces the same correlation failure
that revision 97 solved for append generators.

This is a producer-correlation semantic boundary, not evidence that L-Begin is
possible after retirement. The R96 executable fixture remains the operational
countercheck.

### Recommended next design

Do not retry the removed shape. A design-only package should correlate:

- the post-retire registry;
- the exact lookup of `retireFiber oldFiber`;
- `targetFiber (retireFiber oldFiber) postRegistry = Nothing`;
- the exact normalized raw result of L-Begin (`Nothing`).

A consumer should eliminate that package once, then compose the normalized raw
equality with `checkedActionProjects`; it should not rewrite the type of an
independently let-bound equation.

Only after that consumer checks should the split empty/nonempty L-Advance units
be attempted.

## Deferred units

Not opened:

- B3a retired L-Advance, empty Reloading;
- B3b retired L-Advance, nonempty Reloading;
- B4 two-order activation classifier;
- B5 presence-based orchestration classifier;
- B6 Candidate safety dispatcher and deterministic endpoints;
- positional pair RAR;
- pair-RAR insertion into A6;
- field 9;
- fields 10–15 population;
- occurrence fold, result, and O6 body.

Holes remain **20**, split **6/4/8/1/1**.

## Manifest and isolation

```text
NO_FROZEN_SURFACE_CHANGE_REQUIRED
```

All retained declarations are private quantity-0 CP5 research capital.
`adjacentSwapSuffixSpike` remains byte-identical at 1183 bytes with SHA-256
`e6d0c2d669355e5b7bef9efea1707f5853c708deb888bafe5770ba40dbd15a41`.
Production `src/`, `dgamma.ipkg`, CP3 blob
`2c697e532e83989de8591fa6a4378747c6a501c0`, revision-21 surfaces, fields 1–8,
and frozen revision-101/prefix/suffix capital remain unchanged.

No hole, postulate, `believe_me`, `assert_total`, unsafe escape, or uncommitted
Idris probe remains.

## Status and band

- Track A: **6/6 retained and checked**;
- Track B: **B1 retained; B2 exhausted; B3–B6 unopened**;
- pair RAR: **not started**;
- field 9: **composition retained, pair input absent**;
- fields 10–15: **foundations frozen, population not started**;
- assembly: **not started**;
- holes: **20**, split **6/4/8/1/1**.

The proposed **2–8 implementation-shift** band remains suspended. A narrow
design-only correlated post-retire action package is required before the
classifier producer can resume.
