# O6 revision 99: Begin closed, empty Advance closed, nonempty consumer stop

## Scope

Grind shift #107 (overall #161) resumed from accepted safe HEAD `0625329`
under the revision-98 probe-first ruling.

The shift:

1. checked the disposable retired-Begin correlation probe within its own
   three-attempt budget;
2. retained the checked package, producer, and one-elimination consumer;
3. retained the empty-Reloading retired-LAdvance exclusion;
4. attempted the nonempty-Reloading classifier as a separate unit;
5. stopped immediately when that unit exhausted its three-attempt budget.

B4–B6, pair RAR, fields, and assembly were not opened.

## B2 probe verdict

The disposable probe copied the accepted CP5 source under `/tmp`, adding only:

- a producer-indexed `R98RetiredBeginCorrelationProbe`;
- quantity-0 fields jointly owning:
  - the exact `R97CheckedRetireProjection` output;
  - original and post-replacement owner lookups;
  - retired target absence;
  - normalized raw L-Begin result `Nothing`;
- a one-elimination consumer ending exactly in `Void`.

### Probe attempts

1. **Failed.** Dependent left-hand-side variables `before`, `retiredState`,
   `retireTag`, and `retireChecked` were independently named before matching the
   indexed projection constructor. Idris required the unified constructor
   indices to use the same pattern names.
2. **Failed.** Wildcarding the already fixed indices closed that issue. The
   producer then attempted to rewrite a let-bound `targetAbsent` proof into the
   normalizer and reproduced the prior non-reindexing class. The consumer also
   rejected an independently typed let-bound raw projection.
3. **Passed.** The normalizer reduced the retired target definitionally rather
   than rewriting its proof, while the consumer composed `beginRaw` directly
   with `checkedActionProjects` and a fully explicit `Nothing /= Just _` helper.

Marker:

```text
GRIND161_B2_PROBE_ATTEMPT3=passed
```

The disposable probe directory was removed after the retained implementation
checked.

## B2 retained

Commit `6ec274d` retains:

- `R98RetiredBeginCorrelation`;
- `r98ProduceRetiredBeginCorrelation`;
- `r98NothingNotJust`;
- `r98ConsumeRetiredBeginCorrelation`.

The constructor is indexed by the exact B1 projection and all of its owned
fields are quantity 0. It fixes under one elimination:

- the source state and exact pre-retirement owner lookup;
- the exact post-retirement registry and owner lookup;
- `targetFiber (retireFiber oldFiber) postRegistry = Nothing`;
- raw `applyAction (LBegin actor) postState = Nothing`.

The producer pattern-matches the B1 package exactly once. The consumer does not
rewrite any opaque checked equation and does not expect a let-bound equation to
reindex. It projects `checkedApplyAction` first and composes the resulting raw
success with the jointly owned raw `Nothing`, obtaining `Nothing = Just _`.

The retained unit checked on attempt 1 after the successful disposable probe.
Fresh direct CP5 and R16 checks passed before commit.

## B3a retained

Commit `a2c2c51` retains:

- `r98DivertTagNotIter`;
- `r98DivertTagNotFinish`;
- `r98RetiredAdvanceEmptyExcluded`.

For a retired owner in `Reloading [] accumulator view`, raw L-Advance is
normalized to the exact L-Divert result because retired target lookup is
`Nothing`. The checked equation is projected first; raw output determinism then
proves that the observed tag is L-Divert. Both paper activation tags L-Iter and
L-Finish are excluded.

The unit checked on attempt 1. Fresh direct CP5 and R16 checks passed before
commit.

## B3b stop: nonempty Reloading

### Intended classification

For a retired owner in `Reloading (step :: rest) accumulator view`, the honest
raw outcomes are:

- capability resolution `Nothing`: L-Advance unavailable;
- `runStepEffect = Left error`: L-Raise;
- `runStepEffect = Right ...`: L-Divert, because the retired target is absent.

None can carry L-Iter or L-Finish.

### Attempt record

1. An outcome family indexed directly by the opaque `applyAction` result was
   rejected in both producer and consumer. Branching on capability resolution
   did not reindex the family’s stored `applyAction` expression:

   ```text
   Can't solve constraint between: Nothing and case resolveCommittedValues ...
   ```

   This is the known indexed-computation correlation class, so that shape was
   discarded.

2. The package was changed to own explicit normalized raw equalities, and a
   helper used `with (...) proof` for both capability resolution and
   `runStepEffect`. This closed unavailable and raised construction. In the
   successful-effect branch, a separately named `nextAccumulator` did not
   unfold to the evaluator’s exact `pushLocalUndo` composition. Separately, the
   outcome consumer’s local observed-tag equality failed to elaborate:

   ```text
   Mismatch between: RuleTag and Type.
   ```

3. Inlining the exact `pushLocalUndo` expression closed the complete producer.
   Even fully qualifying the local equality as
   `(the RuleTag LRaiseTag) = tag` left the same consumer elaboration failure:

   ```text
   Mismatch between: RuleTag and Type.
   ```

All attempts count. The complete uncommitted B3b unit was removed. No fourth
consumer cure was attempted.

Marker:

```text
GRIND161_B3B_NONEMPTY=failed_after_3
```

### Semantic diagnosis and next design

The operational producer is design-closed: use explicit normalized equality
fields and `with (...) proof` for capability and step outcomes, with the exact
`pushLocalUndo` expression inlined.

The remaining boundary is now only the dependent consumer’s locally declared
tag equality after outcome elimination. The next design must move tag
comparison into ordinary, fully explicit top-level helpers, for example:

- unavailable raw result versus projected checked success -> `Void`;
- normalized L-Raise raw success versus projected checked success -> both tag
  exclusions;
- normalized L-Divert raw success versus projected checked success -> both tag
  exclusions.

The dependent outcome consumer should only eliminate the package once and call
those helpers. It must not introduce a local observed-tag equality. A fresh
probe of exactly this helper/consumer boundary is appropriate before retaining
B3b.

## Deferred units

Not opened:

- B4 two-order activation classifier;
- B5 presence-based orchestration classifier;
- B6 Candidate safety dispatcher and endpoint determinism;
- positional equal-owner pair RAR;
- pair-RAR insertion into the retained field-9 composition;
- fields 9–15 population;
- occurrence fold, result, and O6 body.

Holes remain **20**, split **6/4/8/1/1**.

## Manifest and isolation

```text
NO_FROZEN_SURFACE_CHANGE_REQUIRED
```

The Track-A chain, B1, revision-101 capital, `84c1b81`, sealed suffix RAR,
fields 1–8, field-10–15 foundations, revision-21 public surfaces, and all prior
capital remain unchanged.

`adjacentSwapSuffixSpike` remains byte-identical at 1183 bytes with SHA-256
`e6d0c2d669355e5b7bef9efea1707f5853c708deb888bafe5770ba40dbd15a41`.
Production `src/`, `dgamma.ipkg`, and CP3 blob
`2c697e532e83989de8591fa6a4378747c6a501c0` remain unchanged.

No hole, postulate, `believe_me`, `assert_total`, unsafe escape, uncommitted Idris
probe, or staged file remains.

## Status and proposed band

- B2 disposable probe: **passed on attempt 3 and removed**;
- B2 retained package/producer/consumer: **closed** (`6ec274d`);
- B3a empty Reloading: **closed** (`a2c2c51`);
- B3b nonempty Reloading: **producer recipe closed, consumer exhausted and
  removed**;
- B4–B6: **unopened**;
- pair RAR: **unopened**;
- field 9: **composition retained, pair input absent**;
- fields 10–15: **foundations retained, population unopened**;
- assembly: **unopened**;
- holes: **20**, split **6/4/8/1/1**.

The implementation band should **not** yet be re-established. A narrow
probe-first shift for the three top-level raw-output/tag comparison helpers and
one-elimination B3b consumer is required. Reconsider the band only after the
full B4 classifier producer checks.
