# Revision-20 whole-bundle transport — moved-alignment stop audit

Coordinate: `cp5-thm73-scoping@f321b7c` after the corrected test-local record
commit, from authorized base `b56f725`.

## Stop decision

The corrected recursive spine and outer envelope elaborate exactly as scoped,
with no recursive `ReplayInvariantBundle`.  A concrete from-empty fixture then
constructs:

1. an actual checked prefix root insert;
2. two distinct checked root inserts forming the local pair;
3. the genuine revision-15 O/O local diamond at that prefix endpoint; and
4. the successful checked cross-state `O-Retire` suffix head.

Construction stops at the first field of the requested whole next bundle:
`replayAligned`.  `LocalRelationalDiamond` stores its moved transitions but does
not authenticate that their stored `DecEq` dictionaries are the outer
`nameEq`/`keyEq` required by `AlignedTransitions`.  Action/tag equations,
`ControlEquivalent`, `EffectStateRelated`, well-formedness, and pair-local
external order do not imply equality of executable dictionary closures.

No frozen declaration, O6 body, result record, manifest entry, production file,
CP3 file, or package file changes in this phase.

## 1. Corrected records pass

`R20CorrectedSealedReplayEnvelopeScopingPositive` defines test-local opaque
records only.

### Recursive `SealedSuffixReplaySpine`

Each nonempty node owns:

- exact checked source and replayed head transitions;
- action equality;
- tag equality;
- per-step RAR;
- per-step relational endpoint;
- per-step action/generated-registration occurrence correspondence;
- per-step relative ordinal equality;
- exact source/replayed after-state indices; and
- an already sealed recursive tail.

It contains **no** `ReplayInvariantBundle`.

### Outer `CorrectedAdjacentReplayEnvelope`

The outer record mirrors the nine existing `AdjacentSwapResult` fields:

1. whole replayed final state;
2. whole replayed suffix;
3. whole swapped trace;
4. original decomposition;
5. swapped decomposition;
6. whole same-external relation;
7. whole RAR;
8. whole endpoint; and
9. whole-trace `ReplayInvariantBundle`.

It then adds only:

10. erased `sealedSuffixReplay`; and
11. erased `sealedOccurrenceFold`.

The complete occurrence map and absolute ordinal law are projections of the
sealed fold.  The record constructor is not exported.

## 2. Concrete fixture capital constructed

`R20WholeBundleAlignmentGapPositive` uses:

- names `Nat`, with actors 0, 1, and 2;
- an uninhabited key type, so every component dependency/provision list is
  necessarily empty;
- one empty-program component;
- a protocol that ranks root components and has an empty generated catalog; and
- an explicitly empty initial registry.

The checked source schedule is:

```text
OInsert 0 Root
OInsert 1 Root   -- local left
OInsert 2 Root   -- local right
ORetire 0        -- source suffix head
```

The checked target prefix/pair/head is:

```text
OInsert 0 Root
OInsert 2 Root   -- moved right
OInsert 1 Root   -- moved left
ORetire 0        -- checked cross-state replay
```

Every raw/checked equation in the fixture reduces constructively.  The source
pair also carries explicit alignment, root-only registration discipline, exact
generation scan, distinct-child evidence, and impossible child-parent crossing
licenses.  `orchestrationOrchestrationDiamondSpike` therefore constructs the
genuine local diamond rather than accepting one as supplied output capital.

`r20CrossRetire` invokes `checkedRetireReplayAcrossLocalSwap` at the exact
`swappedFinal r20Diamond`.  Thus the earlier successful cross-state
applicability/RAR/endpoint/occurrence/ordinal checkpoint remains valid.

## 3. Exact mismatch

A completed bundle for `r20CandidateSwappedTrace` must project:

```idris
AlignedTransitions ... outerNameEq outerKeyEq r20CandidateSwappedTrace
```

The first moved transition has the constructor shape:

```idris
Fired storedRightNameEq storedRightKeyEq action tag checked
```

and its checked equation is indexed by `storedRightNameEq` and
`storedRightKeyEq`.  `AlignedStep` for the whole bundle requires the same trace
node to be literally indexed by the outer dictionaries.  Idris rejects the
conversion with:

```text
Mismatch between: storedRightKeyEq and keyEq.
```

`R20WholeBundleMovedAlignmentNegative` pins this exact failure for an arbitrary
`LocalRelationalDiamond`.  `wholeBundleRequiresExactMovedAlignment` separately
checks that the desired whole bundle necessarily exposes this exact field.

This is not a target-final invariant issue and is earlier than discipline,
provenance, quietness, failure freedom, totality, ranking, acyclicity,
well-foundedness, or support matching.  Those fields must not be investigated by
assuming the missing aligned trace.

## 4. Why existing capital cannot close it

- `movedRightAction` and `movedRightTag` relate only projections of a transition;
  they do not equate stored dictionaries.
- The analogous moved-left fields have the same limitation.
- `swappedEffects` and `swappedControlEquivalent` are endpoint observational
  relations and do not mention transition dictionaries.
- `swappedWellFormed` authenticates only the endpoint state.
- `SameExternalOrchestration` observes external action order, not evaluator
  dictionaries.
- Source `replayAligned` authenticates the source pair, not newly checked moved
  transitions.
- The recursive sealed spine cannot honestly store an aligned head unless its
  producer can first construct one; adding that output field alone merely moves
  the hole.
- Decidable equality/UIP for names or keys does not establish equality of
  arbitrary `DecEq` records or their negative closures.

The mismatch is exactly the dictionary-coherence class previously found in O3,
O4, and O5.  Those local producers were repaired with explicit source/early
alignment, but their result interface did not retain moved-output alignment for
O6.

## 5. Consumer and producer audit

### Consumer need

`ReplayInvariantBundle.replayAligned` is consumed by later adjacent swaps,
deletions, reachability reconstruction, support/rank invariants, and theorem
assembly.  It cannot be retired or weakened to unaligned raw transitions.

### Genuine producer availability

The implementations of O3/O4/O5 construct moved checked transitions using the
outer dictionaries internally.  Therefore moved-output alignment is likely
producer-suppliable **at local-diamond construction time**.  It is not
recoverable from the current public `LocalRelationalDiamond` value after those
checked equations have been hidden.

### Narrow repair candidates requiring a new gate

The preferred candidate is to retain producer-owned erased alignment in
`LocalRelationalDiamond`, for example:

```idris
0 movedPairAligned : AlignedTransitions ...
  (MoreTransitions movedRight (MoreTransitions movedLeft NoTransitions))
```

Every genuine O1–O5 producer must then construct this exact field from the
checked equations it already owns.  Adversarial local diamonds with unrelated
stored dictionaries become uninhabitable.

A weaker alternative is an erased moved-pair alignment premise on
`adjacentSwapSuffixSpike`, supplied only by authenticated local-diamond
producers.  This changes the frozen O6 signature and risks detached caller
capital, so it is not preferred.

Making `AdjacentSwapResult` opaque does not repair this gap by itself: its sole
producer still accepts an arbitrary existing `diamond` and must align the exact
transitions indexed by that value.

Neither repair is authorized here.

## 6. Effect on the previous boundary proposal

The former proposed delta—nine existing fields plus erased
`sealedSuffixReplay` and `sealedOccurrenceFold`, hidden constructor—is necessary
but no longer sufficient.  Issuing that boundary gate now would claim a
whole-bundle producer that cannot construct `replayAligned` from its frozen
inputs.

Therefore:

- no `AdjacentSwapResult` boundary gate is requested;
- the former single-declaration retirement forecast is suspended;
- hole count remains 21;
- `adjacentSwapOperationalOccurrenceFoldSpike` is not retired;
- `adjacentSwapSuffixSpike` stays byte-identical; and
- the `21 -> 20` forecast cannot be activated before moved alignment is retained
  by a reviewed producer boundary.

## 7. Re-estimate

The 18–30 band assumed that outer alignment would follow from the checked local
pair.  Retaining and migrating moved-output alignment across all O1–O5 producers,
then re-running the corrected whole-bundle fixture, adds a scoped interface and
adversarial-review phase.

Remaining O6 estimate is revised to **21–35 implementation shifts**:

| Remaining phase | Shifts |
|---|---:|
| Moved-output alignment scoping, producer audit, and adversarial probes | 3–5 |
| Authorized local-diamond record migration across O1–O5 | 3–5 |
| Corrected whole-bundle fixture after alignment retention | 3–5 |
| Opaque adjacent boundary, fold retirement, manifest/test migration | 2–4 |
| Remaining suffix action families and recursive bundle transport | 5–8 |
| Complete arbitrary suffix integration | 3–5 |
| Scoped adversarial review closure | 2–3 |
| **Total** | **21–35** |

The next checkpoint is now the first checked whole `ReplayInvariantBundle`,
before the first complete `adjacentSwapSuffixSpike`.

## Status

- Corrected test-local spine/envelope: complete and checked.
- Concrete from-empty prefix and root/root local pair: complete and checked.
- Genuine checked cross-state retire head: complete and checked.
- Whole next bundle: stopped at exact moved-transition alignment.
- Final invariant transport: deliberately not reached.
- Frozen interfaces and O6 bodies: unchanged.
