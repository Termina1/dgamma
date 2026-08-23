# O3 dictionary-coherence audit

Audit date: 2026-08-16  
Audit base: `cp5-thm73-scoping@40e7f2ee1cb429271b1507be30b313ce75e895ac`  
Scope: the still-open body `activationActivationDiamondSpike_rhs` only. No
research declaration, hole, production module, package file, or test interface is
changed by this audit.

## Executive conclusion

The apparent three-independent-dictionary problem is real at the standalone O3
signature, but it is **not** real capital at the genuine Theorem-73 consumer.
The immutable theorem already requires `AlignedTransitions ... nameEq keyEq` for
both input traces. `AlignedTransitions` indexes every node by the literal
constructor `Fired nameEq keyEq ...`; its own source comment says that it exists
precisely to avoid assuming proof irrelevance for distinct `DecEq`
implementations (`src/DGamma/Metatheory.idr:893-913`). Every genuine sorting and
operational-permutation consumer retains this alignment inside a
`ReplayInvariantBundle`.

Therefore:

* `left` and `right` may syntactically be nodes of an immutable statement-input
  trace (or a deletion/swap replay), but the genuine producer has an indexed
  proof that their stored dictionaries are definitionally the outer
  `nameEq`/`keyEq`;
* `earlyRight` is not selected from an arbitrary input trace. The local-swap
  producer must reconstruct that checked transition at the pre-left source, and
  the already checked O3 constructors build it with the same outer dictionary
  pair;
* the frozen standalone O3 declaration dropped exactly the alignment capital
  that its genuine producer owns.

Recommendation: **Option B**, narrowly expressed using the existing
`AlignedTransitions` family, not raw equality between interface records. The
Hedberg shortcut does not establish equality of two `Dec` values in Idris 2:
the `No` constructor stores an intensional `Not p` function. A branch-by-branch
cross-dictionary simulation remains possible, but that is Option A-full, not a
small congruence lemma.

## 1. Consumer trace

### 1.1 Immutable boundary

`Transition` stores executable dictionaries independently:

```idris
Fired : (nameEq : DecEq name) -> (keyEq : DecEq key) -> ... -> Transition before afterState
```

(`src/DGamma/Calculus.idr:5838-5847`). Thus a bare
`Transition first middle` does not reveal that its dictionaries equal any
separate outer arguments.

The immutable `confluenceTheorem`, however, accepts its two traces together with

```idris
AlignedTransitions ... nameEq keyEq leftTrace
AlignedTransitions ... nameEq keyEq rightTrace
```

before the remaining discipline, well-formedness, totality, independence, and
same-input premises (`src/DGamma/CP3.idr:3785-3810`). This is stronger than a
semantic replay assertion. The `AlignedStep` result index is literally

```idris
MoreTransitions (Fired nameEq keyEq action tag equation) rest
```

(`src/DGamma/Metatheory.idr:897-913`). Pattern matching an alignment proof
therefore exposes the outer dictionaries and the checked equation without any
`DecEq`-record equality proof.

This means that the immutable statement does **not** pass arbitrary independent
`Fired` dictionaries into the genuine proof chain. The trace values are
syntactically inputs, but their accepted premise refines every constructor to the
single outer pair.

### 1.2 Capital carried through deletion

`ReplayInvariantBundle` stores `replayAligned : AlignedTransitions ... nameEq
keyEq trace` as its first field (`research/DGamma/CP5ConfluenceLocalDiamondSpike.idr:423-450`).
`CanonicalizationPremises` is only a wrapper around that exact bundle
(`research/DGamma/CP5ConfluenceDeletionChainSpike.idr:34-47`).

Deletion has an identity terminator:

```idris
ClosingFreeDeletionDone : (trace : Transitions initial finalState) ->
  ClosingFreeDeletionDerivation ... trace trace
```

(`research/DGamma/CP5ConfluenceDeletionChainSpike.idr:486-512`). Hence a
closing-free statement-input trace can reach sorting without being rebuilt.
That does **not** revive arbitrary dictionaries: the reduction also carries
`reducedPremises : CanonicalizationPremises ... reducedTrace`
(`CP5ConfluenceDeletionChainSpike.idr:569-586`), whose nested
`replayAligned` still refines the exact retained trace.

On a nonidentity deletion path, the same conclusion holds recursively: the
survivor becomes the source of the next `ClosingFreeDeletionStep`, and the final
`ClosingFreeReduction` again exports the aligned `reducedPremises`. Alignment is
capital of the trace, not an assumption that deletion rebuilt every node.

### 1.3 The adjacent-swap chain

The actual local-diamond consumer is the derivation node
`FiniteAdjacentSwapStep`. It stores the exact current `original`, its
`prefixTrace`, adjacent `left` and `right`, `suffix`, orientation, local diamond,
`AdjacentSwapResult`, and recursive derivation
(`research/DGamma/CP5ConfluenceLocalDiamondSpike.idr:881-917`).
`AdjacentSwapResult` is indexed by those same nodes and returns
`swappedPremises : ReplayInvariantBundle ... swappedTrace`
(`CP5ConfluenceLocalDiamondSpike.idr:789-824`). Thus every recursive swap source
is aligned again.

`adjacentSwapSuffixSpike` consumes an exact decomposition plus the complete
`ReplayInvariantBundle` and a local diamond
(`CP5ConfluenceLocalDiamondSpike.idr:2888-2908`). A producer can split
`replayAligned` along that exact decomposition with the existing
`alignedAppendSplit` (`src/DGamma/CP3.idr:4792-4805`). After pattern matching the
resulting two `AlignedStep`s, the adjacent nodes are definitionally
`Fired nameEq keyEq ...`.

`SortedClosingFreeTrace` requires its `sortingAdjacentDerivation` to be exactly a
`FiniteAdjacentSwapDerivation ... nameEq keyEq original sortedTrace`
(`research/DGamma/CP5ConfluenceCanonicalSortSpike.idr:102-123`).
`sortClosingFreeTraceSpike` consumes the aligned `ReplayInvariantBundle` for the
trace and must produce that derivation (`CP5ConfluenceCanonicalSortSpike.idr:192-207`).
Consequently O17 cannot legitimately call O3 on a bare unaligned pair even when
that pair originated in the immutable input trace.

### 1.4 Applicability and O19/O20 consumers

`AdjacentActorSwapSafety` owns both the exact block decomposition and
`sourcePremises : ReplayInvariantBundle ... nameEq keyEq sourceTrace`
(`research/DGamma/CP5ConfluenceCrossTraceSpike.idr:109-142`).
`OperationalAdjacentBlockSwap` consumes that same safety and source bundle and
contains a mandatory `WholeBlockSwapDerivation`, hence a nonempty finite chain of
concrete local diamonds (`CP5ConfluenceCrossTraceSpike.idr:638-670`). Its
producer `operationalAdjacentBlockSwapSpike` receives the source bundle directly
(`CP5ConfluenceCrossTraceSpike.idr:692-712`).

`OperationalActorPermutation` threads `blockSwapPremises step` into every
recursive step (`CP5ConfluenceCrossTraceSpike.idr:719-755`). O19's
`CertifiedOperationalCanonicalPermutation` seals such a realization starting
from `canonicalReplayPremises leftCapital`
(`CP5ConfluenceCrossTraceSpike.idr:860-893`). O20 consumes the sealed
operational fold; it does not inject unrelated local transitions. Thus O19/O20
also have the same dictionary alignment at every local application.

### 1.5 Origin of the three O3 transition arguments

At each genuine A/A crossing:

1. **`left`** is the current trace node selected by the exact adjacent
   decomposition. It can ultimately descend from a statement-input transition,
   a deletion survivor, or a previous swapped transition. In all three cases the
   current `ReplayInvariantBundle.replayAligned` refines it to
   `Fired nameEq keyEq ...`.
2. **`right`** has the same origin and the same refinement; it is the immediately
   following `AlignedStep`.
3. **`earlyRight`** is operational applicability evidence at `first`, not an
   unconstrained occurrence imported from the immutable input trace. The block
   producer must reconstruct the right action before `left`. The checked O3
   pipeline now creates `Fired nameEq keyEq action tag checked` through
   `checkRawActivationMove` (`research/DGamma/CP5ConfluenceLocalDiamondSpike.idr:2369-2385`)
   after raw Begin/Iter/Finish reconstruction. A singleton alignment proof is
   then `AlignedStep action tag checked NoTransitions AlignedEnd`.

There are currently no tracked Idris call sites for
`activationActivationDiamondSpike`; `git grep` finds only its declaration and
hole. The exact sites above are the indexed construction sites that the open O6,
O17, and O19 producers must implement. They all own the needed alignment.

**Consumer verdict:** the standalone O3 type is over-general. Genuine consumers
never need the independent-dictionary case. Option B is producer-suppliable; it
is not killed by the immutable statement inputs.

## 2. Hedberg route assessment

### 2.1 What Hedberg does provide

For a fixed proposition `x = y`, any `Dec (x = y)` has only a logically
consistent polarity. Two `Yes` branches carry equality proofs that can be made
unique (Hedberg/UIP), while `Yes`/`No` and `No`/`Yes` are contradictory. This is
enough to prove a branch-agreement relation and to align the transport used by
dependent lookups in a `Yes Refl` branch.

A local total diagnostic confirmed that Idris accepts generic equality-proof UIP
for the `Yes`/`Yes` case and rejects the cross-polarity cases by contradiction.
The diagnostic was under `/tmp` and is not release evidence; the authoritative
claim here is the constructor analysis against `Prelude.Types.Dec`.

### 2.2 Why `decEqUnique : d1 = d2` does not follow

Idris 2 defines both fields of `Dec` as unrestricted:

```idris
Yes : (prf : prop) -> Dec prop
No  : (contra : Not prop) -> Dec prop
```

(`/opt/homebrew/.../prelude-0.8.0/Prelude/Types.idr:265-275`). In the `No`/`No`
case, equality of `No leftContra` and `No rightContra` requires equality of two
functions `prop -> Void`. Neither Hedberg's uniqueness of proofs of `x = y` nor
self-certification supplies function extensionality or proof irrelevance for
these negative functions.

The diagnostic equation

```idris
decDecisionUnique (No leftContra) (No rightContra) = Refl
```

was rejected with `Mismatch between: rightContra and leftContra`. Adding
function extensionality, a proof-irrelevance postulate, `believe_me`, or another
escape hatch is prohibited by project policy. Therefore two lawful `DecEq`
dictionaries agree in branch polarity, but their `decEq` results are not in
general propositionally equal as Idris data. They cannot be rewritten by a
single pointwise `decEqUnique` congruence lemma.

### 2.3 What a signature-preserving proof would actually require

Option A can still simulate both evaluators branch by branch. A relation such as

```text
DecisionsAgree (Yes p) (Yes q)  -- carrying p = q
DecisionsAgree (No _) (No _)
```

is constructible. Each consumer of `decEq` must then be proved coherent by
simultaneously case-splitting both decisions; it cannot merely rewrite one
`Dec` value into the other.

The O3 path reaches at least:

* `lookupEntries`/`lookupBinding`, whose return type is dependent and whose
  `Yes Refl` transport must be aligned (`src/DGamma/Coeffects.idr:42-57`);
* registry lookup/replacement and the provider pipeline `providerOf`,
  `resolveView`, `valueFromProvider`, `resolveCommittedValues`, and
  `targetFiber` (`src/DGamma/Calculus.idr:769-815, 918-952, 987-995, 1106-1115`);
* `beginFiberAction` and the `LBegin`/`LAdvance` branches of `applyAction`,
  including target comparison, committed capability resolution, program-shape
  cases, step execution, and dependent replacement (`Calculus.idr:1392-1499`);
* `projectEffectState`, `setEffectTable`, `resolveEffectValues`, and
  `advanceRuntimeEffectMap` (`src/DGamma/Metatheory.idr:982-999, 1078-1100,
  1144-1169`);
* `registryWellFormed`, which recursively combines parent-chain, view, and
  pairwise-provision folds (`Calculus.idr:2258-2270`); and finally
* `checkedApplyAction`, which compares the raw evaluator result and executes
  `registryWellFormed` on the exact target (`Calculus.idr:5825-5836`).

This is a cross-implementation evaluator simulation, not congruence at a handful
of call sites.

### 2.4 Dependent `Binding` and erased `UniqueKeys`

`Binding` is genuinely dependent: `Bind k value` stores `value k`
(`src/DGamma/Coeffects.idr:11-22`). In `lookupEntries`, a successful name/key
comparison rewrites the stored value's index through the equality proof. The
`Yes`/`Yes` Hedberg component can align that transport, so this spot is
constructively tractable, but it needs an explicit dependent recursion lemma.

`CoeffectContext.uniqueBindings` has quantity 0, but quantity 0 is erasure, not
definitional proof irrelevance (`Coeffects.idr:24-40`). Equality of two context
records can still require equality of their hidden `UniqueKeys` arguments. The
calculus already contains same-dictionary canonicalization and reproof lemmas,
including `canonicalUniqueKeys`, `canonicalOwnedEvidenceIrrelevant`, and
`canonicalOwnedFromFilteredCong` (`src/DGamma/Calculus.idr:116-179`), plus
runtime reproof lemmas in `src/DGamma/CP4RuntimeBindings.idr`. These reduce the
risk after runtime binding lists are shown equal, but they do not make two
`DecEq` records or two `No` closures equal.

For an A-full proof, one must first show identical runtime binding lists by
branch simulation and then deliberately apply the existing canonical/reproof
lemmas (or prove an analogous `CoeffectContext` reproof lemma). Relying on the
field's quantity alone is unsound.

**Hedberg verdict:** A-Hedberg as “pointwise `Dec` equality followed by ordinary
congruence” is not viable in intensional Idris 2. The viable signature-preserving
variant is A-full, aided by Hedberg in successful dependent branches and by
existing proof-reconciliation lemmas.

## 3. Option B specification and producer audit

### 3.1 Recommended exact premises

Do not add six raw equalities between `DecEq` interface records. Use the existing
indexed family that was designed for this exact boundary. Add these erased
premises to `activationActivationDiamondSpike`:

```idris
AlignedTransitions name key world error value nameEq keyEq
  (MoreTransitions left (MoreTransitions right NoTransitions)) ->
AlignedTransitions name key world error value nameEq keyEq
  (MoreTransitions earlyRight NoTransitions) ->
```

The first premise says both source-pair constructors store the outer dictionary
pair and exposes both outer checked equations. The second says the applicability
transition stores the same pair. There is no new runtime data and no equality of
interface records.

An equivalent but less idiomatic specification would introduce an indexed
singleton `TransitionUses nameEq keyEq transition` with only
`TransitionUses nameEq keyEq (Fired nameEq keyEq action tag checked)`. The
existing `AlignedTransitions` family should be preferred because it already has
production use, documentation, decomposition lemmas, and exact checked-equation
capital.

### 3.2 Producer-suppliability at every genuine site

| Genuine construction site | Source of pair alignment | Source of early alignment | Definitional test |
|---|---|---|---|
| First O17 sorting swap over a reduced trace | `replayAligned (chainReplayCapital (reducedPremises reduction))`, split by the exact prefix/pair/suffix decomposition | reconstructed right transition built as `Fired nameEq keyEq ...` | after matching two `AlignedStep`s, the stored dictionaries are the outer variables; singleton early proof is `AlignedStep ... AlignedEnd` |
| Recursive O17 adjacent swap | `replayAligned (swappedPremises result)` | reconstructed at the new source with the same outer arguments | same constructor forms, no dictionary equality proof |
| O6 whole-block producer | its `sourcePremises : ReplayInvariantBundle ... nameEq keyEq sourceTrace` | reconstructed for the current crossing | same |
| Initial O19 canonical permutation step | `canonicalReplayPremises leftCapital`, passed as `sourcePremises` | reconstructed by `operationalAdjacentBlockSwapSpike` | same |
| Recursive O19 permutation step | `blockSwapPremises step` | reconstructed at `blockSwapTrace step` | same |
| O20 consumer | consumes `selectedPermutationRealized`; does not construct or select local transitions independently | not applicable | local alignment was already sealed in every operational step |

The immutable input boundary also passes the test: its supplied
`AlignedTransitions` proof only has an `AlignedStep` constructor when the trace
head is literally `Fired nameEq keyEq ...`. Even the identity deletion case
therefore enters O17 with definitionally aligned input nodes.

There is no tracked direct use of the standalone O3 function that would lose
capital. Existing research tests exercise surrounding interfaces and concrete
traces; `git grep` reports no separate call site to migrate.

### 3.3 Necessary follow-up changes if authorized

A follow-up implementation shift would need to:

1. change only the O3 research declaration by adding the two erased alignment
   premises above;
2. update the immutable hole-interface manifest and its exact auditor entry as an
   explicitly authorized declaration repair;
3. add a private exact-decomposition helper deriving the pair alignment from a
   `ReplayInvariantBundle` for O6/O17 consumers;
4. refactor the checked homogeneous-dictionary O3 pipeline to pattern match the
   two alignment proofs before consuming `left`, `right`, and `earlyRight`;
5. add focused positive and negative interface probes: an aligned pair must type
   check, while an independently-dictionary `Fired` transition without matching
   alignment must not reach O3; and
6. separately finish the remaining `swappedControls` proof using
   `iteratorYieldsStable` for successful Advance yields.

No change to `Transition`, `AlignedTransitions`, `confluenceTheorem`, `src/`, or
`dgamma.ipkg` is required. O4's reverse-activation signature has the analogous
risk, but changing it is outside this O3 audit and requires its own consumer
gate.

## 4. Recommendation and option-specific grade

### Recommended: B

Option B is the honest minimal repair. It restores capital already present at
all genuine consumers, follows the established `AlignedTransitions` design, and
avoids a large theorem about implementation identity of arbitrary equality
deciders. It is not a convenience assumption and does not strengthen the
immutable Theorem-73 boundary.

Estimated remaining O3 work under B: **4-7 grind shifts (L)**:

* 1 shift for the authorized declaration/manifest/probe change and alignment
  extraction;
* 2-4 shifts for Begin/empty-Finish exact controls and yielded-Advance
  `iteratorYieldsStable` accumulator/undo transport; and
* 1-2 shifts for final assembly, hole removal, bookkeeping, and hardened
  validation.

This remains within the accepted Phase-B 32-55 band; no phase re-grade is
recommended under B.

### Viable fallback: A-full

A-full preserves the standalone signature but requires branch-simulating the
relevant lookup, target, effect, raw evaluator, target-well-formedness, and
checked evaluator paths, with explicit reconciliation of dependent and erased
proofs. Estimated remaining O3 work: **15-29 grind shifts (XL)** before the
already required controls/assembly closure. If chosen, Phase B should be
re-gated and likely widened; hiding this work inside the old band would be
misleading.

### Not viable: A-Hedberg-by-congruence

The proposed `decEqUnique : (d1 d2 : Dec (x = y)) -> d1 = d2` is blocked by the
`No`/`No` negative-function fields. Without an unauthorized extensionality or
proof-irrelevance principle it cannot support direct evaluator congruence. Its
constructive residue is exactly the branch simulation counted as A-full.

## 5. Gate request

Authorize **B** for O3 only: add the two erased `AlignedTransitions` premises to
`activationActivationDiamondSpike`, update the frozen research-hole manifest and
focused probes, then resume the homogeneous-dictionary control/diamond assembly.
If B is rejected, authorize A-full together with an explicit O3/Phase-B re-grade.
Do not authorize or count A-Hedberg-by-congruence.
