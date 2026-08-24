# O6 external-order audit — revision-18 decision gate

Coordinate audited: `cp5-thm73-scoping@ea7def9` (revision-17 review commit).
No declaration in `research/` or `src/` is changed by this audit.

## Verdict in one paragraph

The revision-17 `ControlEquivalent` repair is ratified and the old endpoint-control
blocker is discharged. The new review blocker is real: the *generic* current
`adjacentSwapSuffixSpike` statement is false for two distinct root-external
O-Insert steps because `AdjacentSwapResult.swappedSameExternalInputs` preserves
the immutable external-input order. However, the canonicalization chain has no
semantic need to transpose two root-external steps. Root orchestration is an
ordered subsequence fixed by `SameExternalOrchestration`, the theorem additionally
couples historical root births in that order, and canonical schedules require
that same subsequence while moving it only before lifecycle work. O19's actual
whole-block crossings are stronger still: a block starts with L-Begin and its body
contains only lifecycle steps of the selected actor or yielded *child* insertions,
so every crossed block node is internal. The gap is that the accepted O17/O19
interfaces do not yet record this legality at each `FiniteAdjacentSwapStep`;
their producer bodies are holes. Revision 18 should therefore narrow only the
suffix-splice producer to an exact, erased, pair-local
`SameExternalOrchestration` witness. O5 and the local diamond remain unchanged.

## 1. The obstruction being audited

### 1.1 Immutable external observation

`RootOrchestrationStep` observes:

- root `OInsert`, by action shape (`src/DGamma/CP3.idr:1983-1998`);
- `ORetire` of a currently root-parented fiber (`:1999-2008`); and
- `ORemove` of a currently root-parented fiber (`:2009-2018`).

`SameExternalOrchestration` says explicitly that root inputs match in order
(`src/DGamma/CP3.idr:2051-2056`). Its only constructors are:

- skip a left transition proved non-root (`:2064-2070`);
- skip a right transition proved non-root (`:2071-2077`); or
- match two root steps with one literally equal action (`:2078-2091`).

Thus it is a subsequence equality for root orchestration, not a commutative
multiset quotient.

The immutable theorem premise is even more explicit. A
`SameOrchestrationModuloGenerated` stores both
`sameExternalInputs : SameExternalOrchestration ...` and
`externalRootGenerationsCoupled` (`src/DGamma/CP3.idr:3005-3021`). The latter
matches root O-Insert births in sequence and maps their exact generation ordinals
(`:2191-2246`). Distinct root births therefore cannot be silently permuted by a
current-name bijection.

### 1.2 Where the false generic requirement enters

`AdjacentSwapResult` stores the exact swapped decomposition and then requires

```idris
swappedSameExternalInputs :
  SameExternalOrchestration nameEq original swappedTrace
```

at `research/DGamma/CP5ConfluenceLocalDiamondSpike.idr:841-870`, specifically
`:858-864`. Every `FiniteAdjacentSwapStep` embeds a complete result at
`:925-956`; the nonempty form does the same at `:962-985`.

For a two-node, empty-suffix root/root source, the globally sealed occurrence fold
(`:810-834`, projected at `:872-885`) prevents hiding a third target step. The
tracked `R17FullResultImpossibility` then exhausts all three external-relation
constructors: neither root head can be skipped, while matching the left source
head with `movedRight` equates the distinct insertion actors. This uses no retired
ordered-control field.

Conclusion: the present *unrestricted* suffix theorem is uninhabitable. This does
not invalidate `LocalRelationalDiamond`, whose checked moved steps and endpoint
relations remain true.

## 2. Who genuinely calls O6, with which pairs?

There are currently no completed literal calls to `adjacentSwapSuffixSpike`: its
body and the producer bodies that will invoke it are holes. The genuine call
graph is nevertheless fixed by the accepted indexed result types.

### 2.1 O17: one-trace derivation-carrying sorting

`sortClosingFreeTraceSpike` is the O17 producer. Its declaration consumes a
closing-free trace shape and a support linearization and promises a
`SortedClosingFreeTrace` (`research/DGamma/CP5ConfluenceCanonicalSortSpike.idr:
192-207`). That record must contain:

1. `sortingAdjacentDerivation : FiniteAdjacentSwapDerivation` (`:114-120`), so
   every actual adjacent node has an O6 `AdjacentSwapResult`;
2. `sortedSameInputs : SameExternalOrchestration original sortedTrace`
   (`:121-123`);
3. contiguous `LocatedOpenEpisodeBlock`s in support order (`:124-144`); and
4. canonical input placement (`:145-148`).

The support order alone does **not** constrain root-input order:
`SupportOrderingCapital` contains only `orderedSupportNames` and an Equation-62
linearization (`:63-72`). Therefore the theorem premises do not automatically
prove that an arbitrary `FiniteAdjacentSwapDerivation` chosen by a caller has
legal nodes. O17 must construct a *stable* derivation.

A stable producer has two kinds of movement and neither needs root/root:

- To establish canonical input placement, move each root step left only across
  non-root/lifecycle work, retaining the root subsequence. Canonical placement
  requires every root orchestration step before lifecycle work
  (`src/DGamma/CP3.idr:2034-2049`) and stores that fact as
  `allRootInputsFirst` (`:3152-3164`); it never asks to sort roots among
  themselves.
- To gather and topologically order lifecycle blocks, move L-Begin/lifecycle or
  yielded-child nodes. `LocatedOpenEpisodeBlock` begins with L-Begin and carries
  `ActorLifecycleOnly` for its body (`src/DGamma/CP3.idr:1821-1845`). The latter
  permits only lifecycle actions of the selected actor or
  `OInsert child (ChildOf selected)` (`:1781-1804`). Both are non-root by action
  shape.

Accordingly O17 never *needs* to exchange two root-external transitions. But this
is presently an algorithmic producer obligation, not a theorem already derivable
from the unconstrained finite-derivation type. Revision 18 must make each O6 call
carry the missing legality proof.

### 2.2 O19: cross-canonical actor-block permutation

O19 starts from already canonical traces. `canonicalActorBlockDecomposition`
projects the exact `sortedBlock` values from sealed one-trace capital
(`research/DGamma/CP5ConfluenceCrossTraceSpike.idr:839-853`). The selected
permutation is simultaneously realized as an `OperationalActorPermutation`
inside `CertifiedOperationalCanonicalPermutation` (`:855-893`), rather than
being a caller-selected list permutation.

Each operational actor step consumes an `OperationalAdjacentBlockSwap`
(`:714-755`). That block swap contains a nonempty finite adjacent derivation,
its endpoint, replay bundle, and `blockSwapSameExternalInputs` (`:638-670`). Its
producer explicitly performs the Cartesian crossing of the two located blocks
and splices every `AdjacentSwapResult` (`:692-712`).

At these call sites, both crossed sides are internal:

- `ActorBlockDecomposition.decomposedBlock` returns an exact
  `LocatedOpenEpisodeBlock` (`:43-59`);
- the opening is L-Begin (`src/DGamma/CP3.idr:1833-1835`); and
- each body node is classified by `ActorLifecycleOnly` as lifecycle or child
  insertion (`:1786-1804`).

Therefore the genuine O19 whole-block producer can supply pair-local external
legality at every Cartesian node, including O/O child-insert/child-insert. The
reviewer's root/root counterexample is outside these block ranges.

The outer theorem premise independently pins the common external sequence:
`SameOrchestrationModuloGenerated.sameExternalInputs` and
`externalRootGenerationsCoupled` (`src/DGamma/CP3.idr:3017-3021`). Each sealed
canonical schedule also retains `sameInputs` relative to its source and canonical
input placement (`src/DGamma/CP3.idr:3240-3266`). Thus the left and right
canonical traces may differ in internal block order, but not in their ordered
root subsequence.

### 2.3 O20 and the final bridge

O20 does not call generic O6 directly. It accepts O19's sealed operational
package (`research/DGamma/CP5ConfluenceCrossTraceSpike.idr:1091-1115`). Its
`PermutedCanonicalExecution` stores the composed replay endpoint and
`permutationSameExternalInputs` (`:1010-1032`), while replay and occurrence maps
are definitionally projected from `selectedPermutationRealized` (`:1034-1060`).
The final convergence record then consumes that exact trace/map in the renamed
bridge (`:1062-1089`).

Hence O20 needs every realized O19 node to preserve external order, but needs no
ability to transpose root/root nodes.

### 2.4 Answer to the audit question

- **Need:** no canonical goal requires transposing two distinct root-external
  operations. Their relative order is fixed by immutable theorem capital and by
  every canonical schedule.
- **O19 producer evidence:** direct and strong; every actual block-crossing node
  is internal on both sides.
- **O17 producer evidence:** semantically available through a stable
  root-hoisting/block-sorting algorithm, but not yet represented by the current
  hole signature or finite-derivation constructors.
- **Current type gap:** an arbitrary finite derivation may still contain an
  illegal root/root swap (possibly later undone). Final `sortedSameInputs` alone
  does not authenticate each intermediate node. Narrowing O6 is therefore
  consumer-needed rather than redundant.

## 3. Revision-18 candidate designs

### Option A1 — exact pair-local external relation (recommended)

Add one erased premise to `adjacentSwapSuffixSpike`, indexed by its actual pair,
diamond, and moved transitions:

```idris
(0 pairExternalOrder :
  SameExternalOrchestration nameEq
    (MoreTransitions left (MoreTransitions right NoTransitions))
    (MoreTransitions (movedRight diamond)
      (MoreTransitions (movedLeft diamond) NoTransitions))) ->
```

Do **not** add it to `LocalRelationalDiamond`, `AdjacentSwapResult`, or the
occurrence-fold hole. The suffix producer consumes it exactly to build
`swappedSameExternalInputs`; the occurrence fold has no external-order consumer.
The indices prevent a witness for an unrelated pair or caller-selected endpoint.

**Consumer-neededness:** exact. It is precisely the missing local premise for the
result field at local-diamond lines 863-864 and composes through the prefix and
replayed suffix.

**Producer-suppliability:**

- O19: both source and moved block nodes are internal; construct the relation by
  the four skip constructors using block-position classification and moved-action
  equalities.
- O17: a stable producer supplies internal/internal for block work and
  internal/root or root/internal for stable root hoisting. The external side is
  matched to its moved checked occurrence; the internal side is skipped.
- Root/root distinct: correctly rejected by the tracked total proof.

The O17 root/internal case still requires constructive lemmas that a checked
foreign move preserves `RootOrchestrationStep` for the external node, especially
state-sensitive ORetire/ORemove. This should be proved in positive producer probes
*before* committing the signature repair. If that proof exposes a mismatch, stop
at the gate rather than pass the witness as caller capital.

**O5 impact:** none. O5 continues to construct the true local diamond for all nine
O/O pairs. Revision 18 narrows only when that diamond may be spliced while
preserving external observations.

**Cost:** 4–7 shifts for classification/moved-root stability, genuine O17/O19
producer probes, the one signature edit, suffix external-relation composition,
harness/bookkeeping, and scoped review. The remaining occurrence fold and full
O6 implementation are still separate XL work.

### Option A2 — source-side skippability disjunction

Premise:

```idris
Either
  (RootOrchestrationStep nameEq left -> Void)
  (RootOrchestrationStep nameEq right -> Void)
```

**Consumer-neededness:** logically close but indirect. It excludes the reviewer's
root/root pair.

**Producer-suppliability:** source classifications are easy at genuine O17/O19
positions. However it does not itself classify the moved counterpart. That is
harmless for lifecycle and child-insert actions, whose non-root status follows
from action shape, but state-sensitive root ORetire/ORemove requires additional
lookup/parent transport. The O6 body would have to recover exactly the direct
relation in A1.

**O5 impact:** none.

**Cost:** 5–9 shifts. It saves one premise constructor at call sites but creates
more generic proof work inside O6. It is weaker as authenticated capital and is
not preferred over A1.

### Option A3 — four-side explicit classification

Require a disjunction pairing source and moved skippability, for example
`(left internal, movedLeft internal)` or `(right internal, movedRight internal)`,
plus external matching evidence when the other side is root.

**Consumer-neededness:** sufficient, but it is a manual expansion of a
`SameExternalOrchestration` derivation.

**Producer-suppliability:** strong at O19 block nodes; feasible at stable O17
nodes after the same moved-root lemmas.

**O5 impact:** none.

**Cost:** 5–8 shifts and a wider, less readable interface. A1 already packages
exactly these cases using the immutable relation, so A3 is not recommended.

### Option B1 — sealed `ExternalOrderNeutralCrossing` producer record

If direct A1 production cannot be made stable at O17, introduce a research-only
record indexed by the exact source pair and diamond. It would store the pair-local
`SameExternalOrchestration` plus occurrence-authenticated classification showing
which O17/O19 selected node produced it. Only the stable sorter and whole-block
producer could construct it.

**Consumer-neededness:** exact and more provenance-rich than A1.

**Producer-suppliability:** likely, because O19 already carries exact block
positions and O17 owns the stable selection. It must be demonstrated before the
record is authorized.

**O5 impact:** none.

**Cost:** 6–10 shifts due to the new indexed family, origin projections, tests,
and review. Use only if A1's direct witness can be detached from the real sorter.

### Option B2 — place legality on every finite-derivation constructor

Add pair-local external legality to `FiniteAdjacentSwapStep` and
`NonEmptyAdjacentSwap`, then let O6 consume the constructor-owned witness.

**Consumer-neededness:** very strong: every stored derivation node becomes
self-authenticating.

**Producer-suppliability:** O17 and O19 can supply it under the stable strategy,
but every fixture and derivation consumer changes.

**O5 impact:** none.

**Cost:** 8–13 shifts. This is broader than needed because the O6 result already
contains the global external relation. Not recommended as the first repair.

### Rejected alternatives

1. **Caller supplies `SameExternalOrchestration original swappedTrace`:** circular;
   `swappedTrace` is selected by the O6 result. It moves the theorem field outside
   rather than authenticating a local crossing.
2. **Remove `swappedSameExternalInputs` and reconstruct only at the final sort:**
   permits illegal intermediate root permutations, breaks per-derivation
   composition, and transfers the same obligation to O17/O19/O20.
3. **Weaken immutable `SameExternalOrchestration`:** outside scope and wrong for
   Theorem 73, whose premise intentionally fixes external input order.
4. **Narrow O5:** wrong layer. The checked local commutation is valid; only its
   observational splice applicability is restricted.

## 4. Tracked adversarial evidence

`research-tests/DGamma/R17FullResultImpossibility.idr` is the reviewer's total
proof, copied without weakening. It independently provides:

- the two-node occurrence-fold empty-suffix argument;
- transport of the actual result's external relation to the exact swapped pair;
- exhaustive inversion of skip-left, skip-right, and match-external; and
- `suffixFreeDistinctRootInsertResultImpossible` for the repaired current
  `AdjacentSwapResult`.

It is a positive module: successful typechecking means the counterexample theorem
is proved. Unlike the historical R16 test, it needs no retired local record because
it targets the current unchanged external-order field.

## 5. Recommendation and requested gate

Authorize revision 18 **Option A1**, conditionally in this order:

1. add tracked genuine producer probes first, without declaration changes:
   internal/internal block crossing, stable internal/root and root/internal
   crossings, and root/root rejection;
2. stop for a new audit if moved root ORetire/ORemove classification is not
   constructible from checked transitions;
3. only after the probes pass, add the single erased pair-local
   `SameExternalOrchestration` premise to `adjacentSwapSuffixSpike`;
4. leave the occurrence-fold hole, `AdjacentSwapResult`, all local diamonds/O5,
   `src/`, CP3, and all unrelated hole signatures unchanged;
5. update the frozen manifest, runner/auditor, and plan; then obtain a scoped
   revision-18 adversarial review before O6 proof work resumes.

This is a narrowing, not new operational authority: the proof is erased, indexed
to the actual checked pair and moved transitions, and consumed by an existing
result field.

## Status

- Revision-17 endpoint-control repair: **ratified**.
- O5 local diamond: **proved for all nine O/O pairs**.
- O5 full-result splicing: **blocked at O6 external-order applicability**.
- Generic O6 suffix declaration: **known false for distinct root/root**.
- Stable O17/O19 requested crossings: **audited as not needing root/root, but
  producer lemmas remain to be constructed under revision 18**.
- Research holes: unchanged at 21, split `6/4/8/2/1`.
