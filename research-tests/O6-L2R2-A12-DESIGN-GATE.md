# L2R2 — CANDIDATE A12: forced root input between extended blocks

Status: **CHECKED native countershape; design GATE, not an unconditional normalization theorem or a paper erratum.** No attachment grammar has been defined. Production and frozen research statements are unchanged.

## 1. Exact native evidence

All modules below are in `research-tests/O6-L2R2-Sources/DGamma/`.

- `L2R2SmallStates.smallComponent`, `smallState`: explicit native-operation state expressions; no recursive checked-evaluator state builder. Names are parent **0**, own child **1**, unrelated actor **2**, late root **3**. Child1 and root3 declare the same provision key `True`; parent0 and actor2 declare none. Programs/dependencies are empty and world is `Unit`.
- `L2R2SmallExecution.smallNativeExecution` (C4, `4e6311ed`): source well-formedness, seven checked original edges, two checked alternate edges, exact alternate world/ordered-bindings equality, and native insertion rejection initially and after retirement. This was the specifically authorized C4 two-file bundle.
- `smallTrace` (C5, `e1b69f8e`) is the literal-endpoint trace to `smallState 7`:

| Physical cut | Next checked action | Meaning |
|---|---|---|
| 0 | `LBegin 0` | Parent begins |
| 1 | `LAdvance 0 / LFinishTag` | Parent finishes its empty program |
| 2 | `ORetire 1` | Own child is retired; its declaration STILL occupies `True` |
| 3 | `ORemove 1` | Own child is removed; the declaration is freed |
| 4 | `OInsert 3 Root (smallComponent True)` | Root insertion is now native-applicable |
| 5 | `LBegin 2` | Following actor begins |
| 6 | `LAdvance 2 / LFinishTag` | Following actor finishes |
| 7 | end | Literal `smallState 7` |

- `L2R2SmallPlacement.smallRootBirth` locates the root action at **ordinal 4** in that actual trace, with actual prefix and suffix, not in an unrelated tag list.
- `smallAvailabilityTrail` annotates actual states at cuts 0–4. `smallEarlierUnavailable` (C8) is quantified over **every** `earlier : Nat` with `LT earlier 4`, not a finite-sample stand-in. `rootCutCompatible ... earlier ... = False`, including retired-child cut3. `smallRootEarliest` (C9, `aec6d46a`) inhabits the actual `EarliestAvailableRootBirth` clause: current compatibility plus all earlier exclusions.
- `smallStrictPlacementRejected` (C10, `f56f7a69`) refutes frozen `CanonicalInputPlacement` **for every support state and order**, because `rootGenerationBeforeLifecycle` would require the actual root ordinal4 to precede actual Begin0 ordinal0.
- `L2R2SmallBlocks.smallExtendedBlocks` (C12, `f18f1f00`) simultaneously constructs:
  - parent0's unchanged extended block with exact range **[0,4)**, whose body includes own-child Retire1 **and** Remove1;
  - actor2's extended block with exact range **[5,7)**;
  - physical `BlockBeforeExtended` connecting them;
  - **`transitionCount (extendedBetweenBlocks physicalOrder) = 1`**;
  - an actual `LocatedActionOccurrence` of Root Insert3 inside that gap.

Thus the physical child operations are already inside their parent's extended body. No child-operation relocation remains in this fixture; doing A10's relocation does not itself account for the root edge.

### Important limits of this evidence

This is a native, well-formed-source, real-trace countershape to an inference from **extended block grammar + this root's earliest-compatible placement alone** to zero physical gap. It is NOT a complete inhabitant of `AvailabilityAwareCanonicalInputPlacement`, a full `ActorBlockDecomposition`, `CanonicalSchedule`, `ReplayInvariantBundle`, reachability from an empty registry, registration-protocol history, or final quiescence. In particular root3 has no lifecycle block in the seven-edge trace. The proof does not refute a stronger theorem whose additional premises exclude this trace. It does show what those premises/normalization machinery must explain rather than assume.

“Old rejects/new admits” means the checked **old canonical-placement rejection versus new actual earliest-root clause admission**, not admission of the entire new canonical package. The distinction is intentional.

## 2. Why this is A8 × A10, not a zero-gap theorem

`CP5AvailabilityAwarePlacement.rootDeclaredProvisionsFree` (line17) matches native O-Insert's **declaration** occupancy. Inactivity and retirement do not free declarations. `rootCutCompatible` (line68 onward) requires availability at every crossed state and crosses no actual root input. The endpoint is checked too.

The inherited `ActorLifecycleOnlyExtended` permits lifecycle actions of the actor and selected own-child orchestration; it does not absorb unrelated **root** orchestration. Its larger parent body can end at the freeing Remove, while the correctly earliest root remains just outside. Earlier root-placement normalization cannot simply move this root before the freeing action: the actual guards reject it there.

The retained interim theorem `L2R2ConditionalGap.extendedZeroGapWithoutRoot` is therefore deliberately conditional:

1. a residual-coverage obligation `RemainingGapHeadIsRoot` says every nonempty supplied physical gap starts with actual root orchestration;
2. `NoRootOrchestration` excludes such an edge in the gap;
3. count transport connects that supplied gap to the actual ordered blocks (use the actual gap and `Refl`).

The conclusion is zero count. Neither coverage nor the no-root premise is generated by L2R2. **No-root is stronger than merely “no forced root.”** Replacing it by no-forced-root still requires proving that any remaining root is forced, including external-input-order barriers and chains of roots.

## 3. Existing proof surfaces that a design must respect

- Paper intent, **as reflected in the existing mechanization**, is to obtain a canonical schedule and then permute independent actor blocks while retaining external orchestration order. CP3's old grammar/placement separates root inputs from actor lifecycle blocks. This shift does not quote or claim to have re-audited the paper text: `paper/cordis-paper.txt` is absent in the lane2 worktree, and no main-worktree file was accessed. Exact paper-language review remains with the owner/reviewer; this is not an asserted paper erratum.
- Frozen CP3: `ActorLifecycleOnly` **1786**, `LocatedOpenEpisodeBlock` **1824**, `BlockBefore` **1873**, `CanonicalInputPlacement` **3156** (strict clauses **3164/3173**), `CanonicalSchedule` **3240** (`canonicalBlock` **3256–57**, `inputPlacement` **3265**).
- Frozen O19 `CP5O19SurfaceSpike.AdjacentActorSwapSafety` **113–145** carries **`safetyBlocksAdjacent : transitionCount (betweenBlocks safetyBlocksOrdered) = 0`**. Adjacency in an actor *order list* does not prove this physical property. The A12 gap1 witness cannot be fed to that field. Also, an extended/attached block is not definitionally a frozen old block.
- O17 root work in `CP5ConfluenceCanonicalSortSpike`: `CanonicalRootInsertionHoist` **1583**, `canonicalRootInsertionHoistFromDiamond` **1596**, producer **1617**, located moved root **1638**. The existing full package owns a diamond, replay, and actual moved action; a new availability-aware normalizer must still discharge corresponding operational obligations, not merely sort an action word.

## 4. Design comparison — descriptions only, NO new grammar

### ATTACH — provisionally preferred

Treat the availability-forced external root insertion (and, where required, the following externally ordered root-input bundle) as physically attached to the block containing its freeing action.

This is an annotation/grouping choice, **not** a change from `Root` to `ChildOf parent` at runtime. An actual forcing/release witness, occurrence linkage, exact input order, and availability throughout crossed states are needed. A bare extra “arbitrary root allowed” constructor would be unsound as a normalization argument.

Benefits:
- Provides a direct account of the gap edge within a larger physical unit; the fixture's first unit would extend through Root3.
- Aligns physical adjacency with the intended later whole-unit permutation.
- Keeps root placement immediately after its genuine availability barrier, rather than claiming impossible global “all roots first.”

Costs/open obligations:
- Requires a changed block grammar or an explicit attached-block wrapper and propagated block endpoints/decompositions. It does **not** inhabit frozen O19 safety unchanged.
- O19 crossings must handle external root actions of a third actor inside the unit, preserve external orchestration and generation identities, and prove all real checked successor/availability conditions.
- A root can need multiple keys freed by different blocks. Attaching to the *last* release alone does not license moving another contributing release behind the root. The selector and crossing safety still need these availability dependencies.
- Multiple roots may be order-forced after one availability-forced root; grouping just the first insertion may leave residual gaps.
- Root Retire/Remove barriers must be classified from actual source states, not raw actor/tag guesses.

### PREMISE — honest interim result, insufficient by itself as an algorithm

Keep the inherited extended grammar. State zero gap only under explicit coverage and exclusion of intervening forced roots (or the currently proved stronger no-root condition).

Benefits:
- Smallest additional statement surface; does not pretend gap1 is zero.
- Retains a useful conditional adjacency lemma for genuinely unobstructed pairs.

Costs/open obligations:
- A conditional theorem alone does not supply the next actor-order swap. An inversion selector must handle a root between otherwise neighboring blocks.
- A dependency-aware macro can move the other block across the **freeing-block + root** unit. One possible intermediate arrangement temporarily postpones the root so the actor blocks become physically adjacent; that intermediate need not satisfy earliest-root placement. A macro proof must restore placement and preserve inputs/support at its boundary.
- Moving a lifecycle block left across a root can increase the root-birth inversion count. Thus the O17 root-only decreasing measure is not, by itself, a decreasing measure for such macros. A phase/lexicographic argument and operational safety are needed.
- Even this route eventually introduces unit-level movement machinery. It saves grammar initially, not the underlying dependency proof.

### PLACEMENT — effectively ATTACH, not a free grammar-preserving alternative

Strengthen placement to put a root immediately after the actual freeing action (subject to external root-input order and all required keys).

Benefits:
- Strongly exposes the intended availability boundary and is consistent with the native cut4 fixture.

Costs/open obligations:
- In this fixture the result is still `[parent block] ; Root3 ; [next block]`: zero old extended gap does not follow.
- If the freeing action occurs inside a parent episode with later lifecycle work, the immediate insertion would lie *inside* that episode. The inherited body grammar rejects the unrelated root edge; splitting the episode is not automatically a valid maximal open block.
- Therefore physical zero-gap integration needs attachment/wrapping anyway, plus the same multi-key and root-order qualifications as ATTACH.

### Relative CP3 diff surface (NOT a drafted patch or measured LOC)

| Choice | Additional CP3 schema surface beyond already-authorized A8/A10 variants | Downstream cost |
|---|---|---|
| ATTACH | Body grammar or wrapper; located block endpoint/body fields; ordered-block/decomposition references; canonical block reference. The A8 input-placement change remains. At least the **1786/1824/1873/3240** families are implicated. | Broad: O19 unit crossings, coverage/zero-gap producer, support/input/generation transport, availability-aware selection. |
| PREMISE | Potentially **zero extra grammar definitions**; one additional normal-form/zero-gap premise if stored in the schedule. A8/A10 changes are still required. | Not small: selector/macro proof must move across root+block and manage temporary noncanonical placement. Frozen O19 can only be called after real zero-gap evidence is produced. |
| PLACEMENT | A8 placement clause becomes stronger, but zero physical gap additionally needs the ATTACH block/wrapper surface. | Essentially ATTACH, with a stricter placement producer. |

No exact LOC estimate is warranted before choosing a representation and proving the required bridges. These are signature dependency families, not a claim that changing five names completes the integration.

## 5. Approved snapshot root-phase result and exact production signature delta

The owner separately authorized a **snapshot-level research root phase** after literal uniqueness-proof identity blocked the small exact fixture. This authorization does not authorize an attachment grammar or a silent production edit.

`L2R2RootSnapshot.AvailabilityRootSnapshotExchange` (C13) is the documented counterpart of `CP5L2R1RootExchange.AvailabilityRootExchange:19`:

- OLD alternate late edge: `checkedApplyAction ... = Just (tag, finalState)`.
- APPROVED RESEARCH variant: expose `newFinal`; prove the actual late edge is `Just (tag, newFinal)` **and** `runtimeSnapshot finalState = runtimeSnapshot newFinal`.
- Runtime equality means **world + ordered bindings**, not just a key set, tag count, coeffect lookup sample, or assumed proof irrelevance.

The exact fixture failed because root insertion before Begin2 mentioned an **Inactive2** head in its erased `UniqueKeys` certificate, while insertion after Begin2 mentioned **Reloading2**. C4's authorized native-operation alignment makes each path real but does not manufacture equality between those certificates. The exact old C13 fixture is **parked**, not proved by this new record.

Checked new capital:
- `smallRootSnapshotSquare` (C14, `fc95fdb3`) supplies **both** alternate checked edges and availability on actual cuts4/8. Original final state9 and swapped final state6 have exact equal runtime snapshots.
- `supportSetAcrossSnapshot` (C15, `31a4f060`) proves equality of the **entire executable support set** from snapshot equality. It is not yet the full dependent `LinearizesSupport` transport theorem.
- `beginSnapshotRootDecreases` (C16, `ae92c7b3`) proves exact-one decrease for the actual two-edge pair, arbitrary prior count, no suffix.
- `rootPhaseFromSnapshot` (C18, `e95b397c`) constructs a native swapped trace in an arbitrary unchanged physical prefix, carrying runtime/support equality and that local decrease. The authenticated square is an **explicit input**. There is no generic square dispatcher, arbitrary-suffix replay, `ReplayInvariantBundle`, global placement producer, or full O17 normalizer hidden in the type.
- `smallRootPhaseEvidence` (C20, `141a1d80`) uses the actual four-edge freeing prefix and both full six-edge runs. Actual-state annotated root-birth inversion counts are **3 → 2**, with exact-one equality. Counts are not on an unlinked action word and no prior-count assertion is substituted. Two blocked inversions remain; zero is not claimed.

## 6. Owner gate / next-shift decision

**Provisional recommendation: ATTACH, with PLACEMENT as its intended placement discipline.** Retain the conditional PREMISE theorem meanwhile. Before any new variant grammar, the owner must choose the representation and accepted downstream O19/root-phase signature changes. A release/availability dependency policy (including multi-key and ordered-root bundles) is part of that gate, not an implementation detail to guess.

This shift has deliberately stopped at B22/C20 and has defined no attached-root grammar. The checked A12 witness and scoped snapshot phase are review capital for that decision.
