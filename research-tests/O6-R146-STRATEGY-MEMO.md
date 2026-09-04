# O6 R146 — Theorem 73 strategy memo

## Scope

This is a paper-and-surface review only.  It changes no Idris source, attempts no
proof body, invokes no compiler, and does not inspect `build/`.  It decides the
next research direction after R145's stopped probes and records the surface
revision that should precede another O21 body attempt.

Baseline for this memo: branch `cp5-thm73-scoping`, starting HEAD
`460d76bb8d0a1386b202bd887d376cb0851f9da8`; production remains frozen against
`34b21c9`, including CP3 blob
`2c697e532e83989de8591fa6a4378747c6a501c0`.  The research census is still 13
holes: CanonicalSort 2 / CrossTrace 4 / DeletionChain 6 / LocalDiamond 0 /
RenamingComposition 1.

## Decision 1 — O9 takes route B

**Decision: take route B, a generation-aware pre-interval/crossing exclusion.
Do not add route A's overlapping-activation predicate.**

This is a semantic decision from the paper's operational rules, not a claim
that the Idris theorem has been proved.  R145's fixture remains correctly
classified as mechanically inconclusive.

### Why the paper chooses B

The relevant chain is already present in the paper.

1. Definition 53 and Table 1 say that an episode begins only at `L-Begin` and
   ends only at `L-Unload` (Lemma 54(4)).
2. `L-Begin` resolves the target and stores the resulting provider-name view in
   the lifecycle state.  Lemma 54(2) says that committed view is constant for
   the whole episode and is discarded only at `L-Unload`.
3. Definition 50 defines `relied_n` from *other installed fibers' committed
   views*.  The guarded `L-Unload(n)` rule requires `not relied_n` before it can
   apply.
4. Consequently, if a consumer has committed a dependency to `n` and stays
   installed through an attempted `L-Unload(n)`, its committed view witnesses
   `relied_n`; that unload is impossible.
5. A later activation of the same fiber name requires the earlier selected
   activation to have reached `Inactive`, and only `L-Unload` makes an installed
   fiber inactive.  Thus a consumer episode crossing from before the selected
   activation cannot have committed the selected provider generation (or a
   prior same-raw-name generation that would have had to unload while the
   consumer stayed installed).

The paper uses exactly this exclusion, albeit in compressed prose, in the last
paragraph of Lemma 72: a surviving step can read the deleted fiber through
`target` only for a dependency edge; the relevant consumer has no closing
episode, its committed view is fixed, and the deleted provider cannot be the
provider selected at its begin.  The `relied` guard is the operational reason a
committed provider cannot disappear underneath the installed consumer.
Preservation Theorem 59(4) states the same invariant globally.

Route A would strengthen the deletion candidate with a new prohibition on an
overlapping activation.  That is not a premise of Lemma 72, is stronger than
the operational invariant, and would risk making Theorem 73's maximal-episode
selection unusable.  The paper expects the overlap shape to be *derived away*,
not assumed away.

### Idris-facing theorem decomposition for the next shift

Do not introduce a broad new deletion predicate.  Add the minimum producer-side
lemmas needed to connect the existing, already-proved operational capital:

1. **Pre-interval classification.**  For a foreign installed segment crossing a
   state inside the selected closed episode, classify its opening as either
   inside the selected interval or before it.  Preserve the exact prefix/suffix
   witnesses; do not compare only `Nat` ordinals.
2. **Closing/reissue localization.**  In the before case, use registration
   discipline plus `closingOccurrenceGivesLocatedActivation` to locate the
   activation whose committed view is being transported.  Raw-name reuse must
   be split by `RegistrationGeneration`, not by name equality alone.
3. **Committed-provider exclusion.**  Reuse
   `crossingActivationExcludesSelectedProvider` where a closed consumer
   activation is available.  Where the consumer stays installed to the selected
   unload, build `SelectedUnloadRelianceAnchor` and close the selected-provider
   branch with `committedSelectedContradictsUnload` (or its existing
   `relianceAnchorProviderExcluded` wrapper).
4. **Adapter into O9.**  Convert the exclusion into the precise
   `providerCandidate = False` / target-frame equality consumed by the
   deletion replay step.  Keep all generation casts at this adapter boundary.

The intended research theorem is therefore of the following shape, described
without committing to an Idris spelling:

> Given the selected located closed episode, aligned execution from the empty
> registry, well-formedness, `NoDependentClosingEpisode`, and a foreign
> installed trace that crosses the selected interval, every dependency key of
> the foreign fiber excludes the currently selected provider.  If the raw name
> was reused, the exclusion is indexed by the registration generation current
> at each endpoint.

Most of this statement already exists as
`crossingActivationExcludesSelectedProvider`; the missing work is the exact
pre-interval decomposition and the generation-aware adapter demanded by O9.
No new public premise is recommended.

### Stop condition

Route B gets one focused surface pass and then one 3-attempt proof/fixture
budget in the next implementation shift.  Stop and reconsider only if an exact
constructor case shows that an accepted `L-Unload` can coexist with an
installed committed consumer, or that the candidate hypotheses cannot produce
the necessary located activation/generation.  An elaboration failure in a
large evaluator fixture is not such evidence.

## Decision 2 — make O21's fixed bijection constructor-owned

### The defect

`ReplayedCanonicalEndpointBridge` currently stores:

- a caller-chosen `replayBridgeBijection`, and
- an erased equality `replayBridgeBijectionFixed` proving that choice equal to
  `currentNameBijection (endpointRenaming sameInputs)`.

Every semantic field is then indexed by the caller-chosen value.  O21 must
rewrite those fields across the equality before the accepted endpoint
renaming can consume them.  R145 showed that this propositional boundary, not
new semantic information, is the final surface obstruction.

### Required surface

Replace the record with a **record-shaped sealed data family whose sole
constructor stores all clauses directly at the canonical bijection**.  In
schematic form:

```idris
expectedBridgeBijection sameInputs =
  currentNameBijection (endpointRenaming sameInputs)

data ReplayedCanonicalEndpointBridge ... where
  MkReplayedCanonicalEndpointBridge :
    (0 ambient : ... expectedBridgeBijection sameInputs ...) ->
    (0 tables : ... expectedBridgeBijection sameInputs ...) ->
    (0 controls : ... expectedBridgeBijection sameInputs ...) ->
    (0 generatedBirths : ... expectedBridgeBijection sameInputs ...) ->
    ReplayedCanonicalEndpointBridge ...
```

Export record-style eliminators with the old semantic names.  In particular:

```idris
replayBridgeBijection bridge = expectedBridgeBijection sameInputs
replayBridgeBijectionFixed bridge = Refl
```

The equality

```text
replayBridgeBijection bridge =
  currentNameBijection (endpointRenaming sameInputs)
```

is thus emitted by the bridge constructor and reduces to `Refl`; it is no
longer evidence supplied by a bridge caller.  This is preferable to merely
moving the same equality into another record because O21 needs the payload
indices themselves to be definitionally fixed.

If Idris record projection ergonomics make a `data` family undesirable, the
acceptable equivalent is a one-constructor exact-index family nested inside
the record, with all later fields pattern-matched under that constructor.  A
free `NameBijection` plus equality field is not acceptable.

### Old-to-new clause map

| Current bridge clause | Revised clause | Consequence |
|---|---|---|
| `replayBridgeBijection : NameBijection name` | Remove constructor argument; exported eliminator returns `currentNameBijection (endpointRenaming sameInputs)` | A producer cannot choose a different bijection. |
| `replayBridgeBijectionFixed : replayBridgeBijection = ...` | Exported constructor-owned `Refl` (or an exact-index constructor field) | No consumer rewrite is needed. |
| `replayBridgeAmbient` | Same proposition, indexed directly by the expected bijection | O21 consumes it without `replace`. |
| `replayBridgeTables` | Same proposition, indexed directly by the expected bijection | Pointwise table transport is definitionally aligned. |
| `replayBridgeControls` | Same proposition, indexed directly by the expected bijection | Control-field comparison is definitionally aligned. |
| `replayedGeneratedBirthMatched` | Same quantified occurrence/origin/birth equation, with every `renameForward` using the expected bijection directly | Wrong-birth protection is retained; no arbitrary map can be smuggled in. |

No clause is weakened and no new public semantic premise is introduced.

### Producer and consumer migration

Direct bridge producers/assemblers:

- `canonicalSchedulesConvergeSpike` must construct the sealed bridge using only
  the four canonical clauses.
- `canonicalConvergenceFromBridge` and `MkCanonicalConvergenceResult` retain the
  bridge as-is; only any explicit constructor spelling changes.
- `R8BridgeAuthenticatedDirectionPositive.rebuildAuthenticatedBridge` removes
  the first two constructor arguments and rebuilds the four canonical clauses.
- `R8BridgeWrongBirthNegative` must be updated to the new constructor arity;
  its deliberately missing generation equation must continue to be rejected.

Direct consumers:

- `replayedCanonicalToOriginalEndpointSpike` and its local
  `pointwiseOutsideBoth` helper switch from a caller-selected bijection to the
  expected one.  The R145 reindexing obstruction disappears.
- `originalEndpointsConvergeSpike` still passes `convergenceBridge`; its public
  result type is unchanged.
- `CanonicalConvergenceResult.convergenceBridge` retains the same semantic
  type.
- `R8WrongTraceBridgeNegative`, `R8WrongOccurrenceBridgeNegative`, and
  `R8PublicScheduleCannotReachBridgeNegative` should retain their negative
  behavior.  They are boundary tests, not alternate producers.  Re-run the
  wider R8 pipeline tests after the surface patch because `R8FullPipeline`
  reaches the bridge transitively.

The constructor should remain non-public if all legitimate construction can be
centralized in the CrossTrace producer; otherwise export the constructor but
make its exact indices unforgeable as above.  Constructor ownership here means
ownership of the bijection choice, not hiding the four real proof obligations.

### Withdrawal cases after the cure

The fixed-bijection cure is sufficient for the **outside-both** O21 branch only.
The left-withdrawn, right-withdrawn, and both-withdrawn branches still need
operational generation capital.  They do **not** appear to need new caller
premises:

- `AcceptedDeletionScannerCapital` already owns the accepted left/right
  registration scans and exact withdrawn-generation sets;
- `CanonicalRegistrationTree` authenticates the deleted births and their
  canonical absence;
- `CurrentEndpointRenaming` already classifies an exact current generation as
  mapped or vestigial; and
- the bridge supplies canonical endpoint domain/control/birth agreement.

What is missing is a producer-side endpoint lemma extracting the exact current
`RegistrationGeneration` from an original endpoint lookup and the accepted
scan, followed by an induction that rules out the mapped branch when the
canonical endpoint is absent.  Because raw names may be reused,
name-membership or “some withdrawn generation with this name” is insufficient.
If the accepted scanner currently lacks an exported endpoint-domain/current
coherence theorem, enrich **its producer-owned capital** with that derived
field; do not ask O21 callers for a chosen generation or vestigial witness.
This is a missing-capital risk, not a reason to weaken the bridge.

## Stop-map triage

The labels below are decisions about the current theorem surfaces, not proof
results.

| Hole / cluster | Classification | Evidence and disposition |
|---|---|---|
| O14 `sortClosingFreeTraceSpike` | **(ii) Missing-capital chain** | R134–R135 isolated ordinary stable rank-sort mechanics: rank membership, head/tail lookup transport, and strict `BeforeIn` reconstruction.  No counterexample or bad public premise was found.  Keep parked until the deletion gate moves, then resume with a named producer-owned sorting invariant rather than another monolithic body. |
| O17 canonical schedule operationalization (the R144 sort-base obligation feeding CrossTrace) | **(ii) Missing-capital chain** | R144 found no surface defect.  A pure canonical permutation is not enough: the producer must carry intermediate states, target constancy, yield stability, and local swap derivations.  This is substantial operational stable-sort capital, not an elaborator-only fix. |
| O19 `operationalAdjacentBlockSwapSpike` | **(iii) Suspected-false statement** | `AdjacentActorSwapSafety` permits a provider-before-dependent-consumer shape, while the consumer's `L-Begin` is inapplicable before the provider becomes active.  The R144 fixture stopped before packaging the full counterexample, so this is not “refuted”, but another body attempt is unjustified.  Revise the surface to require support incomparability / both-direction applicability, or prove that the actual O19 producer can supply that stronger condition. |
| `canonicalSupportOrdersMatchSpike` | **(ii) Missing-capital chain** | Same inputs plus the two authenticated canonical schedules should determine the same active support/tree up to the generation bijection, but the pointwise current-generation, parent, dependency, and provision transport is not yet exposed.  No evidence the result is false. |
| `selectOperationalCanonicalPermutationSpike` | **(ii) Missing-capital chain, blocked by the O19 revision** | It needs the finite linear-extension theorem together with an operational certificate for every adjacent incomparable swap.  Do not attempt it while O19 accepts the weaker safety shape. |
| `canonicalSchedulesConvergeSpike` | **(ii) Missing-capital chain** | Its remaining payload is the exact replayed-left-to-canonical-right bridge: ambient, tables, controls, and generated-birth correspondence.  O21's constructor cure removes a later reindexing defect but does not manufacture these O20 clauses. |

None of these six is classified as an elaborator-only fix.  None is yet put in
category (iv) “genuinely hard/park”: O14 and O17 are expensive, but their
missing invariants are identifiable.  O19 is parked specifically for a surface
decision, not because a correct statement is intractable.

## Ranking of all 13 holes by expected unlock

This ranking weighs dependency fan-out first, then confidence that the surface
is sound.  Mirrored obligations are listed separately because the census does.

1. **`enrichDeletionChainStepSpike` (Deletion O9 main gate).**  Route B unlocks
   the five-hole deletion tail and therefore every canonical/cross-trace stage.
2. **`deletionStepOperationalOccurrenceFoldSpike` (O9 prerequisite).**  Exact
   survivor/source ordinal and occurrence capital is needed by the enriched
   step and is independent of the route-B semantic exclusion.
3. **`deletedClassificationForcesLeftScannerDiscardSpike` (O9 accounting
   prerequisite).**  Turns authenticated deleted births into the left scanner's
   exact discard list.
4. **`deletedClassificationForcesRightScannerDiscardSpike` (mirror).**  Same
   role on the surviving/right scan; implement only after the left induction
   fixes the recursion pattern.
5. **`replayedCanonicalToOriginalEndpointSpike` (O21).**  The fixed-bijection
   revision is bounded and removes a known false abstraction boundary; it is a
   good independent lane while O9's proof decomposition is fresh, although it
   does not unlock the upstream pipeline.
6. **`deleteClosingEpisodesCoreSpike` (O10).**  Structural well-founded
   iteration becomes available once the enriched one-step package is real.
7. **`assembleClosingFreeAccountingSpike` (O11).**  Folds the chain's endpoint,
   replay, and withdrawn-generation accounting after O10.
8. **`supportOrderingSpike` (Canonical ordering producer).**  Finite support
   ordering is upstream of both O14 and CrossTrace matching and is more local
   than the sorting proof.
9. **`sortClosingFreeTraceSpike` (O14).**  Resume the named stable-sort invariant
   only after the accepted closing-free trace and ordering are available.
10. **`canonicalSupportOrdersMatchSpike`.**  First cross-trace bridge from two
    completed canonical capitals; it unlocks permutation selection.
11. **`operationalAdjacentBlockSwapSpike` (O19).**  High downstream fan-out but
    deliberately ranked below matching until its suspected-false safety surface
    is revised and negative-tested.
12. **`selectOperationalCanonicalPermutationSpike`.**  Depends on the corrected
    O19 local step plus matching and the linear-extension decomposition.
13. **`canonicalSchedulesConvergeSpike` (O20).**  Final canonical endpoint bridge;
    broadest payload and no further research hole can consume it until all
    earlier CrossTrace capital exists.

The O21 rank reflects *bounded risk retirement*, not graph order.  In a strictly
serial end-to-end proof plan it remains after O20; doing its constructor revision
early prevents O20 from being implemented against an immediately obsolete
bridge.

## Recommended next shift

Run a **two-part implementation shift, with O9 as the only proof gate**:

1. First make the bounded O21 sealed-bijection surface revision and update its
   direct fixtures.  This should be a surface/build commit only; do not attempt
   the three withdrawal branches in the same budget.
2. Then implement O9 route B's pre-interval classification/adapter, reusing the
   production crossing and reliance theorems.  Attack the left scanner discard
   induction and operational occurrence fold before the monolithic enriched
   step; derive the right scanner result by an explicit mirror once the left
   recursion is stable.

Do **not** spend the next shift on O14/O17, and do not attempt O19 before its
stronger swap premise has a paper-consistent surface and negative fixture.

## Theorem-risk debt register

| Debt | Risk | Required discharge |
|---|---|---|
| **Lemma 72 compresses the crossing argument.**  “No surviving step loses a premise” skips the explicit pre-interval/reissue split. | High for O9 | Generation-indexed route-B lemma using committed-view persistence and the guarded unload contradiction. |
| **Raw names are reusable.**  Paper prose often reasons by a name where Idris must distinguish registration births. | High for O9/O20/O21 | Never infer a current birth from raw-name membership; route through accepted scanner/current-generation bijections. |
| **O19's local-swap surface is too weak.**  Map independence does not make an early dependent `L-Begin` applicable. | High | Require support incomparability and/or a two-sided applicability diamond; negative-test the provider/consumer shape. |
| **Theorem 73 uses the linear-extension transposition lemma without stating its constructive hypotheses.** | Medium-high for O17/O19 | Finite decidable support set, strict acyclic order, and a producer returning adjacent incomparable transpositions. |
| **Yield stability is stronger than commutation of state maps.**  Definition 60's second clause fixes inverse/continuation/registered component across interleavings. | High for O17/O20 | Carry producer-owned per-iteration yield and registration correspondence through every swap. |
| **Cross-trace “same registrations” is asserted at tree level in the paper.**  Exact occurrence and birth correspondence is not immediate from same external orchestration. | High for O18/O20 | Induct over authenticated traces and preserve `RegistrationGenerationBijection` equations at each generated insertion. |
| **Vestigial removal and fresh-name reuse interact.**  Lemma 57(2) explicitly excepts an insertion drawing the removed name or colliding with its provision. | High for O21 | Exact current-generation/absence induction; no raw-name-only endpoint theorem. |
| **The bridge previously exposed a caller-selected bijection.** | Medium, revision-shaped | Apply the sealed constructor surface before another O21 attempt; retain wrong-birth and wrong-trace fixtures. |
| **`≈` and `≃` forget different state halves.**  Paper confluence concludes both, while research bridges mix exact ambient/table equality with control equivalence. | Medium | Keep clause-by-clause accounting explicit and document every conversion; do not silently collapse the relations. |
| **Stable rank sorting is not supplied by the library theorem at the dependent indices O14 needs.** | Medium | Named rank/head/tail invariants and strict-before reconstruction, with no new semantic premise. |
| **Constructive maximal/minimal selection is hidden in paper prose.** | Medium | Expose finiteness, decidable membership/order, and measure decrease in O10/O13 rather than appealing to existence. |
| **The paper's claim that the base calculus also satisfies Theorem 73 drops the unload guard.**  That statement removes the operational fact used by route B and deserves separate scrutiny. | Medium, paper erratum candidate | Scope the current mechanization claim to the guarded calculus; audit the base-calculus variant independently before recording it as proved. |
| **Stopped evaluator fixtures are not semantic countermodels.** | Process risk | Treat only a fully checked negative witness or constructor contradiction as refutation; keep attempt budgets local to fixtures. |

## Gate result

**GO for route B and for the O21 constructor-owned fixed-bijection revision.**

**NO-GO for route A, another unchanged O19 body attempt, or resuming O14/O17 in
the next shift.**  All statements here remain strategy decisions until a later
Idris build validates their implementations.
