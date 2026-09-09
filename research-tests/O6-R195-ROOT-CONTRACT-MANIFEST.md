# R196 proposed root producer contract — NOT APPLIED

R195 owner decision: defer the three insufficient visibility exports in
O6-R195-ROOT-VISIBILITY-MANIFEST.json. Strengthen the storing producer contracts
instead. This document is planning evidence, not approval to edit LocalDiamond,
not an inhabited new field, and not a convergence proof. R195 LocalDiamond is
byte-identical to981e6137, SHA256
`f77f66a3e3a62f2ff757709f08d1488a25d54d425af74dcec4c2c0f0ed28c6fd`.

## Necessity and minimal choice

`r195ReplayRecordDoesNotOwnRootLaw` is a checked constructive necessity witness:
a FULL ActionRegistrationReplayCorrespondence on a checked root singleton need
not preserve that root's ordinal. The record constrains generated births only.
This is NOT a protected-canonical-convergence counterexample.

Prefer the **all-root law directly**, not equality of two dependent records or
`storedMapIsBuilder`. This avoids a forward reference to the private builder,
function extensionality, and identifying arbitrary supplied maps with a default
implementation. Leave generic ActionRegistrationReplayCorrespondence unchanged;
it is intentionally insufficient in isolation. No new public-export keyword is
needed merely to name the proposed stored field's proposition.

## Exact proposed erased fields

### 1. AdjacentSwapOperationalOccurrenceFold

File `research/DGamma/CP5ConfluenceLocalDiamondSpike.idr`, record2849–2877,
constructor2862. Append after `operationalOrdinalRelation`:

```idris
  0 operationalRootOrdinalPreserved :
    {root : name} -> {component : Component key value world error} ->
    (occurrence : LocatedActionOccurrence (OInsert root Root component) swappedTrace) ->
    (generationForward (replayGenerationRenaming operationalOccurrenceCorrespondence)
      (MkRegistrationGeneration root
        (locatedActionOrdinal (replayActionOrigin operationalOccurrenceCorrespondence occurrence))) =
      MkRegistrationGeneration root (locatedActionOrdinal occurrence))
```

It ties the law to the SAME stored correspondence and occurrence, not to a
separately reconstructed map. All witnesses are erased. Keep existing four
fields unchanged. It is a producer strengthening, not a hypothesis inserted
into a frozen theorem or into O20's result consumer.

**Every current construction site, from a main-tree literal constructor search:**

| Site | Required producer-owned argument |
| --- | --- |
| LocalDiamond27352, `buildAdjacentOperationalOccurrenceFold` | Root specialization of `adjacentOrdinalRelationForward`26670 + `adjacentOriginOrdinalRelation`27168, at the SAME `origin` used by `buildAdjacentActionRegistrationCorrespondence`27280. |
| research-tests/DGamma/R19SuffixFreeFullAdjacentCertificatePositive.idr:340 | Root domain is empty in this two-Advance fixture. Use its actual `twoAdvanceOccurrenceAction`114–138 to contradict OInsert= LAdvance; do not postulate the new field. |

The constructor declaration itself is2862, not a construction. There are no
production, lane-owned, O19Surface, or CrossTrace construction calls.
`AdjacentSwapResult`9174–9210 STORES the enriched fold; it needs no extra field.
Its actual constructor use at27427 receives that fold through
`produceAdjacentOperationalOccurrenceFold`27357–27388/27437; its signature and
call need not change. The private actual map/proof need not be exported if this
root helper is proved in its defining module and only the stored law is exposed.

A proposed top-level helper `adjacentOriginRootOrdinal` should have the SAME
root proposition specialized to `buildAdjacentActionRegistrationCorrespondence
origin`. Its proof is congruence of `MkRegistrationGeneration root` over the
existing all-action ordinal relation; no new permutation algorithm is needed.
If that helper is placed before the builder, spell its map and action-origin
expression directly as in the generated sibling27140/27251. Do not create a
cyclic declaration or use `with`/local aliases. This helper is not implemented.

### 2. DeletionProducerOperationalCapital

File `research/DGamma/CP5ConfluenceDeletionChainSpike.idr`, record4577–4655,
constructor4590. Append after `deletionProducerGeneratedOrdinalPreserved`:

```idris
  0 deletionProducerRootOrdinalPreserved :
    {root : name} -> {component : Component key value world error} ->
    (occurrence : LocatedActionOccurrence (OInsert root Root component)
      (survivingTrace result)) ->
    (generationForward deletionProducerGenerationRenaming
      (MkRegistrationGeneration root
        (locatedActionOrdinal
          (deletionWholeSourceOccurrence
            (deletionWholeOccurrenceOrigin nameEq keyEq original selected episode
              registered episodeStartOrdinal episodeStartLive result occurrence)))) =
      MkRegistrationGeneration root (locatedActionOrdinal occurrence))
```

**Sole actual constructor use:** DeletionChain27495,
`scopedOperationalFromOrdinalSegments`27485–27505. Fill from the SAME
`ScopedDeletionOrdinalSegments` and `ScopedOrdinalSpinePermutationWitness`
which produce its generation map, using `scopedDeletionWholeOrdinal` and
congruence of `MkRegistrationGeneration root`. The generated sibling
`scopedDeletionGeneratedOrdinal`27463–27484 already composes that all-action
ordinal equation with generated-occurrence conversion. Roots need no generated
conversion. No freely supplied all-root oracle may replace this argument.

`scopedDeletionOperationalCapital`27507–27516 obtains these segments;
`scopedEnrichedOperationalCapital`27519–27529 feeds the live enriched result;
`MkDeletionChainStep`27905 retains the capital and its occurrence exactness.
`deletionStepOperationalOccurrenceFoldSpike`4805–4845 need not change the generic
ARRC type: its root law is separately recovered from the new capital field.
`DeletionChainStep.deletionOccurrenceCorrespondenceExact`4878–4881 attaches
that law to the exact stored occurrence correspondence. A defining-module
exported proof helper may be needed to unfold its private action-origin helper;
it must prove this equality from the actual stored field and exactness, not
introduce another premise. No frozen deletionTheoremProof call is involved.

## Consumer chain, including every storage boundary

1. Enriched adjacent fold -> `swappedOccurrenceFold`9401 ->
   `swappedOccurrenceCorrespondence`9413. New stored law projects directly.
2. `finiteDerivationOccurrenceCorrespondence`9555–9565: identity base plus
   R195 `o20ComposeRootReplayOrdinals` at each actual swap result.
3. `sortingOccurrenceCorrespondence` CanonicalSort173–179 uses that finite
   derivation; `blockSwapOccurrenceCorrespondence` O19Surface818–824 does too.
4. Enriched deletion capital -> `deletionOccurrenceCorrespondenceExact` ->
   `closingFreeDeletionOccurrenceFold`29062–29072, identity/composition induction
   -> `reductionOccurrenceCorrespondence`29167–29173.
5. `deletionSortingOccurrenceCorrespondence` CanonicalSort4414–4426 composes
   those exact two maps. `canonicalOccurrenceCorrespondence`4876–4884 eliminates
   the actual IndependentCanonicalSchedule and its producer equation. Result:
   `O20RootReplayOrdinals ... (canonicalOccurrenceCorrespondence capital)`.
6. `operationalPermutationOccurrenceCorrespondence` CrossTrace68–90 composes
   actual block-swap correspondences, and `permutationOccurrenceCorrespondence`
   CrossTrace460–470 projects that operational derivation. Compose its law with
   the left canonical law using R195's checked composition lemma.
7. Only then use `o20RootOrdinalsAttached` with actual original external-root
   occurrence correspondence. Whole paired stage extraction and endpoint cut
   rebasing remain separate obligations even after this contract is inhabited.

No structural step may assume ARRC -> root law; the R195 necessity fixture must
continue to typecheck because the generic record is unchanged.

## Statement fidelity / frozen bodies

No constructor use lies inside the frozen closed O19 body
`operationalAdjacentBlockSwapSpike` CrossTrace30–47, O19Surface, or the frozen
`adjacentSwapSuffixSpike` LocalDiamond27446 onward. The latter calls
`produceAdjacentSwapResult`; enriching its internal fold preserves that call's
signature. Therefore the proposed design requires NO changes to either frozen
body, the four hole statements, A11's record, selector, O21, production, or any
lane-owned baseline module. If implementation discovers otherwise: **STOP and
request an owner-level exception**, do not edit a frozen body silently.

Required immutable adjacent bytes:1470,
SHA256`2d01486bf953f11191b758ac3cfb5722d1d02b1a192b6e552adc8a3f58199ecf`;
statement1154,
SHA256`3aae5a9fbc5b14e0411b4a91e557a6f3dc68c9a6282b9ec2b3fc658cec337adf`.
All additions need an exact approved field/construction-site byte manifest
before R196 edits. No whole-file AFTER hash is asserted for this unimplemented
helper/field series; unlike the rejected three-keyword proposal, it is not yet
an executable replacement manifest.

## R196 execution and resource gate

Supervisor's binding R195 reply: the52GiB LocalDiamond ruling extends to the
owner-gated KEYWORD/FIELD-only strengthening; one declaration per invocation,
LocalDiamond first under the heavy lock, then serialized dependents. Every
other check stays48GiB. No unmonitored or cold build, TTC deletion, or package
rebuild across invalidated caches. Preserve one actual-origin state, zero-hidden
signatures and fully instantiated native lookups.

The field and its constructor argument must be one approved existing-surface
revision: changing only the record leaves its constructor calls ill-typed.
A new helper is a separate one-declaration micro-unit checked before that
revision; the R196 gate must explicitly confirm whether the52GiB FIELD-only
exception covers the necessary helper check too. Without that clarification a
changed mathematical helper remains under the default48GiB rule. Do not infer a
blanket52GiB limit for unrelated changed LocalDiamond code.

The visibility proposal's conservative transitive invalidation inventory has
241 modules at its committed preparation point. The final R195 contract-cost
inventory refreshes this graph to include newly added R195 consumers. Historical
per-target costs are estimates from retained R194/R195 sampled checks, not OS
high-water marks. Unmeasured modules have UNKNOWN cost and need conservative
heavy-lock treatment; no fabricated estimate may authorize unsafe concurrency.
The inventory is NOT a runnable all-positive fixture suite: legacy R11 targets
are forbidden; deliberate negative fixtures require their own authenticated
symbol/diagnostic; unclassified fixtures need preflight disposition. Run the
applicable inherited main-tree validation plan plus all changed/dependency
source modules in topological, seeded order; never claim unrun fixtures passed.

**Lane coordination:** parent must reserve the shared heavy rebuild window with
lane2 before R196 launch. Lane2 must not run heavy checks during that reserved
window; main must not enter, edit, build or kill processes in its worktree.
The shared lock still applies to every actual heavy launch; no assumed calendar
reservation replaces lock ownership. This document does not claim lane2 agreed
or that a rebuild window has been scheduled.
