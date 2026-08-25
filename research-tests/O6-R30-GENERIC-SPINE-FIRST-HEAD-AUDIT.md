# O6 revision 30: first generic sealed-spine recursion audit

## Scope

This audit records the first body-work checkpoint after
`review-cp5-r19-scoped.md` returned ACCEPT-WITH-CHANGES and the stale plan
inventory was corrected at `fbb1bee`.

The public type of `adjacentSwapSuffixSpike` is unchanged. No caller premise,
result field, constructor visibility, production module, or manifest exception
was added. The implementation work is private to
`CP5ConfluenceLocalDiamondSpike` and is intended to discharge the existing
body hole.

## Constructive checkpoint

The containing module and `R16ConfluenceTheoremAssemblyPositive` elaborate with:

1. `PointwiseRelationalHeadReplay`, a private producer-owned envelope indexed by
   the exact source transition and replay start. It owns the checked target
   transition, action/tag equality, singleton alignment, RAR, exact map
   equality, endpoint, occurrence correspondence, and relative ordinal.
2. `sealPointwiseRelationalHead`, which is definition-only and feeds those owned
   fields directly to the private `SealedSuffixReplayStep` constructor.
3. `PointwiseSuffixSpineReplay` and `replayPointwiseSuffixSpineWith`, the first
   genuine generic recursion over exact `AlignedTransitions`. The empty case
   produces `SealedSuffixReplayEnd`; the step case evaluates one private head,
   derives the source target's well-formedness from its checked transition,
   threads the produced endpoint, recurses on the exact tails, and seals the
   node.
4. Generic singleton action/child-registration occurrence reconstruction,
   generation identity, tag preservation, and relative ordinal construction.
   These are derived at the same packaging point as the checked replay and are
   not independent inputs.
5. `singletonNonAdvanceRAR`, which constructs generator/stage correspondence
   for any non-`LAdvance` singleton from the exact producer-owned head-map
   equality. Iterator stages are constructively impossible in such a singleton.
6. `replayPointwiseRetireHead`, the first fully general semantic head branch.
   It reconstructs target `O-Retire` applicability from `ControlEquivalent`,
   derives the checked target, exact endpoint effects/controls/well-formedness,
   identity head map, singleton RAR, occurrence and ordinal capital, and then
   packages the frozen head envelope.

The retire branch is generic in `name`, `key`, `value`, `world`, and `error`; it
is not the concrete R19 actor-0 fixture.

## First-recursion finding

The recursion shape itself is constructible without changing the frozen
boundary. The remaining semantic parameter is a total pointwise action
replayer. The older production `replayRelatedAction` consumes
`OrderedRegistryControlsRelated`, while revision 17 intentionally retains only
`ControlEquivalent`; independently stored ordered target lists cannot be
restored in general. R23 already pins that exact mismatch.

This is not presently a stop-audit finding. Pointwise controls plus effect
relatedness and well-formedness plausibly determine the operational behavior,
and the fully generic retire branch demonstrates one cross-state constructor.
However, the other seven `Action` constructors still require constructive
pointwise branches. `LAdvance` is the largest: unlike the generic non-advance
RAR, it must transport every reachable iterator stage and yielded inverse, not
only the actual head map.

After the total head dispatcher, whole-suffix RAR, whole occurrence/ordinal
fold, external-order framing, and whole target `ReplayInvariantBundle` assembly
remain. R29 proves the bundle field order for a two-finish fixture but does not
supply those generic recursions.

## Estimate and stop rule

At this first generic recursion the remaining O6 band is re-estimated from
**20–35** to **22–38 shifts**:

- pointwise semantic heads for the seven remaining actions, including iterator
  provenance: 9–15;
- whole suffix RAR and occurrence/ordinal composition: 5–8;
- target invariant bundle and adjacent envelope assembly: 5–9;
- adversarial probes, full validation, and scoped review: 3–6.

Any future branch that requires ordered controls, a caller-selected target map,
an endpoint, occurrence/ordinal evidence, quietness, no-failure, independence,
or a target bundle must stop-audit rather than widen the theorem boundary.

## Hole forecast

This checkpoint does not claim body closure. The research tree remains at 20
holes with split `6/4/8/1/1`; `adjacentSwapSuffixSpike` remains the sole
LocalDiamond hole. Successful full adjacent-result assembly will reduce the
total to 19 and O6 from two obligations to one.
