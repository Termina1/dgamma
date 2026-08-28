# O6 revision 57: indexed joint and spine closed; suffix RAR cons stop

## Scope

Shift #65 (overall #119) resumed at accepted revision-56 HEAD `27c6e55` and
implemented the selected action-specialized indexed GADT representation. The
new representation closed the dependent eliminator on its first attempt and
then instantiated the retained structural suffix recursion on its first
attempt. Work stopped at the next resisting lemma after the fresh three-attempt
budget for whole-suffix relational-replay concatenation was exhausted.

All uncommitted concatenation helpers were reverted. The indexed GADT,
dependent eliminator, exhaustive action producer, and concrete suffix spine
remain committed. No whole-target bundle or final adjacent result was opened;
`adjacentSwapSuffixSpike` and its hole are unchanged.

## Indexed GADT — `42a7651`

`PointwiseAlignedHeadJoint` now has exactly eight private constructors:

- `MkPointwiseInsertJoint`;
- `MkPointwiseRetireJoint`;
- `MkPointwiseRemoveJoint`;
- `MkPointwiseBeginJoint`;
- `MkPointwiseAdvanceJoint`;
- `MkPointwiseDivertJoint`;
- `MkPointwiseLeaveJoint`;
- `MkPointwiseUnloadJoint`.

Every constructor fixes its exact `Fired` action in the GADT result index and
carries the matching checked equation plus exact aligned singleton. The seven
fixed-tag constructors fix their rule tag in the index; L-Advance retains its
runtime tag. The eight retained builders were adapted directly to these
constructors. Fixed-tag extraction stays inside the builders and continues to
use `pointwiseBeginTag`, `pointwiseDivertTag`, `pointwiseLeaveTag`, and
`pointwiseUnloadTag`.

The declaration and builders are mutually type-dependent: replacing the old
single constructor invalidated every builder result at once, so they landed as
one dependency-atomic commit rather than an intermediate non-building commit.
Containing module and R16 passed on attempt 1.

## Dependent elimination — `f55e284`

`replayPointwiseJointHead` has one explicit joint scrutinee, an implicit exact
source-step index, and the exact dependent codomain
`PointwiseRelationalHeadReplay ... sourceStep replayedBefore`. Its eight clauses
match the eight GADT constructors and delegate directly to the already-closed
semantic heads.

The declaration compiled and passed coverage on attempt 1. This confirms the
revision-56 diagnosis: constructor specialization in the GADT index gives Idris
the source-action refinement that the old generic constructor could not
provide. No existential fallback, UIP, dictionary equality, or transport
package was required.

## Spine instantiation — `52ffa3f`

`buildPointwiseJointAction` exhaustively dispatches the source action to its
producer-owned specialized builder. It compiled on attempt 1.

The private `PointwiseRelationalHeadReplayer` was narrowed from a redundant
source-transition plus aligned-singleton boundary to the exact action, tag, and
checked equation already exposed by the structural `AlignedStep`. This removes
the old independently scrutinized dictionary-bearing source transition while
retaining checked ownership.

`replayPointwiseActionHead` composes `buildPointwiseJointAction` with
`replayPointwiseJointHead`. `replayPointwiseSuffixSpine` then instantiates
`replayPointwiseSuffixSpineWith` with that closed replayer. Its existential
target trace, final endpoint, and `SealedSuffixReplaySpine` compile on attempt 1.
Containing module and R16 passed.

Thus generic recursion is now genuinely instantiated for all eight action
families.

## Whole-suffix RAR concatenation: three-attempt stop

The next lemma attempted to concatenate each sealed singleton
`RelationalReplayCorrespondence` with the recursive tail correspondence. This
requires mapping every target `TraceEffectGenerator` and `IteratorStage` by
whether its `OccursIn` proof is `OccursHere` or `OccursLater`, while retaining
map and exact iterator-outcome capital.

### Attempt 1

The first structural implementation added:

- singleton-occurrence widening and tail-occurrence prepending;
- corresponding generator and iterator-stage lifts;
- head/tail generator and stage origin dispatch;
- map and exact outcome dispatch;
- `consRelationalReplayCorrespondence`.

Idris first localized missing explicit selected-transition endpoint indices in
the occurrence helpers and the ambiguity between the `Unified` and
`Metatheory` `OccursLater` constructors. After those syntactic errors, every
`OccursHere` clause also reported that the named `targetHead` unifies with the
exact `Fired ...` stored by the occurrence:

```text
Pattern variable targetHead unifies with:
  Fired ?nameEq ?keyEq ?action ?tag ?equation.
Suggestion: Use the same name for both pattern variables, since they unify.
```

### Attempt 2

The occurrence helpers received explicit endpoints and qualified constructors.
Each `OccursHere` clause then patterns the exact `Fired` target head. This
cleared the occurrence/index errors and exposed the first semantic transport
wall in the generator-map field:

```text
Mismatch between: sourceMiddle and sourceFinal.
```

The head RAR proves maps for its singleton source origin. The whole source
origin is `widenSingletonGenerator sourceTail (replayGeneratorOrigin ...)`.
Because `replayGeneratorOrigin` is an opaque record projection, reducing the
widening function cannot inspect it, so the singleton and widened executable map
expressions are not definitionally identical at the whole-trace endpoint.
Separate harmless actor-name alias errors also remained in iterator clauses.

### Attempt 3

Explicit proofs that singleton widening and tail prepending preserve each
executable generator map were added, together with relational map transports.
This moved the map clause from endpoint mismatch to a correlated-projection
identity wall:

```text
Can't solve constraint between:
  headRAR .replayGeneratorOrigin actor target
and:
  source.
```

The local `source` is exactly that projection, but the related-map field
reprojects it independently. Idris does not identify the two dependent
existentials after the widening index changes. The iterator field exposed the
analogous singleton/whole mismatch:

```text
Mismatch between: targetTail and NoTransitions.
```

Calling `replayIteratorOutcomePreserved headRAR` with the whole-stage value
cannot make that stage definitionally equal to the separately reconstructed
singleton stage expected by the head RAR.

The remaining actor-alias diagnostic was syntactic, but the generator and stage
errors both require preserving an origin and its proof as one dependent value;
they are not solved by actor renaming or proof irrelevance. The three-attempt
budget was exhausted. All concatenation code was reverted.

## Required next representation

The direct analogue of the successful L-Advance agreement/seal architecture is
a private producer-owned append package:

1. `LocatedConsReplayGeneratorOrigin` packages the lifted whole-source generator
   together with the map relation obtained from the *same* singleton/tail origin
   elimination;
2. `LocatedConsIteratorStageOrigin` packages the lifted whole-source stage
   together with its exact iterator-outcome equation;
3. `consRelationalReplayCorrespondence` projects both fields from those packages
   rather than independently recomputing `replayGeneratorOrigin` or
   `replayIteratorStageOrigin`.

This is private proof capital derived from the sealed head and tail RARs. It does
not widen caller inputs, identify dictionaries, or detach maps/outcomes from
their producer. Because this is a new dependent-package representation after a
bounded failure, it requires the normal design gate before implementation.

## Status

- indexed joint GADT: **8/8 constructors closed**;
- specialized builders: **8/8 adapted and closed**;
- dependent eliminator: **closed on attempt 1**;
- exhaustive action producer: **closed on attempt 1**;
- generic suffix spine: **instantiated and closed on attempt 1**;
- whole-suffix RAR: **blocked at producer-correlated cons packaging; reverted**;
- whole-suffix occurrence/ordinal composition: **unopened**;
- whole target `ReplayInvariantBundle`: **unopened**;
- final `AdjacentSwapResult`: **unopened**;
- holes: **20**, split **6/4/8/1/1**;
- estimate: original **3–15 shifts** band is held pending the RAR-cons design
  gate; the lower-bound work advanced substantially, but the new dependent
  append package replaces the anticipated direct fold.
