# O6 revision 39 — L-Advance map-demand analysis

Status: **pre-shape analysis only**.  This document was written before selecting
or pre-declaring a replacement for the frozen exact-map fields.  It changes no
Idris declaration.

## 1. Why L-Advance must be scoped with L-Unload

The revision-38 failure is not confined to the Table-1 `LUnload` map.  A replayed
`LAdvance` singleton contributes all three kinds of Definition-54 generator:

1. `ActualForwardGenerator`, whose map is the checked transition's
   `partialEffectMap`;
2. `IteratorForwardGenerator`, whose map projects the successful forward state
   from `iteratorStageEffect`; and
3. `IteratorYieldedGenerator`, whose map is the inverse returned by the iterator
   at the generator's stored origin.

The first kind reaches the same accumulator boundary as `LUnload` in the
`LIter`/`LFinish` Table-1 branches.  Related source and target fibers retain
`AccumulatorRelated`, not equality of proof-bearing accumulator functions.
The second and third kinds expose the callback's proof-bearing output context
and yielded inverse.  Therefore an exact-equality repair for L-Unload followed
by an independent L-Advance campaign would oscillate over the same semantic
boundary.

## 2. Existing relational capital at the boundary

The production definitions already provide the right quotient, without proof
irrelevance or function extensionality:

- `partialEffectMapForRespects` / `partialEffectMapRespects` show each Table-1
  map respects `EffectStateRelated` on related inputs;
- `relatedLifecyclePartialMapOutputsAtStates` relates source and target
  lifecycle maps on the same input from `FiberControlRelated`;
- `relatedAccumulatorOutputs` relates proof-distinct accumulator maps on the
  same input from `AccumulatorRelated`;
- `runtimeAdvanceOutcomeRelated` compares the actual iterator invocation from
  related fibers/effects and returns `RuntimeIteratorOutcomeAgreement`;
- `RuntimeYieldsAgree` retains both the yielded forward states under
  `EffectStateRelated` and yielded inverse maps under `PartialMapsEquivalent`;
- `iteratorStageOutcomeRelated` and
  `iteratorOutcomeAgreementTransitive` are the existing Equation-55 quotient
  consumed by `TraceIndependent.iteratorYieldsStable`.

No one of those lemmas yields equality of the proof-bearing output
`EffectState`, accumulator, or inverse function, and none should be strengthened
to do so.

## 3. Evidence demanded by each generator case

### 3.1 Actual forward

For related input states, source and replayed Table-1 outputs must have matching
undefinedness and related defined outputs.  Same-input
`relatedLifecyclePartialMapOutputsAtStates`, combined with one side's
`partialEffectMapRespects`, is sufficient.  Exact output equality is not.

### 3.2 Iterator forward

The target stage must be mapped to the exact corresponding source stage.  At
related inputs, `RuntimeIteratorOutcomeAgreement` supplies matching
undefined/failure/success shape and, in the successful case, related yielded
forward states.  Projecting the successful states gives the relational partial
map fact needed by the generator field.

A bare `IteratorOutcomeAgreement` is **too weak for this case**: its successful
constructor intentionally omits the yielded forward state and retains only the
continuation and inverse-map relation.  Any proposed RAR stage field must either
retain `RuntimeIteratorOutcomeAgreement` or prove the forward-generator
relation directly at the producer.

### 3.3 Iterator yielded inverse

For the target `IteratorYieldedGenerator stage origin`, replay construction must
choose the corresponding source stage and a source origin related to the target
origin.  `RuntimeYieldsAgree` exposes `PartialMapsEquivalent`; its forward half
is exactly the relation required between the source and target yielded inverse
maps on related arguments.  Demanding equality here would repeat the R38 bug
for callback-returned proof-bearing tables.

## 4. Equation-55 / independence interaction

Relational foreign transformation outputs need not be the same state.  The
transport proof must:

1. obtain related source/target moved states from the relational transformation
   map;
2. apply source `iteratorYieldsStable` at the source moved state;
3. use `iteratorStageOutcomeRelated` across the related moved states and across
   the related original states; and
4. compose the resulting `IteratorOutcomeAgreement` values.

Consequently a same-input-only `PartialRelated` field is producer-friendly but
not by itself consumer-sufficient for transformation composition and
`replayIndependent`.  The final shape must quantify over **related source and
target inputs** (or carry equivalent map-respect capital), and the probes must
check this before a manifest delta is proposed.

## 5. Constraints on the eventual shape

The revision-39 probe candidate must satisfy all of the following before a
frozen declaration is touched:

- producer-suppliable for proof-distinct L-Unload accumulators;
- producer-suppliable for L-Advance actual, forward, and yielded generators;
- closed under identity and transformation composition;
- closed under replay-correspondence composition;
- sufficient to transport `PartialCommute` and all of `TraceIndependent`;
- sufficient to recover existential target map totality used by the R27/R29
  fixture, without recovering false exact identity;
- implied by every currently retained exact producer proof;
- compatible with self-contained retired exact shapes for existing negatives.

This analysis deliberately stops short of naming the proposed replacement.
The candidate is selected only after consumer and producer probes elaborate.
