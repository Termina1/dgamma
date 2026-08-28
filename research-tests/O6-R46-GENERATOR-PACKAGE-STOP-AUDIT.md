# O6 revision 46: dependent generator package STOP-AUDIT

## Scope

Shift #54 began at accepted revision-45 HEAD `d989390` and retried only the
private singleton L-Advance generator package. No frozen signature, public
caller boundary, production file, runtime branch producer, or retained stage
package changed.

## Ratified R45 representation

The shift reintroduced the ratified dependent structure:

- `SingletonAdvanceStageReplayFamily` locates the already-retained
  `LocatedSingletonAdvanceStageReplay` for each target stage;
- `LocatedSingletonAdvanceGeneratorReplay` owns one exact source generator and
  a universally quantified relational map proof for that same generator;
- `locateSingletonAdvanceGeneratorReplay` handles actual-forward,
  iterator-forward, and iterator-yielded generators.

The actual-forward branch accepted the corrected R45 binder syntax:

```idris
\observedKeyEq, inputs => ...
```

Thus the revision-45 parser stop is closed. The attempt budget was spent in the
two iterator branches while forcing their locally named projections to stay
identical to the dependent record indices.

## Three-attempt diagnostic

1. The first compile reached the iterator-forward branch. An unannotated local
   `sourceGenerator` did not remain definitionally the explicit
   `IteratorForwardGenerator sourceStage` required by the projection theorem:

   ```text
   Mismatch between:
     IteratorForwardGenerator sourceStage
   and:
     sourceGenerator.
   ```

2. Both local source generators were given complete singleton trace types. The
   next compile showed that the unannotated local `sourceStage` similarly did
   not stay definitionally the record projection used by
   `locatedAdvanceOutcomeSame`:

   ```text
   Can't solve constraint between:
     located .locatedSourceAdvanceStage
   and:
     sourceStage.
   ```

3. Both local source stages were then given complete singleton trace types. The
   exact map equations elaborated, but the convenience call to
   `replayExactMapsGivePartialMapsRelated` inferred its target-respect argument
   as `EffectPartialMapRespects` before recognizing that
   `replayTraceGeneratorMapRespects` is the equivalent strong relational shape:

   ```text
   When unifying:
     relation ... -> PartialRelated ...
   and:
     EffectPartialMapRespects ?keyEq ?_
   Mismatch between:
     EffectStateRelated observedKeyEq ?x ?y
   and:
     EffectState ?name ?key ?value ?world.
   ```

The third attempt exhausted the fresh budget. The whole generator family,
dependent generator record, and locator were reverted. No partial RAR,
`replayPointwiseAdvanceHead`, or metavariable remains.

## Next representation

The next fresh-budget attempt should keep the same dependent generator package
but avoid the inference-sensitive convenience helper in the two iterator
branches. Give a named, fully typed local proof:

```idris
0 related : PartialMapsRelated (EffectStateEquivalence observedKeyEq)
  (traceGeneratorMap sourceGenerator)
  (traceGeneratorMap targetGenerator)
```

and define it directly, field-by-field, with `replayPartialRewrite`, the exact
map equation, and
`replayTraceGeneratorMapRespects observedKeyEq targetGenerator`. This fixes all
map domains before elaborating the proof body and retains the essential R45
rule: origin and map proof are projections of the same located package.

Only after that package compiles should the singleton RAR, the
`runtimeAdvanceOutcomeRelated` dispatcher, and `replayPointwiseAdvanceHead` be
opened.

## Status

- all L-Advance operational runtime branch producers: **closed individually**;
- singleton stage origin/outcome capital: **closed and retained**;
- dependent generator package: **STOP-AUDIT; fully reverted**;
- singleton RAR and complete L-Advance head: **open**;
- semantic families: **7/8**;
- whole-suffix composition: **unopened and gated**;
- adjacent result: **unopened**;
- holes: **20**, split **6/4/8/1/1**;
- O6 estimate: **9–21 shifts**, unchanged because this shift resolved the R45
  parser stop and localized the remaining failure to one inference-sensitive
  convenience call, but retained no new proof declaration.
