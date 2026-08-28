# O6 revision 47: generator RAR closed; advance dispatcher STOP-AUDIT

## Scope

Shift #55 began at accepted revision-46 HEAD `cb05a84` and remained inside the
private O6 pointwise L-Advance replayer. Frozen signatures, production files,
public caller boundaries, and the sole local-diamond hole were unchanged.

## Retained closure

### Dependent generator locator

Commit `45d7f4d` closes the ratified R46 route:

- `SingletonAdvanceStageReplayFamily` owns the already-proved located stage
  package for every target stage;
- `LocatedSingletonAdvanceGeneratorReplay` packages a source generator and its
  universally quantified relational map proof together;
- `locateSingletonAdvanceGeneratorReplay` handles actual-forward,
  iterator-forward, and iterator-yielded generators.

The actual-forward branch uses the corrected dependent binder. Both iterator
branches give source stages and generators complete singleton trace types. Each
then declares a fully typed local `PartialMapsRelated` function and constructs
it directly with `replayPartialRewrite`, the branch's exact generator-map
equation, and `replayTraceGeneratorMapRespects`. The inference-sensitive
`replayExactMapsGivePartialMapsRelated` helper is not used. This compiled on the
first fresh-budget attempt, so the generator-RAR design escalation boundary was
not triggered.

### Singleton L-Advance RAR

Commit `774fd3f` adds `singletonAdvanceRAR`. It defines one shared dependent
generator locator and projects both generator origin and relational map proof
from that same located package. Stage origin and exact same-input outcomes come
from the same `SingletonAdvanceStageReplayFamily`. The complete
`RelationalReplayCorrespondence` compiled on its first attempt.

### Common head packager

Commit `0e2e90a` adds `packagePointwiseAdvanceHead`. Given one checked
`PointwiseAdvanceOperationalReplay` and the concrete related reloading owners,
it constructs:

- the exact source and replay singleton transitions;
- the singleton stage family;
- `singletonAdvanceRAR`;
- source alignment;
- the sealed pointwise head, including occurrences, relative ordinal, maps, and
  endpoint through `packagePointwiseRelationalHeadReplay`.

This compiled on its first attempt. No caller-provided target provenance was
introduced.

## Runtime dispatcher three-attempt diagnostic

A private `eliminateSealedPointwiseAdvanceHead` was then attempted. Its GADT
pattern opened the source reloading owner and related target owner in one scope,
used `pointwiseRelatedLifecycleMaps`, consumed
`runtimeAdvanceOutcomeRelated`, and exhaustively dispatched empty, undefined,
failure, yielded-divert, yielded-finish, and yielded-iteration outcomes into the
already-retained operational producers.

1. The initial elaboration reached the successful-yield dispatcher but rejected
   a nested local `where` under a `with` clause:

   ```text
   Wrong number of 'with' arguments: expected 1 but got 0.
   ... 0 dispatchYield :
   ```

2. The yield cases were inlined under `case matches` and `case rest`. The next
   elaboration reached the common `finish` callback, where its implicit local
   component had not been named in the defining clause:

   ```text
   Mismatch between: component (implicitly bound ...) and component.
   ... sourceFound replayedFound operational
   ```

3. `finish {component}` fixed that scope. Elaboration advanced to the empty
   operational branch and exposed the same omitted implicit pattern in the
   enclosing `dispatchRemaining` clause:

   ```text
   Mismatch between: component (implicitly bound ...) and component.
   ... sourceFound
   ```

The dispatcher's fresh budget was exhausted. The whole uncommitted eliminator
was reverted. The three retained producer/RAR/package commits remain complete;
no incomplete head, branch, or metavariable remains.

## Next route

On a fresh dispatcher budget, restore the same exhaustive eliminator and name
its local dependent component in **both** `dispatchRemaining {component}`
defining clauses before compiling. Keep `finish {component}`. This is the same
concrete-index discipline that closed the common packager and every yielded
operational producer; no caller widening or new sealed interface is indicated.

After the eliminator compiles, `replayPointwiseAdvanceHead` should only need to:

1. project the source raw action from `sourceChecked`;
2. call `sealPointwiseAdvanceSource`;
3. locate the related replay owner pointwise;
4. delegate to the eliminator.

## Status

- dependent generator package: **proved and retained**;
- singleton L-Advance RAR: **proved and retained**;
- common checked head packager: **proved and retained**;
- exhaustive runtime dispatcher: **STOP-AUDIT; fully reverted**;
- semantic families: **7/8** until the outer complete head is retained;
- whole-suffix composition: **unopened and gated**;
- adjacent result: **unopened**;
- holes: **20**, split **6/4/8/1/1**;
- O6 estimate: **7–19 shifts**, narrowed from **9–21** after closing generator
  provenance, singleton RAR, and the common head-capital package.
