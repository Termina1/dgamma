# O6 revision 86: field-8 indexed transport and moved-boundary backward stop

## Scope

Grind shift #94 (overall #148) resumed at accepted revision 85
`ce19b2d`. It opened only field 8 (`TraceComponentsTotal`). Ten checked,
lemma-sized units were retained. A combined backward paper-step unit exhausted
its own fresh three-attempt budget on erased-local annotation mechanics and was
removed. Fields 9–15 and final assembly were not opened.

## Retained capital

### Correlated fiber and one-transition transport

- `fiberControlActiveSame` (`ee74370`) passed on attempt 1. It eliminates exactly
  one `FibersControlRelated` and delegates directly to
  `pointwiseLifecycleActiveSame`.
- `pointwiseTransitionComponentTotal` (`777d753`) passed on attempt 1. It uses
  symmetric pointwise lookup, exact action-owner reindexing, the correlated
  activity projection, frozen table/effect transport, and no reopened relation
  elimination.

This closes the stop diagnosed by revision 85.

### Suffix and source decomposition

- `replayPointwiseSuffixTraceComponentsTotal` (`0b55a89`) passed on attempt 1.
  Its structural recursion consumes each sealed `sameAction` and `headEndpoint`
  before rebuilding `TraceComponentsTotalStep`.
- `adjacentSourceTraceComponentsTotalSplit` (`f643256`) passed on attempt 1. It
  reindexes the source bundle through the exact adjacent decomposition and uses
  `totalAppendSplit` to retain prefix, left boundary, right boundary, and suffix
  totality.
- `appendTraceComponentsTotal` (`6f2d24c`) passed on attempt 1 and is the inverse
  structural composition needed to rebuild target pieces.

`DGamma.CP4DeletionPremiseSplit` is imported by the research spike solely for
its already checked `totalAppendSplit`; production files are unchanged.

### Active-state transport and the moved-left boundary

- `transitionComponentTotalFromActiveFibers` (`03e69a8`) passed on attempt 1.
- `pointwiseActiveFibersProvideAll` (`a2afa87`) passed on attempt 1, lifting the
  frozen per-fiber table transport through one `RelationalReplayEndpoint`.
- `adjacentMovedLeftComponentTotal` (`9345f17`) passed on attempt 2. It composes
  source prefix/pair totality, derives all active provisions at `pairFinal` from
  the authenticated empty initial state, transports them through the exact
  diamond endpoint to `swappedFinal`, and discharges `movedLeft`. Attempt 1 only
  discovered that production's otherwise suitable
  `emptyActiveFibersProvideAll` is private; the retained proof inlines the same
  constructive empty-lookup contradiction.

### Backward paper-step foundations

- `foreignActiveFiberProvidesBackward` (`b1d0722`) passed on attempt 1. A
  different actor's active fiber is recovered exactly with
  `checkedActionProjects`, `applyActionLocalUpdate`, and
  `systemLocalUpdateForeign`.
- `retireOwnerActiveProvidesBackward` (`89b04cb`) passed on attempt 3. It opens
  one `retireSuccessView`, correlates the observed source fiber with the caller's
  exact fiber, and transports the provision predicate across `retireFiber`,
  whose component, table, and lifecycle are unchanged. Attempts 1–2 were
  dependent correlation/normalization layout refinements; no semantic premise
  was added.

## Removed unit and exact diagnostics

The removed `paperStepActiveFibersBackward` attempted to combine activation and
orchestration owner cases in one declaration. Its intended theorem was:

1. foreign owner: delegate to `foreignActiveFiberProvidesBackward`;
2. activation owner: contradict checked activation's already proved
   `activationSourceOwnerNotActive` with the supplied active fiber;
3. insertion owner: contradict frozen
   `checkedInsertRequiresAbsentExplicit` with the supplied lookup;
4. retirement owner: delegate to `retireOwnerActiveProvidesBackward`;
5. removal owner: open `removeSuccessView`, use
   `inactiveLifecycleFromRemovalGuard`, and contradict activity.

All three deaths were annotation mechanics, not a semantic wall:

1. `falseIsNotTrue` was discovered private; replacing it with a direct
   impossible equality advanced elaboration.
2. the insertion branch's erased `absent` local lacked an exact type, producing
   a generated `fromInteger` declaration error; an ordinary explicit
   lookup-equality type advanced elaboration.
3. the removal branch's erased `raw` local lacked an exact type and produced the
   same generated `fromInteger` declaration error.

Per the permanent protocol, the whole combined unit was removed at attempt 3.
No partial branch remains.

## Exact next decomposition

Do not retry the combined declaration. Use separate fresh budgets:

1. `paperActivationActiveFibersBackward`: foreign case plus the checked
   `activationSourceOwnerNotActive` contradiction.
2. `paperInsertActiveFibersBackward`: foreign case plus explicitly typed
   `checkedInsertRequiresAbsentExplicit` contradiction.
3. `paperRetireActiveFibersBackward`: foreign case plus frozen
   `retireOwnerActiveProvidesBackward`.
4. `paperRemoveActiveFibersBackward`: foreign case plus an explicitly typed
   raw `applyAction ... = Just ...`, `removeSuccessView`, and
   `inactiveLifecycleFromRemovalGuard`.
5. a one-clause/classifier dispatcher with no proof logic.

Then factor `adjacentSwappedFinalActiveFibersProvideAll` from the already checked
body of `adjacentMovedLeftComponentTotal`. Apply the dispatcher backward over
`movedLeft` (the revision-21 safety classifier provides its activation or
orchestration species), obtaining `ActiveFibersProvideAll` at `swappedMiddle`.
`transitionComponentTotalFromActiveFibers` then closes `movedRight` without an
intermediate detached endpoint. This is the exact producer-owned moved-pair
boundary transport.

Finally:

- combine prefix unchanged, moved-right, moved-left, and sealed suffix totality;
- populate private package field 8;
- only then open fields 9–15.

## Status

- fields 1–7: **closed and frozen**;
- field 8 one-transition, source split, suffix recursion, append composition,
  endpoint active transport, and moved-left boundary: **closed and retained**;
- field 8 moved-right boundary: **open at the split backward-classifier
  dispatcher**;
- field 8 package field: **not populated**;
- fields 9–15: **unopened**;
- final result/body: **unopened**;
- holes: **20**, split **6/4/8/1/1**.

The accepted remaining band is held at **1–10 shifts**. The body-closure review
boundary was not reached.

## Isolation

The frozen 1183-byte adjacent interface, revisions 19–21, fields 1–7, all prior
field-8 foundations, production `src/`, `dgamma.ipkg`, and CP3 remain unchanged.
No hole, postulate, escape hatch, detached caller premise, public surface, or
independently supplied target capital was introduced.
