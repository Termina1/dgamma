# R144 CrossTrace serial budget-stop audit

## Scope and frozen boundary

R144 began at the exact clean production boundary `569446a` on
`cp5-thm73-scoping`.  The only pre-existing untracked paths were the permitted
`paper/` directory and `review-o6-body-adversarial.md`.  O17 was processed first
and audit-stopped separately.  This audit covers the required serial pivot over
all four CrossTrace holes.

No production module, CP3 definition, adjacent-swap record/constructor, or
existing theorem statement was changed.  The only checked code changes in this
phase are transparent helper lemmas in
`research/DGamma/CP5ConfluenceCrossTraceSpike.idr` plus the direct import of the
already-existing DeletionChain same-external algebra used by one helper.

## O19 local block transposition: probe-stop, body 0/3

`operationalAdjacentBlockSwapSpike` remains at **0/3 body attempts**.  The prior
R144 dependency probe established that the current `AdjacentActorSwapSafety`
surface does not visibly exclude a provider-finish / consumer-begin ordering,
while an early consumer `LBegin` evaluates to `Nothing` in the disposable
fixture.  Full checked countershape packaging stopped at well-formedness and
target-resolution equations, so the fixture was removed and no surface change
was requested.  See
`O6-R144-CROSSTRACE-O19-DEPENDENCY-PROBE-STOP-AUDIT.md`.

## Canonical support-order matching: body 3/3

Three independently checked and committed eliminators/assemblers were retained:

- `02c3baf` — `canonicalSupportOrderForwardFromTruth`;
- `cd1ee19` — `canonicalSupportOrderBackwardFromTruth`;
- `7d0fac1` — `canonicalSupportOrdersFromTruth`.

They reduce `MappedCanonicalSupportOrders` exactly to two pointwise semantic
facts:

1. left endpoint support is preserved by `renameForward`; and
2. right endpoint support is preserved by `renameBackward`.

Body attempts were then charged as follows.

1. Direct use of the checked assembler left exactly those two support-truth
   functions unapplied.
2. Reflexive proof forwarding was rejected at the distinct endpoint states
   (`rightFinal` versus `leftFinal`), confirming that order enumeration alone
   does not identify endpoint support.
3. An attempted inverse-renaming rewrite used a nonexistent generic inverse
   name; the budget is charged rather than silently repaired because even the
   correct `renameLeftInverse`/`renameRightInverse` can rewrite only actor names,
   not the distinct endpoint states.

The remaining obligation is a genuine endpoint-support preservation theorem
from `SameOrchestrationModuloGenerated` plus both independent canonical
capitals.  Current-generation correspondence handles mapped versus fully
vestigial generations, but support is a registry-wide fixed point depending on
component dependencies/provisions and parent edges.  No existing field directly
connects those endpoint support computations, and no circular appeal to O20 was
introduced.

`canonicalSupportOrdersMatchSpike` is restored to its original hole and is
**budget-stopped at 3/3**.

## Operational canonical permutation selection: body 3/3

The three body attempts established the exact split.

1. The zero-swap `ActorPermutationDone` construction was rejected because the
   mapped right support order is not definitionally the left support order.
2. Destructing `MappedCanonicalSupportOrders` exposes only mutual membership;
   it still gives no list equality and did not close the same target-order
   constraint.
3. A `decEq` split did not refine the hidden computed order inside
   `CertifiedOperationalCanonicalPermutation` under the inferred nondependent
   case motive; more importantly, the unequal branch still requires a finite
   adjacent-transposition selector and a safety-producing operational fold.

The nontrivial construction must combine a duplicate-free finite-list
permutation algorithm with per-step `AdjacentActorSwapSafety`, invoke
`operationalAdjacentBlockSwapSpike`, and thread the exact blocks and replay
bundle.  Mutual set membership is sufficient for a pure permutation but is not,
by itself, the missing operational safety theorem.

`selectOperationalCanonicalPermutationSpike` is restored and is
**budget-stopped at 3/3**.

## Canonical endpoint convergence: body 3/3

Four checked helper units were retained, each committed immediately after a
fresh terminal-module check:

- `fbd6287` — `operationalPermutationEndpoint`, composing every local endpoint
  quotient along the sealed operational fold;
- `198ce4e` — `operationalPermutationSameExternalInputs`, composing the exact
  external-input relation along the same fold;
- `6a67c5f` — `permutedCanonicalExecutionFromOperational`, assembling the full
  `PermutedCanonicalExecution` from O19 capital;
- `758daff` — `canonicalConvergenceFromBridge`, the final O20 constructor once
  its authenticated replay-to-right endpoint bridge is available.

Body attempts were then charged as follows.

1. Direct `MkCanonicalConvergenceResult` assembly accepted the new permuted
   execution and stopped exactly at `ReplayedCanonicalEndpointBridge`.
2. Direct use of `canonicalConvergenceFromBridge` exposed the identical single
   missing bridge.
3. Partial construction of `MkReplayedCanonicalEndpointBridge` fixed the exact
   endpoint bijection and exposed the four remaining semantic fields: ambient
   equality, renamed table equality, renamed control correspondence, and exact
   generated-birth matching.

Thus O19 now supplies all operational replay projections needed by O20; the
remaining gap is precisely the cross-trace endpoint comparison, not replay-fold
bookkeeping.  `canonicalSchedulesConvergeSpike` is restored and is
**budget-stopped at 3/3**.

## Validation and census

After every retained helper, only
`build/ttc/2025081600/DGamma/CP5ConfluenceCrossTraceSpike.ttc` and its `.ttm`
were removed, followed by the seeded check:

```sh
IDRIS2_PATH="$PWD/build/ttc/2025081600${IDRIS2_PATH:+:$IDRIS2_PATH}" \
  idris2 --source-dir research --check \
  research/DGamma/CP5ConfluenceCrossTraceSpike.idr
```

The final fresh CrossTrace check passes with only the pre-existing lowercase
implicit-binding warnings.  A final seeded `idris2 --build dgamma.ipkg` also
passes.  No `build/` tree was deleted.  The full hole census remains **13**, split **CanonicalSort 2 / CrossTrace 4 / DeletionChain 6 /
LocalDiamond 0 / RenamingComposition 1**.

## Safe gate

All four CrossTrace holes have now been visited serially for R144.  Resume only
with one of these producer results:

1. a checked exclusion theorem or complete countershape for the local O19
   adjacent block swap;
2. a pointwise endpoint-support preservation theorem for current mapped names;
3. a dependent finite permutation worklist that produces safety at every swap;
   or
4. the four-field authenticated replay-to-right endpoint bridge.

No later DeletionChain work is opened in this shift.
