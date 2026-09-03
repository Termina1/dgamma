# O6 revision 132: Canonical producer-scan copy-probe stop audit

## Authorized continuation

The R131 stop gate at `06db94dbb720fc9cfbed2264c7c0c513a8c5c3a6` was
accepted.  The supervisor ratified all nine retained O12 preparation helpers and
ruled that the executable ordinal scan failure was mechanical: nested `with`
made the existential transition middle inaccessible.  A fresh three-attempt
scan unit was authorized in the same shift under three binding changes:

1. no `with` block anywhere in the scan;
2. invert the scan into a producer-owned research record/data family whose
   public fields carry the existential middle and its exact transition proofs;
3. retain the complete explicit type/state telescope and avoid reserved names.

O12's actual hole-fill budget remained separate and untouched.

## Producer design

The discarded candidate followed the ruling literally:

- `CanonicalTraceHead` carried `traceHeadMiddle`, the head transition, and the
  indexed rest as public producer-owned fields;
- `CanonicalFirstLifecycleOccurrence` carried both existential occurrence
  states, both stored equality dictionaries, the action/tag/checked equation,
  exact earlier/later traces, `NoLifecycleBy` for the earlier trace, owner and
  lifecycle proofs, and exact decomposition;
- `CanonicalFirstLifecycleScan` returned either structural absence or the exact
  first occurrence;
- a prepend producer lifted either recursive result through one excluded head;
- owner and lifecycle decisions were each isolated in a dedicated top-level
  single-elimination helper; and
- the recursive scan and head-record consumer formed one mutual total block.

The entire scan region contained zero `with (` syntax.  It used no reserved
identifier or local `let` alias and declared `name/key/world/error/value`, all
three relevant endpoint states, equality dictionaries, action/tag/equation,
and trace inputs explicitly.

## Fresh scan-unit attempts

The fresh unit exhausted its binding three attempts:

| Attempt | Result |
|---:|---|
| 1 | Pre-Idris infrastructure failure.  A static zero-`with` guard naively matched the English word “with” in a doc comment; no elaborator process ran. |
| 2 | First elaboration.  The data constructors and consumers needed explicit hidden initial/final indices.  The head consumer's result also referred to bare projection names instead of projections from an explicit record argument. |
| 3 | After explicitly naming every result index and record argument, elaboration reached two bounded defects: the non-lifecycle prepend callback omitted its required actor-equality argument, and runtime scan code called helpers mistakenly declared at quantity 0, reported as “not accessible in this context”. |

The decisive attempt-3 diagnostics were:

```text
Mismatch between: Void and
  transitionActor (Fired storedNameDecision storedKeyDecision action tag checked)
    = selected -> Void.

produceCanonicalTraceHead is not accessible in this context.
canonicalScanOwnerDecision is not accessible in this context.
```

These are mechanical arity/quantity defects, not a semantic refutation.
Nevertheless the three-attempt budget is binding, so no fourth correction was
made.

## Mandatory disposable exact copy-probe

Per the continuation ruling, budget exhaustion triggered a disposable minimal
copy-probe before gating.  Temporary module
`DGamma.R132CanonicalScanProducerCopyProbe` retained exactly the proposed
producer shape while removing owner/lifecycle classification entirely:

- one public `ProbeTraceHead` record with explicit middle, transition, and rest;
- one runtime `produceProbeTraceHead` constructor helper;
- one zero-`with` mutual structural scan; and
- one consumer which projected the producer-owned middle and recursed on the
  exact rest.

The fresh one-module check stopped at the producer call made after matching the
nonempty trace:

```text
1/1: Building DGamma.R132CanonicalScanProducerCopyProbe
Error: While processing right hand side of probeScan.
{middle:75267} is not accessible in this context.

probeScanFromHead initial finalState
  (produceProbeTraceHead transition rest)
```

Thus making a record whose field stores the middle is not by itself sufficient
when that record is constructed *after* `MoreTransitions` has already hidden
its existential middle in the caller pattern.  The next design must make the
trace-view producer itself the first elimination (for example, a public view
indexed by the untouched whole trace), so no caller first exposes and then tries
to repack the existential.  This remains an elaboration/scoping wall, not a
proof-theoretic or semantic wall.

The temporary probe source and both possible TTC/TTM paths were removed.  The
complete uncommitted producer candidate was restored byte-for-byte to the R131
committed boundary.  No fourth scan attempt, restatement, O12 fill attempt,
other CanonicalSort hole, or DeletionChain pivot followed.

## Status and disposition

The R131 helper capital remains ratified and unchanged.  This R132 continuation
adds no retained proof source.  The research-hole census remains **19**, split
**6/4/8/0/1** (CanonicalSort/CrossTrace/DeletionChain/LocalDiamond/
RenamingComposition).  `closingFreeTraceShapeSpike_rhs` used **0/3** fill
attempts; the R132 producer-scan unit used **3/3** attempts; the mandated copy-
probe used one fresh check and was fully removed.

`THM73-PLAN.md`, production `src/`, `dgamma.ipkg`, CP3, the frozen adjacent-swap
surface, the R129 deferred integration, and the two permitted untracked paths
were not modified.  The terminal gate revalidates the committed CanonicalSort
module, seeded 207/207 production closure, exact hashes, hole split, and a safe
unstaged boundary.
