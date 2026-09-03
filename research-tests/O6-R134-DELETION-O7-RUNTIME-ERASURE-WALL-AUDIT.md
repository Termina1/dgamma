# O6 revision 134: Deletion O7 runtime-erasure wall audit

## Authorized pivot

After R133 ratified O12, the next CanonicalSort dependency O14 was prepared by
a protocol-rank stable-sort helper unit.  That helper unit exhausted its strict
three-attempt budget and was restored/audited in
`O6-R134-CANONICAL-O14-RANK-SORT-HELPER-BUDGET-PIVOT-AUDIT.md`.  The R133 ruling
pre-authorized a motivated pivot to DeletionChain without an intermediate gate.
No CanonicalSort source remained dirty when DeletionChain was inspected.

## O7 interface wall

The first DeletionChain dependency is O7,
`closingEpisodeOccurrenceScanSpike`.  Its present research interface is
runtime-relevant (the function is not quantity 0) and returns a
`ClosingEpisodeScan` whose unrestricted list stores dependent
`ClosingEpisodeOccurrence` values.  Each occurrence stores a
`LocatedClosedEpisode`; that record in turn stores the episode's existential
intermediate system states and indexed transitions as runtime fields.

This is the same erased-index boundary canonized by the R133 ruling.
`MoreTransitions` hides its middle state at quantity 0.  A runtime producer
cannot recover that state and place it in an unrestricted occurrence record.
Unlike O12's new scan, O7's frozen research statement itself currently demands
the impossible runtime-relevant result.

## Mandatory probe-first evidence

Before spending any O7 fill attempt, disposable module
`DGamma.R134O7RuntimeMiddleProbe` isolated the exact interface shape:

- `RuntimeTraceView` had an unrestricted middle-state field, transition, and
  rest, indexed by the untouched input trace;
- `runtimeTraceView` matched a nonempty `Transitions` and attempted to construct
  that runtime result; and
- a parallel `ErasedTraceView`/quantity-0 covering definition recorded the
  canonized admissible shape.

The fresh one-module check failed exactly at the unrestricted constructor:

```text
1/1: Building DGamma.R134O7RuntimeMiddleProbe
Error: While processing right hand side of runtimeTraceView.
{middle:74780} is not accessible in this context.

RuntimeTraceMore _ transition rest
                 ^
```

The temporary source and both possible TTC/TTM outputs were removed.  This is a
correlation/erasure wall, not an algorithmic absence of a closing-episode scan:
a fully erased view can bind the same hidden state, as already established and
ratified for O12.  But filling O7 honestly requires changing the research
interface so the scan and every consumer are quantity 0 (or replacing the
runtime occurrence list by an erased indexed view).  Such a restatement was not
silently made at this gate.

## Attempt and source status

O7 used **0/3** fill attempts.  No DeletionChain source was edited, no later
DeletionChain obligation was opened out of dependency order, and no second
proof class is active.  The project remains at **18 holes**, split
**5/4/8/0/1**.  Production sources, package manifest, CP3, and the adjacent-swap
surface remain frozen.
