# O6 revision 124: four-region view copy-probe STOP-AUDIT

## Coordinate

Shift #122 (overall #176) started from actual accepted HEAD
`01968a8012a684ce7d7e1220ae6a94c598aca43f`. The gate message's
`019db665` coordinate was not present at checkout; `01968a8` is the exact
committed #121 audit boundary and contains all six reviewer-ratified commits.
The tracked tree was clean except for the pre-existing untracked `paper/`.

Only the mandatory disposable exact-copy probe was opened. No retained view,
action origin, correspondence, occurrence fold, result, bundle field, frozen
declaration, or hole was modified.

## Proposed view

The disposable exact CP5 copy appended a private four-constructor view indexed
directly by the original target `LocatedActionOccurrence`:

- prefix region owned a local prefix `LocatedActionOccurrence`, exact target tag
  equality, and exact target/local ordinal equality;
- moved-right owned exact action, tag, and `transitionCount prefixTrace`
  ordinal equations;
- moved-left owned exact action, tag, and successor ordinal equations;
- suffix owned a local replayed-suffix occurrence, exact tag equality, and the
  exact two-head-plus-prefix ordinal equation.

The recursive producer inspected the dependent prefix stored inside the target
occurrence. A one-elimination consumer projected a target ordinal witness from
all four constructors. It never called `actionOccurrenceOccurs`, never called
`R97AppendOccurrenceView`, and never supplied a foreign `OccursIn` proof.

## Three-attempt copy-probe record

### Attempt 1 — infrastructure nonlinear endpoint patterns

The first exact-copy check rejected the empty-prefix clauses because their
left-hand sides repeated dependent endpoints (`pairFirst pairFirst`) and also
bound the occurrence's action-before state independently. Idris requested the
same pattern variable after unification. No semantic view field was reached.

### Attempt 2 — remaining empty-prefix endpoint unification

The explicit duplicate names were replaced by distinct endpoint names and the
occurrence states/transitions by wildcards. Patterning `NoTransitions` in the
same left-hand side still forced `initial = pairFirst`, and Idris again rejected
the independently named endpoints as nonlinear.

### Attempt 3 — joint identity failure in recursive prefix lift

A producer-owned `ProbePrefixShape prefixTrace` removed every
`NoTransitions`/endpoint pattern from the main function boundary. Empty-prefix
classification and all four constructors elaborated. Recursion reached the
prefix-region lift, then stopped at:

```text
Mismatch between: prefixHead and _
```

The `ProbeNonemptyPrefix prefixHead prefixTail` branch owned the source prefix
head, while the separately eliminated target occurrence decomposition retained
an anonymous first transition. Although the whole traces are propositionally
the same, the two dependent transitions were not definitionally the same when
constructing the lifted prefix occurrence.

This is a semantic stored-vs-reconstructed identity failure, not remaining
module plumbing. The copy-probe's three-attempt infrastructure budget is also
exhausted. Per the binding ruling, the complete disposable copy, source, and
TTC/TTM were removed, no pass marker was emitted, and no retained implementation
was attempted.

## Required design-only boundary

A future campaign must use one **joint prefix/target-occurrence shape producer**
rather than independently eliminating `PrefixShape prefixTrace` and the target
occurrence. Its nonempty-prefix constructor must own, under the same dependent
elimination:

- the exact prefix head and tail;
- the exact first target-trace transition identity;
- the exact tail-global `LocatedActionOccurrence`;
- and the equation relating the original occurrence to the one-step lifted tail
  occurrence.

The four-region recursion may then lift its prefix constructor using that owned
head identity. Merely adding transition equality after the two independent
eliminations would repeat the detached-proof error. No frozen surface or replay
bundle lemma is implicated.

## Status

- actual start/safe HEAD: **01968a8**;
- four-region exact-copy probe: **failed after 3; removed**;
- four-region retained view: **unopened**;
- action origin/correspondence/fold/result/body: **unopened**;
- body external-order and all #121 capital: **unchanged and frozen**;
- holes: **20**, split **6/4/8/1/1**.

```text
NO_FROZEN_SURFACE_CHANGE_REQUIRED
R124_FOUR_REGION_COPY_PROBE=failed_after_3
R124_DISPOSABLE_FOUR_REGION_PROBE_REMOVED=passed
```
