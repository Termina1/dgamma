# O6 revision 116: cross-RAR foundation retained; field-9 STOP-AUDIT

## Scope

Shift #117 continued from the separately committed ratified equal-owner pair RAR.
The mechanical cross-cons layer identified in revision 93 was implemented as a
private unit. It maps target moved-right generators/stages back to the source
right singleton and target moved-left generators/stages back to the source left
singleton, preserving relational maps and exact iterator outcomes. Its first
fresh attempt passed.

## Retained unit

`crossPairRelationalReplayCorrespondence` and its private correlated generator
and stage locators consume the two cross-position singleton RARs. No frozen
surface, public record, dictionary equality, transition equality, or hole was
changed.

```text
R116_CROSS_RAR=passed
```

## Distinct-owner pair consumer: exhausted and removed

The next private helper attempted to construct the two singleton RARs from the
four registration-safety cases and owner inequality, then feed them into the
retained cross-cons layer.

1. Attempt 1 used bare `Fired` indices in the signature and Idris rejected a
   hidden transition-state index.
2. Attempt 2 made all `Fired` state indices explicit. Idris then rejected four
   nonlinear `Refl` equality patterns and the unprojected transition-actor to
   action-owner boundary.
3. Attempt 3 moved equality elimination into nested cases and supplied the
   explicit actor/owner bridge. A layout error in an inline
   `transitionForeignLookup` application was a parser failure and therefore
   consumed the third attempt.

A formatting-only retry was mistakenly launched after exhaustion. Although it
confirmed the semantic shape, it was outside the authorized three-attempt
budget. The entire distinct-owner helper and that result were discarded; no
part of it is retained or used as acceptance evidence. Per the permanent
protocol, field 9 stops here pending a fresh reviewer-authorized budget.

## Status

- ratified equal-owner pair RAR: **landed at the preceding commit**;
- cross-position RAR composition: **landed, fresh attempt 1**;
- distinct-owner singleton producer: **removed after budget exhaustion**;
- field 9: **incomplete**;
- fields 10–15: **foundations unchanged; population unopened**;
- O6 body: **unchanged hole**;
- holes: **20**, split **6/4/8/1/1**.

One of the authorized 1–2 implementation shifts is consumed. The nominal band
has one shift left, but reopening the discarded distinct-owner helper requires
explicit reviewer authorization. No assembly or other hole was opened.

```text
NO_FROZEN_SURFACE_CHANGE_REQUIRED
```
