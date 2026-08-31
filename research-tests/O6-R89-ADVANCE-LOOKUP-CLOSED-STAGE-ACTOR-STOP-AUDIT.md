# O6 revision 89: advance lookup transport closed; stage-actor stop

## Scope

Grind shift #97 (overall #151) resumed from accepted revision 88 `26298be` and
opened only the authorized three-unit singleton L-Advance stage-family split.
The first unit closed. The second unit exhausted its own fresh three-attempt
budget at a genuine dependent index boundary and was removed in full. The
family wrapper, singleton RARs, moved-pair RAR, whole RAR, bundle fields, and
assembly were not opened.

## Retained capital

`singletonAdvanceSourceFoundFromOwnerLookup` is retained at `04fda32` after one
visible fresh attempt. Its signature makes all dependent type parameters and
both lookup expressions explicit and parenthesizes every compound proposition.
Given exact owner lookup equality and exact moved-side presence, it proves exact
source-side presence by:

```text
trans lookupSame movedFound
```

No dictionary equality, fiber reconstruction, relation elimination, or output
capital is introduced.

## Removed unit

The removed `locateSingletonAdvanceStageFromOwnerLookup` had the authorized
shape:

1. consume one moved singleton `IteratorStage`;
2. eliminate `StageFromAdvance`;
3. reduce its occurrence to the singleton transition;
4. expose the exact `MkFiber ... (Reloading remaining accumulator view)` cell;
5. invoke the retained lookup transport;
6. delegate to frozen `locateSingletonAdvanceStageReplay`.

The three fresh deaths were:

1. nonlinear constructor pattern mismatch: the explicit `selected` stage index
   and `StageFromAdvance` actor must use the same pattern name;
2. after fixing that pattern, reconstructing the exact target stage at the
   delegation point failed with `actor` versus `selected`;
3. preserving the original target stage with an as-pattern reached the same
   `actor` versus `selected` mismatch when passing it to the delegate.

The exact retained diagnostic is:

```text
IteratorStage ... actor (singleton LAdvance actor)
vs
IteratorStage ... selected (singleton LAdvance actor)
Mismatch between: actor and selected.
```

This is not a lookup, fiber, lifecycle, dictionary, or iterator-outcome wall.
Attempt 3 had already completed occurrence, exact fiber, lifecycle, and source
lookup transport. The missing fact is the actor equality hidden behind the
singleton transition occurrence. Direct dependent occurrence elimination did
not reindex the separately named outer stage index through the delegate call.
Per protocol, the complete uncommitted locator was removed at attempt 3.

## Exact next decomposition

Do not retry the failed locator unchanged. Give these separate fresh budgets:

1. `lAdvanceActorInjective`: constructor injectivity
   `(LAdvance leftActor = LAdvance rightActor) -> leftActor = rightActor`, by
   `Refl`.
2. `singletonAdvanceStageActorSame`: consume one target singleton stage,
   eliminate `StageFromAdvance`, project the singleton transition equality with
   `cong transitionAction (singletonOccursSelected occurs)`, and apply helper 1.
   This intentionally discards stored transition dictionaries before actor
   reindexing.
3. A revised `locateSingletonAdvanceStageFromOwnerLookup` must first eliminate
   `singletonAdvanceStageActorSame ... targetStage`; only in its `Refl` branch
   perform the exact stage/fiber/lifecycle elimination, lookup transport, and
   delegation.
4. Then construct the one-clause family wrapper and continue the already
   accepted singleton-RAR, moved-pair-RAR, whole-RAR, field, and assembly chain.

The preferred producer form is a small correlated package if direct actor
`Equal` transport still leaves the target-stage term generalized. The package
must own both `selected = actor` and the exact original stage; it may not
identify independently stored `DecEq` dictionaries.

## Status

- identity prefix RAR: **closed and frozen**;
- singleton advance lookup transport: **closed**;
- one-stage L-Advance locator: **open at actor index reification**;
- family wrapper and singleton RARs: **unopened**;
- moved-pair and whole RAR: **unopened**;
- fields 1–8: **closed and frozen**;
- field 9: **open**;
- fields 10–15 foundations: **closed and frozen; population pending**;
- occurrence fold/result/body: **unopened**;
- holes: **20**, split **6/4/8/1/1**.

The accepted remaining band is held at **1–10 shifts**. The body-closure review
boundary was not reached.

## Isolation

Production `src/`, `dgamma.ipkg`, CP3, the frozen 1183-byte adjacent interface,
revision-21 surfaces, prefix RAR, fields 1–8, and fields 10–15 foundations are
unchanged. No escape hatch, hole, postulate, public surface, or failed locator
was retained.
