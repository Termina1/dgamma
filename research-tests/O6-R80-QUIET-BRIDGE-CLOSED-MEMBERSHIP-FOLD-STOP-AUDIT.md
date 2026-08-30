# O6 revision 80: quiet lifecycle bridge closes; membership fold stop

## Scope

Grind shift #88 (overall #142) resumed from accepted revision-79 boundary
`bbdb06d` and executed the authorized field-6 decomposition. Each unit had its
own fresh three-attempt budget. Fields 1–5 and every frozen revision-19/20/21,
registration, suffix, occurrence, generator, RAR, and public-interface surface
remain unchanged.

## Retained checked capital

Every retained helper received TTC/TTM removal, a visible direct CP5 source
rebuild, a lemma-sized commit, and an additional R16 assembly check.

1. `lifecycleQuietAt` (`c6e3e4c`) is a private total executable classifier over
   one lifecycle and its concrete target query. Attempt 1 exposed the missing
   explicit `DecEq name`; attempt 2 added the named dictionary and passed.
2. `lifecycleControlQuietRelated` (`e0db494`) passed on attempt 1. It eliminates
   exactly one `LifecycleControlRelated`; outcome/view equalities and the target
   equality remain under that single correlated elimination.
3. `quietFiberAsLifecycleQuietAt` (`fd87c5b`) passed on attempt 1, proving the
   executable normalization for all five lifecycle constructors.
4. `pointwiseQuietFiberTrue` (`d8743fd`) passed on attempt 2. It combines
   `pointwiseConcreteTargetFiberSame`, the single-elimination lifecycle lemma,
   and both normalization directions. All dependent equalities use explicit
   `Equal` statement shapes and all proof locals are quantity 0.

This closes the revision-79 independently-bound active-view wall. Per-fiber
quietness transport is fully constructive and retained.

## Exhausted membership-fold unit

The target-registry fold `pointwiseQuietTrue` exhausted its separate three-
attempt budget and was removed.

1. The local `targetAll` type could not infer the dependent `value` parameter
   from an unannotated `MkCoeffectContext`.
2. Replacing the constructor with `registry rightState` still left the dependent
   `quietEntryFor` value unresolved.
3. Explicitly supplying every `quietEntryFor` and `lookupFiber` type parameter
   closed inference. Elaboration advanced through exact target membership,
   target lookup, source lookup recovery, and per-fiber quietness, then stopped
   because the local `where` abstraction distinguished the as-pattern alias
   `rightState` from its concrete constructor:

```text
Mismatch between:
  MkSystemState rightWorld (MkCoeffectContext rightEntries rightUnique)
and:
  rightState.
```

This is a dependent state-alias/elaboration wall in the established
producer-owned concrete-state class, not a quietness semantic gap. The unit was
removed after budget exhaustion; all four prior quietness helpers remain.

## Recommended cure

Introduce a top-level private
`pointwiseQuietEntriesTrueExplicit` whose statement takes worlds, entries, and
uniqueness proofs explicitly and whose `ControlEquivalent`, effects,
well-formedness, source quietness, and result mention only the two literal
`MkSystemState ...` constructors. Perform the tracked-membership recursion
there. Then make `pointwiseQuietTrue` a one-clause wrapper that pattern-matches
both states and calls the explicit helper. Give the explicit fold and wrapper
separate fresh budgets.

The tracked membership shape itself is validated: recursion carries an
embedding from the current suffix into the original target entries, derives
lookup from that `Elem`, and embeds the tail through `There`. No detached domain
or lookup premise is required.

## Status

- fields 1–5: **closed and unchanged**;
- lifecycle quiet classifier: **closed**;
- lifecycle relation preservation: **closed**;
- fiber normalization and pointwise fiber bridge: **closed**;
- target-registry fold: **not retained**;
- field 6: **not yet complete**;
- fields 7–15: **unopened in this shift**;
- final assembly/body: **unopened**;
- holes: **20**, split **6/4/8/1/1**.

Because this shift retained the full semantic field-6 bridge but not the final
finite fold, the accepted **1–12 shift** remainder is held.

## Isolation

The 1183-byte `adjacentSwapSuffixSpike` signature retains SHA-256
`e6d0c2d669355e5b7bef9efea1707f5853c708deb888bafe5770ba40dbd15a41`.
Production `src/`, `dgamma.ipkg`, and CP3 blob
`2c697e532e83989de8591fa6a4378747c6a501c0` remain isolated. No hole, postulate,
escape hatch, detached caller capital, or public field was added.
