# O6 revision 75: moved-retire/insert elaboration stop

## Scope

Grind shift #83 (overall #137) resumed from accepted rollback boundary
`130603d`. It rebuilt field-2 retirement/provenance capital as small units under
the permanent revision-74 protocol: before every proof commit the CP5 TTC/TTM
was removed and a direct source check had to emit a visible
`Building DGamma.CP5ConfluenceLocalDiamondSpike` line. R16 was run only after
that check as additional assembly evidence.

## Fresh-checked units retained

The shift retained these constructive units, all private:

1. action/tag reconstruction of `ParentRecoveryStep`;
2. sealed-suffix preservation of `NoParentRecovery`;
3. sealed-suffix preservation of `ChildRetiresBeforeRecovery`;
4. sealed-suffix preservation of `ChildRetirementProvenance`;
5. adjacent-prefix/pair preservation of no-recovery;
6. adjacent-prefix/pair preservation of ordered retirement, including the
   landed `candidateSafetyExcludesParentRecovery` boundary;
7. adjacent-prefix/pair preservation of retirement provenance;
8. foreign checked parent-yield transport in both directions;
9. producer-owned exact-fiber retirement parent-yield transport in both
   directions;
10. orchestration parent-yield transport in both directions, with explicit
    same-owner Insert/Retire/Remove cases;
11. aligned foreign/orchestration yield wrappers;
12. moved-right and moved-left parent-yield reconstruction;
13. moved-step recovery classification and provenance prefixing;
14. same-action and pointwise registration-step discipline transport;
15. complete producer-sealed suffix registration-discipline transport.

The pinned binder-capture, nonlinear suffix patterns, same-owner retirement
correlation, and suffix declaration-order walls were discharged. Every new
lowercase dictionary/component binder is explicit and locally named; every
proof local is quantity 0.

## Exhausted unit

The next unit attempted to prove:

```idris
0 movedRetireBeforeInsertedChildImpossible :
  ... ->
  transitionAction left = OInsert child insertedParent insertedComponent ->
  transitionAction right = ORetire child -> Void
```

Its semantics are straightforward: checked source-left insertion requires the
child absent at `pairFirst`, while checked moved-right retirement requires it
present at the same state. Three fresh attempts were spent:

1. dependent LHS reused the abstract `left` and the constructor exposed by
   `AlignedStep` nonlinearly;
2. after matching the exact `Fired` source-left value, the moved-pair tail
   pattern reused the record projection `movedLeft diamond` nonlinearly;
3. after erasing the tail pattern, `checkedActionProjects` still saw the
   producer's `movedAction`, while the local call demanded `ORetire child`;
   the available `trans (movedRightAction diamond) rightRetire` equation had
   refined the action result but not the independently named checked-action
   argument.

The exact terminal diagnostic was:

```text
Mismatch between: movedAction and ORetire child.
```

This is an elaboration/reindexing wall in an already checked impossible
operational shape, not a new semantic premise gap. The unverified helper was
removed in full. The retained HEAD ends immediately before this unit.

## Recommended next cure

Use a producer-owned dependent package for the moved-right aligned head:

- eliminate `movedPairAligned diamond` once;
- package its action, tag, checked equation, and the explicit equation to
  `transitionAction right` together;
- reindex the checked equation through
  `trans (movedRightAction diamond) rightRetire` before calling
  `checkedActionProjects`;
- never pattern the moved tail separately.

That package is one new unit with a fresh three-attempt budget. If it closes,
resume moved-left tail provenance, moved-pair `RegistrationStepDiscipline`,
whole adjacent discipline, and only then close bundle field 2.

## Status

- field 1: **closed**;
- field 2 parent-yield sub-obligation: **closed**;
- field 2 sealed-suffix discipline: **closed this shift**;
- field 2 moved-pair yield transport: **closed this shift**;
- field 2 adjacent retirement provenance primitives: **closed this shift**;
- field 2 whole adjacent discipline: **not closed**;
- fields 3–15: **unopened**;
- final assembly/body: **unopened**;
- holes: **20**, split **6/4/8/1/1**.

The prior **3–15** band consumed one implementation shift. Given the retained
capital and this local elaboration stop, the honest remaining estimate is
**2–14 shifts**.

## Frozen-capital audit

No public/frozen declaration changed. Revision-21 surfaces, the joint generator,
RAR chain, relational maps, occurrences, ordinals, and parent-yield package
remain unchanged. `adjacentSwapSuffixSpike` remains 1183 bytes with SHA-256
`e6d0c2d669355e5b7bef9efea1707f5853c708deb888bafe5770ba40dbd15a41`.
Production `src/`, `dgamma.ipkg`, and CP3 blob
`2c697e532e83989de8591fa6a4378747c6a501c0` remain isolated. No hole or escape
hatch was added.
