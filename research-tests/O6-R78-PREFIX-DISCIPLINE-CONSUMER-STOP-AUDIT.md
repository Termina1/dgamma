# O6 revision 78: prefix-discipline view closes; consumer stop

## Scope

Grind shift #86 (overall #140) resumed from accepted revision-77 boundary
`6f2d96a` and executed the authorized nonempty-prefix dependent-view cure. The
frozen revision-21 surfaces, revision-76 retirement package, revision-77 units,
parent-yield package, sealed suffix replay, joint generator/RAR chain, and public
adjacent-swap interface were not changed.

## Retained checked capital

`PrefixRegistrationDisciplineView` and
`producePrefixRegistrationDisciplineView` are retained at `6938471` after a
visible fresh CP5 source rebuild and R16 assembly check.

The private erased view seals at construction:

- the exact dependent prefix head;
- the exact constructor-owned source rest;
- equality of that head with the expected prefix head;
- equality of that rest with `appendTransitions prefixTail pairBody`;
- the head `RegistrationStepDiscipline` indexed by the stored head/rest;
- the tail `RegistrationDiscipline` indexed by the same stored rest.

The producer's first attempt was rejected because a nonlinear pattern variable
for the rest unified with the append expression. Attempt 2 replaced that
pattern variable by an erased wildcard and constructed the exact expected rest
explicitly; direct fresh elaboration passed. Every record field is quantity 0.

## Exhausted consumer unit

The separate `adjacentRegistrationDiscipline` consumer exhausted its fresh
three-attempt budget:

1. The package elimination and both proof reindexes elaborated far enough to
   reach the first local type annotation, where the recursive prefix middle
   state was not in scope by name.
2. Naming the constructor index explicitly as
   `MoreTransitions {middle = prefixMiddle} ...` closed that issue. Idris then
   rejected the first local definition because its continuation was indented as
   part of the type annotation.
3. Correcting the `sourceRest` indentation advanced elaboration to the next
   local, `targetRest`, where the identical indentation defect remained.

The terminal diagnostic was:

```text
While processing type of ... targetRest. Undefined name ... targetRest.
```

This is a layout/parser failure, not a semantic or dependent-index wall. The
package had already supplied the accepted correlation: the consumer reindexed
both the action-indexed head discipline and tail discipline before constructing
its retirement callback; the callback passed exact append-indexed retirement
provenance to `adjacentChildRetirementProvenance`.

The entire unverified consumer was removed. The checked view remains. No field
2 claim is made.

## Next step

Reintroduce the consumer as a fresh unit only after the next gate. Use a
layout-normalized `let` block in which every declaration and its definition
begin in the same layout column (or split each reindex into a tiny helper). The
consumer should preserve the already-ratified single package elimination and
reindex-before-provenance order. It receives a new three-attempt budget.

## Status

- `PrefixRegistrationDisciplineView`: **closed**;
- producer: **closed**;
- whole-prefix `adjacentRegistrationDiscipline`: **not retained**;
- field 2: **open only at the consumer**;
- fields 3–15: **unopened**;
- final result/body: **unopened**;
- holes: **20**, split **6/4/8/1/1**.

Because this shift retained only the already-planned correlation package and did
not complete field 2, the accepted **1–13 shift** remainder is held.

## Isolation

The 1183-byte `adjacentSwapSuffixSpike` interface and SHA-256
`e6d0c2d669355e5b7bef9efea1707f5853c708deb888bafe5770ba40dbd15a41` remain
unchanged. Production `src/`, `dgamma.ipkg`, and CP3 blob
`2c697e532e83989de8591fa6a4378747c6a501c0` remain isolated. No hole, postulate,
escape hatch, detached premise, or public field was added.
