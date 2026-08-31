# O6 revision 91: correlated singleton-stage package escalation

## Scope

Grind shift #99 (overall #153) resumed from accepted revision 90 `6f599c0` and
opened only the pre-authorized correlated-package fallback for the singleton
L-Advance actor index. The package producer exhausted its independent three
fresh attempts. Its consumer could not be opened because no package constructor
survived. The entire unit was removed. Per the explicit escalation boundary,
the next shift is design-only on the singleton stage representation: no fourth
package edit, no fifth cure, and no RAR or assembly work.

## Intended package

`LocatedSingletonAdvanceActor` was indexed by the original target stage and was
designed to own jointly:

- the exact original target `IteratorStage`;
- the proof `selected = actor`;
- the singleton `Fired ... (LAdvance actor)` trace index.

Its producer eliminated one `StageFromAdvance` and used only
`viewConsStageOccurrence occurs`:

- `ConsStageOccursHere` for the exact singleton head;
- `ConsStageOccursLater _ later` eliminated by `noOccurrenceInEmpty later`.

It never compared whole dependent transitions and never compared stored
`DecEq` dictionaries.

## Three package deaths

1. **Exact constructor index.** The constructor fixed its stage argument at
   actor and returned the package indexed by that stage. In the Here branch,
   the occurrence view refined the stage payload to the exact head, but the
   left-hand as-pattern retained the original `targetStage` name. Idris rejected
   the result index:

   ```text
   targetStage
   vs
   StageFromAdvance nameEq keyEq actor tag checked OccursHere ...
   ```

2. **Generalized selected index.** The constructor accepted a stage indexed by
   arbitrary `selected` plus an explicit `selected = actor`. This retained the
   actor equality but its result was still indexed by the constructor's stage
   argument, so the same original-stage versus reconstructed-stage mismatch
   remained.

3. **Separate original-stage index and stage equality.** The constructor was
   changed to accept a correlated stage, an explicit `stage = targetStage`, and
   `selected = actor`, returning the package at the independent original
   `targetStage` index. Idris could not scope/infer the dependent type of that
   constructor-level target index:

   ```text
   Can't solve constraint between:
     IteratorStage ... selected (singleton LAdvance actor)
   and:
     ?type_of_targetStage
   ```

   The constructor was therefore not generated, and the producer necessarily
   failed as undefined.

These deaths are all declaration-level joint-introduction failures. The Here
and Later occurrence cases themselves elaborated; the failure is retaining the
opaque original stage identity while simultaneously refining its actor index.
No lookup, lifecycle, generator map, iterator outcome, or independence theorem
was reached.

## Escalation boundary reached

The correlated package is the pre-authorized fallback after the bare equality
ladder. Its constructor exhausted all three fresh attempts, so the package
consumer is uninhabitable and cannot receive a meaningful separate attempt.
This satisfies the stipulated package-plus-consumer escalation condition in the
only reachable way. No fourth package declaration and no fifth cure are
permitted in this implementation shift.

## Required design-only next campaign

The next shift must make **no retained Idris proof change** until a declaration
shape is reviewed. It should compare the checked joint-introduction precedents
from revisions 66 and 71 and decide among representation-level options only,
for example:

1. a package indexed by a `LocatedConsTargetStageRuntime`-style producer rather
   than raw `IteratorStage`;
2. a constructor whose explicit ordinary parameters include both the original
   stage and its full stage type before any equality field, preventing the
   generated `?type_of_targetStage` scope loss;
3. a singleton-specific occurrence GADT whose Here constructor carries the
   original stage and all payload projections without reconstructing it;
4. changing only the new internal package to store observational runtime
   equalities instead of propositional stage identity, if the frozen delegate
   can consume that honestly.

The design review must identify the exact consumer type and demonstrate that it
can eliminate the chosen package once while keeping the original target stage
index. It may not revise `IteratorStage`, `LocatedSingletonAdvanceStageReplay`,
`locateSingletonAdvanceStageReplay`, revision-20/21 surfaces, or any frozen
public capital without a separate authorization.

## Status

- identity prefix RAR: **closed and frozen**;
- singleton advance lookup transport: **closed and frozen**;
- LAdvance actor injectivity: **closed and frozen**;
- bare actor equality ladder: **exhausted and removed**;
- correlated package fallback: **exhausted and removed**;
- locator/family wrapper/singleton RARs: **unopened**;
- moved-pair and whole RAR / field 9: **unopened**;
- fields 1–8: **closed and frozen**;
- fields 10–15 foundations: **closed and frozen; population pending**;
- occurrence fold/result/body: **unopened**;
- holes: **20**, split **6/4/8/1/1**.

The previous **1–10 implementation-shift** band is no longer asserted as an
implementation forecast at this escalation boundary. A design-only shift is
required before re-estimating; the numerical downstream obligations are
unchanged.

## Isolation

Production `src/`, `dgamma.ipkg`, CP3, the frozen 1183-byte adjacent interface,
revision-21 surfaces, prefix RAR, lookup transport, actor injectivity, fields
1–8, and fields 10–15 foundations are unchanged. No escape hatch, hole,
postulate, public surface, package, or failed producer was retained.
