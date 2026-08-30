# O6 revision 70: registration safety lands; parent-yield elimination stop

## Scope

Grind shift #78 (overall #132) implemented the accepted revision-21 safety
boundary from `24e3fea`. The field/producers and all affected consumers are
landed and buildable. Bundle field 2 then advanced to its first private
constructive sublemma, transport of `ParentRegistrationYield` through
`ControlEquivalent`, where the fresh dependent-elimination budgets exhausted.
The uncommitted helper unit was reverted in full. No bundle field or adjacent
body was partially retained.

Safe implementation HEAD before this audit: `739922c`.

## 1. Revision-21 live field — closed at `e306708`

The research module now exports protocol-independent erased safety:

```idris
public export
data CandidateRegistrationSwapSafety left right where
  CandidateActivationActivation : ...
  CandidateActivationOrchestration : ... -> parentSafe -> ...
  CandidateOrchestrationActivation : ... -> childSafe -> parentSafe -> ...
  CandidateOrchestrationOrchestration : ... ->
    insertedChildrenDistinct -> generatedLicensesDoNotCross -> ...
```

`LocalRelationalDiamond` appends exactly one field:

```idris
0 registrationSwapSafety : CandidateRegistrationSwapSafety left right
```

The field is quantity 0. No record parameter, prior field, result type, or
adjacent function declaration changed.

All four centralized producers supply evidence they already owned:

| Producer | Live field constructor | Evidence |
|---|---|---|
| `activationActivationDiamondSpike` | `CandidateActivationActivation` | `leftActivation`, `rightActivation` |
| `activationOrchestrationDiamondSpike` | `CandidateActivationOrchestration` | `leftActivation`, `rightOrchestration`, `parentSafe` |
| `orchestrationActivationDiamondSpike` | `CandidateOrchestrationActivation` | `leftOrchestration`, `rightActivation`, `childSafe`, `parentSafe` |
| `orchestrationOrchestrationDiamondSpike` | `CandidateOrchestrationOrchestration` | both orchestration classifiers plus `insertedChildrenDistinct safety` and `generatedLicensesDoNotCross safety` |

The research spike checked on the first attempt. R16 and the byte-frozen spike
hash passed before and after the commit.

## 2. R19, retainers, and permanent counterexample — closed at `739922c`

`R19SuffixFreeFullAdjacentCertificatePositive` remains live. Its repeated-Iter
fixture supplies:

```idris
CandidateActivationActivation
  (PaperIterStep leftAdvance leftIter)
  (PaperIterStep rightAdvance rightIter)
```

No R19 public type changed and it was not retired.

The revision-21 design positive now imports and probes the live safety family;
its duplicate test-local data declaration was removed. All four retainers and
`candidateSafetyRejectsBareCounterexample` still check.

The old unsafe public shape is preserved only as the test-local
`RetiredBareLocalRelationalDiamond`. It retains the total evidence that every
pre-revision-21 operational/endpoint field was inhabitable while the swapped
registration discipline was false, but it has no live authority.

`R45BareDiamondSafetyProjectionNegative` is now the permanent live-boundary
negative. It attempts to construct the A/O safety for the exact
`LBegin 0 ; OInsert 1 (ChildOf 0)` counterexample. The retained diagnostic is:

```text
... is not a valid impossible case.
```

at `bareDiamondCannotProjectRegistrationSafety`, because the required
`parentSafe` specializes to `Not (0 = 0)`.

R19, the total counterexample positive, the live design positive, and the exact
negative all passed on the first attempt. R16 and spike SHA passed around the
commit.

## 3. Manifest landing

The baseline manifest now records revision 21 in both required ledgers:

- `approvedTypeAdditions`: `CandidateRegistrationSwapSafety`;
- `approvedRecordFieldRevisions`:
  `LocalRelationalDiamond.registrationSwapSafety`.

`cp5-r21-proposed-manifest-delta.json` is marked `PARTIALLY_LANDED` with the
field/producer and consumer commits. It remains partial only because bundle
field 2 and later O6 work are not closed.

## 4. Bundle field 2 decomposition

Target `RegistrationDiscipline` requires three layers:

1. unchanged prefix discipline, including child-retirement obligations whose
   suffix spans the swapped pair;
2. a branch-specific two-step swap using `registrationSwapSafety`; and
3. pointwise suffix discipline transport through `SealedSuffixReplaySpine`.

The first shared primitive is exact parent-yield transport at pointwise-related
states:

```idris
0 parentRegistrationYieldControlTransport :
  ControlEquivalent ... source target ->
  ParentRegistrationYield protocol nameEq parent component source ->
  ParentRegistrationYield protocol nameEq parent component target
```

This statement is semantically supported by `FiberControlRelated`: the
component/program is shared definitionally, `ReloadingControls` preserves the
remaining program exactly, and the target accumulator/view are available from
the related target lifecycle. No protocol equality, dictionary identity, or
runtime-table equality is needed.

## 5. Attempt ledger and stop

The semantic construction reached only dependent elimination of the pointwise
parent lookup. All versions kept proof locals at quantity 0.

### Lookup localization unit

A private proposed `LocatedRightControlFiber` localized:

- the target fiber;
- exact target lookup; and
- `FiberControlRelated` from the source parent fiber.

The locator itself is total:

```idris
locateRightControlFiber (SomeControlFibers related) =
  MkLocatedRightControlFiber _ Refl related
```

### Eliminator attempts

Three bounded eliminator strategies were tried and reverted:

1. **direct source-found/control case** — rewriting source lookup to
   `Just sourceFiber` did not make the abstract target lookup refinement
   available while matching `SomeControlFibers`;
2. **located target package destruction** — opening the located fiber and its
   relation together produced the familiar dependent unification:

   ```text
   Pattern variable targetFiber unifies with:
     MkFiber ... rightLifecycle
   Suggestion: Use the same name for both pattern variables, since they unify.
   ```

3. **ordinary-variable/projection eliminators** — separating target location,
   source/target fiber arguments, and an explicit
   `parentFiberAtYield sourceYield = sourceFiber` equality moved the failure but
   still could not refine the projection-indexed source fiber when eliminating
   `FibersControlRelated`:

   ```text
   Can't solve constraint between:
     MkFiber ...
   and:
     ... .parentFiberAtYield.
   ```

Intermediate variants also confirmed that untyped or unrestricted located
proof locals make erased locators inaccessible; the final attempts used fully
typed quantity-0 locals.

This is not a new semantic wall class. It is a private dependent-elimination
shape analogous to the earlier generated-registration projection wall. The
fresh final eliminator budget is exhausted, so the entire uncommitted helper
unit was reverted as required.

## 6. Recommended next unit

Use a projection-only cure, not a wider premise:

1. define a private `LocatedTransportedParentYield` package whose producer opens
   `FiberControlRelated` and `ParentRegistrationYield` together;
2. make its consumer project an already constructed target
   `ParentRegistrationYield`, avoiding any second independent elimination of
   `parentFiberAtYield`;
3. keep the ordinary variable on the consumer left-hand side and every local at
   quantity 0; and
4. only after that helper closes, build the structural pointwise provenance and
   discipline transport.

No public signature, record parameter, revision-21 field, or caller boundary
needs another change. In particular, do not expose target discipline or a
located target fiber as caller capital.

## Frozen-capital audit

This shift did not change:

- the 1183-byte `adjacentSwapSuffixSpike` declaration, SHA-256
  `e6d0c2d669355e5b7bef9efea1707f5853c708deb888bafe5770ba40dbd15a41`;
- `AdjacentSwapResult`;
- `ReplayInvariantBundle`;
- revision-20 relational-map/RAR surfaces;
- any revision-19/20 retained proof body;
- `src/`, `dgamma.ipkg`, or CP3 blob
  `2c697e532e83989de8591fa6a4378747c6a501c0`.

## Status

- revision-21 type/field: **landed and proved buildable**;
- four centralized producers: **4/4 updated**;
- R19 repeated-Iter positive: **updated, not retired**;
- permanent counterexample negative: **tracked and exact**;
- bundle field 1: **proved**;
- bundle field 2: **not yet proved; private parent-yield eliminator STOP**;
- bundle fields 3–15: **unopened**;
- final assembly: **unopened**;
- holes: **20**, split **6/4/8/1/1**;
- movement against accepted 4–18 band: **one shift consumed; 3–17 remain**.
