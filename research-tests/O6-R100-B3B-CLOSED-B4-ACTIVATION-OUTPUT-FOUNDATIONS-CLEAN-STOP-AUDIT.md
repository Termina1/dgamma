# O6 revision 100: B3b closed; B4 activation-output foundations retained

## Scope

Grind shift #108 (overall #162) resumed from accepted safe HEAD `73a8d37`.
The shift followed the revision-99 top-level-helper ruling and stopped at a clean
committed boundary before attempting the remaining two-order activation
classifier assembly.

Completed:

1. all three top-level B3b raw-output/checked-output comparison helpers;
2. the complete nonempty-Reloading outcome package, producer, and
   one-elimination consumer;
3. the complete generic retire-then-paper-activation exclusion;
4. producer-owned activation output-control foundations for Begin, empty
   Finish, one-step Finish, and Iter;
5. the generic paper-activation output-control producer;
6. activation-output-followed-by-Begin exclusion.

Not opened: final B4 two-order dispatcher, B5, B6, pair RAR, fields, and
assembly.

## B3b top-level helpers

Commit `0c848b5` retains three fully explicit helpers:

- `r99UnavailableVersusChecked`;
- `r99RaiseVersusChecked`;
- `r99DivertVersusChecked`.

Their signatures carry ordinary explicit `RuleTag` arguments. They introduce no
local tag equality. Each projects the checked equation first and compares it to
the producer-owned raw result using raw determinism. The Raise and Divert
helpers return both exclusions:

```idris
(Not (observedTag = LIterTag),
 Not (observedTag = LFinishTag))
```

The helper unit checked on attempt 1 with fresh direct CP5 and R16 checks.

## B3b complete

Commit `f808d5a` retains:

- `R99RetiredNonEmptyAdvanceOutcome` with explicit raw equality fields;
- `r99ClassifyRetiredNonEmptyAdvanceRaw`;
- `r99ProduceRetiredNonEmptyAdvanceOutcome`;
- `r99ConsumeRetiredNonEmptyAdvanceOutcome`.

The producer uses `with (...) proof` for both capability resolution and
`runStepEffect`, and inlines the evaluator’s exact `pushLocalUndo` expression in
the successful branch. Its only outcomes are:

- unavailable;
- L-Raise;
- L-Divert.

The consumer performs exactly one outcome elimination and delegates each branch
to the top-level helper. It contains no local tag equality.

The entire retained unit checked on attempt 1 with fresh direct CP5 and R16
checks.

**B3b is fully closed.**

## Generic retirement/activation exclusion

Commit `5176ae7` retains:

- `r99SelectPaperAdvanceExclusion`;
- explicit non-Reloading retired raw normalizers;
- `r99RetireThenPaperAdvanceImpossible`;
- `r99RetireThenPaperActivationImpossible`.

The final theorem:

1. produces and eliminates the exact B1 retirement projection;
2. uses retained B2 for L-Begin;
3. dispatches empty Reloading to B3a;
4. dispatches nonempty Reloading to B3b;
5. handles Inactive, Active, and Unloading through explicit raw `Nothing`
   normalizers;
6. requires an exact owner equality and reindexes it before calling an
   actor-specific helper.

Attempt 1 reached two known issues: a local raw equality and an unstated same
owner premise. Attempt 2 moved raw normalizers to top-level functions and made
the owner equality explicit; it passed. Fresh direct CP5 and R16 checks passed
before commit.

## B4 activation output foundations

### Output family and simple cases

Commit `f197180` retains:

- `r99ViewEqReflexive` and `r99TargetMatchesSelf`;
- `R99PaperActivationOutputControl` with only Reloading and Active constructors;
- `r99BeginOutputControl`;
- `r99FinishEmptyOutputControl`.

The package owns the exact owner lookup in the checked activation endpoint. The
Begin output is Reloading; empty-program Finish is Active.

Attempt 1 found the missing explicit `targetMatches (Just view) view = True`
normalizer. Attempt 2 supplied the structural reflexivity proof and passed.
Fresh R16 passed before commit.

### One-step Finish

Commit `9a27f12` retains `r99FinishOneOutputControl`.

It uses proof-retaining capability and evaluator cases. Capability absence and
L-Raise contradict the checked L-Finish tag. Successful execution constructs the
exact Active owner with the evaluator’s inlined `pushLocalUndo` accumulator.

Attempts:

1. local raw-unavailable equality hit the known local-binding elaboration class;
2. direct top-level/raw composition closed that branch, then the successful
   branch exposed a let-bound `nextAccumulator` opacity;
3. inlining `pushLocalUndo` closed the function.

Fresh direct CP5 and R16 checks passed before commit.

### Iter

Commit `09a5059` retains `r99IterOutputControl`.

It has the analogous complete resolution/evaluator dispatch and constructs the
exact Reloading `(next :: more)` owner after a checked L-Iter. It checked on
attempt 1 with fresh CP5 and R16.

### Generic producer

Commit `4fa71ba` retains `r99PaperActivationOutputControl`, covering all three
paper activation constructors and all three operational advance-source
constructors.

Attempts:

1. the dependent `PaperAdvanceSource` constructor stored its own source registry
   and would not identify it with the caller’s independently let-bound raw
   equation;
2. naming the constructor-owned source still left the raw equation attached to
   the caller source;
3. transporting the raw equation explicitly through the constructor-owned
   source equality closed all branches.

Fresh direct CP5 and R16 checks passed before commit.

### Activation output cannot Begin

Commit `f90908d` retains `r99ActivationOutputCannotBegin`. A second checked
L-Begin source view requires an Inactive owner, contradicting either exact
Reloading or exact Active output lookup.

The proof source checked on attempt 1. The second unit attempt passed source
checking but `git diff --cached --check` found one terminal blank line. The
third attempt removed it, freshly rebuilt CP5/R16, and committed.

## B4 remaining boundary

The generic output family intentionally distinguishes only Reloading versus
Active, not the originating paper tag. This is sufficient to exclude a later
Begin. To finish the two-order classifier, the remaining semantic fact is:

```text
checked L-Finish output is Active;
no paper activation is applicable from that exact Active owner.
```

The existing Finish constructors already prove Active output operationally, but
the generic return type does not expose that constructor after an opaque
producer call. Do not attempt to recover it by rewriting or by a caller-supplied
classification.

Recommended next package:

- a producer-owned, tag-indexed activation-output class whose constructors are
  exactly Begin/Reloading, Iter/Reloading, and Finish/Active; or
- a specialized producer-owned `PaperFinishOutputActive` package built directly
  from the checked Finish equation using the already checked empty/one-step
  recipes.

Then prove `Finish -> paper activation -> Void`, and dispatch the 3x3 two-order
matrix:

- any Begin is contradicted in one of the two orders by
  `r99ActivationOutputCannotBegin`;
- any Finish is contradicted by the Active-output exclusion;
- only Iter/Iter remains.

No actual B4 two-order classifier declaration was retained, so no partial or
misleading classifier surface exists.

## Deferred status

- B3b: **closed**;
- retire-then-paper-activation: **closed**;
- B4 activation output semantics: **all operational branches closed**;
- B4 two-order classifier: **not yet assembled**;
- B5 orchestration classifier: **unopened**;
- B6 dispatcher/determinism: **unopened**;
- pair RAR: **unopened**;
- field 9: **retained composition still awaits pair RAR**;
- fields 10–15: **foundations retained; population unopened**;
- assembly: **unopened**;
- holes: **20**, split **6/4/8/1/1**.

The implementation band remains **suspended** because the B4 classifier has not
yet checked. Reconsider only after the exact two-order B4 producer checks.

## Manifest and isolation

```text
NO_FROZEN_SURFACE_CHANGE_REQUIRED
```

All additions are private proof capital. No revision-21 public surface, frozen
Track-A/B1/B2/B3a declaration, adjacent result type, or genuine producer
signature changed.

`adjacentSwapSuffixSpike` remains 1183 bytes with SHA-256
`e6d0c2d669355e5b7bef9efea1707f5853c708deb888bafe5770ba40dbd15a41`.
Production `src/`, `dgamma.ipkg`, and CP3 blob
`2c697e532e83989de8591fa6a4378747c6a501c0` remain unchanged.

No hole, postulate, `believe_me`, `assert_total`, unsafe escape, probe file, or
staged change remains.
