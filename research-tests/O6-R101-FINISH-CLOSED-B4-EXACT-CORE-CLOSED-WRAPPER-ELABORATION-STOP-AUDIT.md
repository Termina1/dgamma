# O6 revision 101: Finish closes; B4 exact core closes; wrapper elaboration stop

## Scope

Grind shift #109 (overall #163) resumed from accepted HEAD `fc7c3fa`.
The shift retained the specialized Finish/Active package, the complete
Finish-followed-by-activation exclusion, and a checked exhaustive two-order
activation core. It then stopped under the mandatory three-attempt rule when the
producer wrapper over four aligned transition views exhausted its unit budget.

B5, B6, pair RAR, fields, and assembly were not opened.

## Specialized checked Finish output

Commit `c4c57d2` retains:

- `R100PaperFinishOutputActive`;
- `r100FinishEmptyOutputActive`;
- `r100FinishOneOutputActive`;
- `r100ProducePaperFinishOutputActive`.

This is the reviewer-authorized smallest sufficient package. The producer is
built directly from the checked L-Finish equation. It projects the checked
equation first, eliminates `PaperAdvanceSource` once, explicitly transports the
raw equation through the constructor-owned source equality, and dispatches to
the checked empty/one-step evaluator recipes. The one-step success branch uses
the exact inline `pushLocalUndo` expression.

The unit passed on attempt 1 under a fresh direct CP5 check and R16 check.

## Finish followed by paper activation is impossible

Commit `2b55b29` retains:

- `r100FinishActiveAsActivationOutput`;
- `r100ActiveFoundVersusAdvanceSource`;
- `r100ActiveOutputCannotPaperAdvance`;
- `r100RetargetFinishOutputActive`;
- `r100FinishThenPaperActivationImpossible`.

The theorem handles all three later paper activation constructors:

- L-Begin contradicts the exact Active output via the already retained
  activation-output/Begin exclusion;
- L-Iter and L-Finish project their checked equation, eliminate the exact
  `PaperAdvanceSource`, transport its source lookup through the constructor-owned
  source equality, and contradict Active versus Reloading.

All output retargeting is producer-owned and explicit. No independently let-bound
owner equality is expected to reindex a package.

Attempts:

1. exposed the known constructor-owned source-registry correlation boundary and
   independent actor-output reindexing boundary;
2. a top-level source-shape comparison helper closed the first boundary; direct
   equality elimination still did not reindex the independently produced output;
3. the explicit top-level output retarget helper closed the unit.

Fresh direct CP5 and R16 checks passed before commit.

## Exhaustive exact two-order activation core

Commit `695307b` retains:

- `r100RetargetActivationOutputControl`;
- `r100ExactTwoOrderActivationTags`.

The latter accepts four exact checked transitions:

1. source left;
2. source right;
3. moved right with the exact source-right action/tag;
4. moved left with the exact source-left action/tag;

plus the four correlated paper activation witnesses and owner equality. It
checks all nine source activation pairs constructively:

- Begin/Begin: source-left output contradicts source-right Begin;
- Begin/Iter and Begin/Finish: moved-right output contradicts moved-left Begin;
- Iter/Begin: source-left output contradicts source-right Begin;
- Iter/Finish: moved-right Finish output contradicts moved-left Iter;
- Finish/Begin, Finish/Iter, Finish/Finish: source-left Finish contradicts the
  later source-right activation;
- Iter/Iter is the only returning constructor pair and yields exact
  `(leftTag = LIterTag, rightTag = LIterTag)`.

Attempt 1 exposed independent actor reindexing after owner elimination. Attempt 2
introduced explicit producer-owned output retargeting and passed. Fresh CP5 and
R16 checks passed before commit.

Thus the **3x3 operational B4 classification core is closed**, but no public or
private final B4 classifier package was declared.

## Exhausted producer-wrapper unit

The attempted wrapper was intended to return a private
`R100EqualOwnerActivationIterPair` containing source/moved activation witnesses
and exact source tag equalities. It consumed:

- the source pair alignment;
- `movedPairAligned`;
- the diamond action/tag projection equalities;
- source and moved activation branches;
- exact checked-action transport into the already checked 3x3 core.

Attempts:

1. omitted explicit source state arguments in the wrapper signature; Idris could
   not infer the transition indices;
2. added explicit `first/middle/originalFinal` arguments but omitted them from
   the definition LHS, causing argument-position misalignment;
3. corrected the LHS. Elaboration then stopped at the first annotated equality
   over independently inferred, untyped local aligned-head views:

```text
When unifying:
    Action name key value world error
and:
    Type
Mismatch between: Action name key value world error and Type.
```

The failed wrapper unit, including its result record and helper, was removed in
full. No partial B4 classifier surface remains.

This is an elaboration/scoping stop, not a semantic counterexample. The next
attempt must follow the standing dependent-boundary recipe more strictly:

- define a producer-owned package containing all four `LocalAlignedHeadView`
  values and the exact cross-action/tag equations;
- give every package field and local a fully explicit quantity-0 type;
- eliminate that package once in the final wrapper;
- do not use inferred `let 0 sourceHead = ...` declarations across annotated
  dependent equalities.

Because the wrapper unit exhausted three attempts, the shift stopped immediately.
B5 and later work were not opened.

## Status

- specialized Finish/Active package: **closed**;
- Finish -> paper activation `Void`: **closed**;
- B4 3x3 exact operational core: **closed**;
- final producer-owned B4 classifier package: **open after three-attempt
  elaboration stop**;
- B5 presence classifier: **unopened**;
- B6 safety/determinism dispatcher: **unopened**;
- pair RAR: **unopened**;
- field 9: **retained append composition still awaits pair RAR**;
- fields 10–15 population: **unopened**;
- assembly: **unopened**;
- holes: **20**, split **6/4/8/1/1**.

The implementation band remains suspended until the final exact B4 producer
checks. No re-established band is proposed at this gate.

## Manifest and isolation

```text
NO_FROZEN_SURFACE_CHANGE_REQUIRED
```

No revision-21 or frozen surface changed. `adjacentSwapSuffixSpike` remains 1183
bytes with SHA-256
`e6d0c2d669355e5b7bef9efea1707f5853c708deb888bafe5770ba40dbd15a41`.
Production `src/`, `dgamma.ipkg`, and CP3 remain unchanged.

No new hole, escape hatch, probe, failed unit, or staged change remains.
