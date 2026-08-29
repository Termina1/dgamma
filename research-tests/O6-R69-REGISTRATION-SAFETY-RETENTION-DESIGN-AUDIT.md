# O6 revision 69: registration-safety retention design campaign

## Decision scope

This is the design-only shift #77 (overall #131) requested after the accepted
revision-68 field-2 stop at `e94d63e`. It proposes scoped frozen declaration
revision 21. It does **not** implement a cure in the research spike.

The campaign answers five questions:

1. Is the bare-diamond counterexample executable and constructive?
2. Does every local-diamond construction site in the R16 assembly chain already
   own the missing safety?
3. Can the preferred richer safety package be retained without changing the
   byte-frozen adjacent declaration?
4. Can an opaque genuine producer solve the problem under that same constraint?
5. What exact frozen/consumer manifest delta would implementation require?

Base HEAD: `e94d63e1ee65bd67a15f500df1fa4545341f8f21`.

## 1. Constructive counterexample pin

### Positive witness

`R45BareDiamondDisciplineCounterexamplePositive.idr` constructs a concrete
empty-key calculus instance with:

- a parent component whose first program step has registration yield tag `0`;
- a protocol catalog mapping tag `0` to the concrete child component;
- root insertion of the parent from the empty registry;
- source pair

  ```text
  LBegin 0 ; OInsert 1 (ChildOf 0) child
  ```

- target pair

  ```text
  OInsert 1 (ChildOf 0) child ; LBegin 0
  ```

- a trailing `ORetire 1` on both traces.

Every transition is checked by `checkedApplyAction`. The source whole trace has
a constructive `RegistrationDiscipline`: after `LBegin`, the parent is
`Reloading [yieldingStep]`, the step has the right tag/catalog entry, and the
child retires immediately in the insertion suffix.

The module also constructs `r45BareDiamond` directly with the public
`MkLocalRelationalDiamond`. It supplies moved-pair alignment, all branch
functions, pointwise effect/control endpoint relations, and target
well-formedness. Thus the counterexample does not depend on an uninhabited
operational or endpoint premise.

Finally:

```idris
0 r45TargetDisciplineImpossible :
  RegistrationDiscipline r45Protocol r45NameEq r45TargetTrace -> Void
```

is total. It opens the target child insertion's
`ParentRegistrationYield`; its parent lookup identifies `r45ParentFresh`, whose
lifecycle is `Inactive Nothing`, contradicting the required nonempty
`Reloading` lifecycle.

### Expected-failure pin

`R45BareDiamondFalseDisciplineNegative.idr` tries to construct exactly that
missing target yield. Its mandatory diagnostic is:

```text
Mismatch between: Reloading [r45YieldingStep] id EmptyView and Inactive Nothing.
```

This is tracked as an expected failure at
`bareDiamondCannotForgeTargetYield`.

Conclusion: revision 68's field-2 obstruction is executable, not merely an
absence of a convenient lemma.

## 2. Exhaustive construction-site inventory

The R16 chain is:

```text
r16ConfluenceTheoremAssembly
  -> fullPipelineFromBundles
  -> sortClosingFreeTraceSpike
  -> adjacent transpositions
  -> the four Lemma-71 local-diamond producers
```

`sortClosingFreeTraceSpike` remains a hole, so it has no hidden direct
constructor call. All live construction intended for that chain is centralized
in the four producers below. Exact source search at the base found four
research constructor sites and no others:

| Site | Base line | Branch | Missing evidence at site | Derivable there? | Probe |
|---|---:|---|---|---|---|
| `activationActivationDiamondSpike` | 17009 | A/A | no insertion-specific exclusion; retain both classifiers | **Yes**: `leftActivation`, `rightActivation` are explicit inputs | `retainActivationActivationSafety` |
| `activationOrchestrationDiamondSpike` | 17238 | A/O | right child insertion must not be licensed by the left activation actor | **Yes**: exact `parentSafe` is an explicit producer input | `retainActivationOrchestrationSafety` |
| `orchestrationActivationDiamondSpike` | 17449 | O/A | right activation actor must differ from an inserted child and its licensing parent | **Yes**: exact `childSafe` and `parentSafe` are explicit inputs | `retainOrchestrationActivationSafety` |
| `orchestrationOrchestrationDiamondSpike` | 17731 | O/O | inserted children distinct; neither inserted child crosses the other's licensing parent | **Yes**: `insertedChildrenDistinct safety` and `generatedLicensesDoNotCross safety` are fields of the already-required `OrchestrationSwapSafety` | `retainOrchestrationOrchestrationSafety` |

`R45GenuineDiamondSafetyDesignPositive.idr` checks all four retainers against a
test-local indexed `CandidateRegistrationSwapSafety`. The package is
protocol-independent: only the O/O producer's larger source package is indexed
by `protocol`; the two negative functions projected from it are not.

The candidate also proves:

```idris
0 candidateSafetyRejectsBareCounterexample :
  CandidateRegistrationSwapSafety r45Begin r45ChildInsert -> Void
```

In its only shape-compatible A/O branch, `parentSafe 1 0 child Refl` says the
left actor `0` is not parent `0`, immediately contradicting `Refl`. The other
three branch constructors contradict the concrete action classifiers.

### Other direct constructor users

The only base-tree direct constructor call outside the four research producers
is line 316 of `R19SuffixFreeFullAdjacentCertificatePositive.idr`. It is not in
the R16 assembly chain. It manually builds a repeated-`LAdvance` A/A fixture.
Both `PaperIterStep` witnesses are already in scope, so cure (a) can add the A/A
safety constructor without changing the R19 producer's public type.

The new R45 positive intentionally adds one further test-only bare constructor
use. At implementation it must be preserved as a test-local
`RetiredBareLocalRelationalDiamond`; the live safety-retaining constructor must
reject it.

No other `MkLocalRelationalDiamond` occurrence exists.

**Make-or-break result: PASS for cure (a).** Every R16-chain construction site
owns the exact safety needed for its branch; no new caller premise is required.
This does not pre-prove the later sorting hole's derivation of each producer's
existing inputs, but it introduces no new obligation at that upstream boundary.

## 3. Cure probes in both directions

### Cure (a): richer safety-retaining local diamond — PASS, preferred

Test-local proposed shape:

```idris
data RegistrationSwapSafety left right where
  RegistrationSwapActivationActivation :
    PaperActivationStep left -> PaperActivationStep right -> ...
  RegistrationSwapActivationOrchestration :
    PaperActivationStep left -> PaperOrchestrationStep right ->
    parentSafe -> ...
  RegistrationSwapOrchestrationActivation :
    PaperOrchestrationStep left -> PaperActivationStep right ->
    childSafe -> parentSafe -> ...
  RegistrationSwapOrchestrationOrchestration :
    PaperOrchestrationStep left -> PaperOrchestrationStep right ->
    insertedChildrenDistinct -> generatedLicensesDoNotCross -> ...
```

and one appended erased field:

```idris
0 registrationSwapSafety : RegistrationSwapSafety left right
```

Positive direction:

- all four construction-site retainers typecheck;
- the package is at quantity 0 and protocol-independent;
- all producer public types remain unchanged;
- the exact counterexample is rejected by the candidate type; and
- `adjacentSwapSuffixSpike` still mentions only the same
  `LocalRelationalDiamond` type, so its declaration text need not change.

Negative direction:

- `R45BareDiamondSafetyProjectionNegative.idr` proves the current bare record
  cannot be treated as the richer candidate; Idris reports a mismatch between
  `LocalRelationalDiamond ...` and `CandidateSafetyRetainedDiamond ...` at
  `bareDiamondCannotProjectRegistrationSafety`;
- the constructive counterexample proves why accepting a bare value would be
  unsound for field 2; and
- `candidateSafetyRejectsBareCounterexample` proves the proposed package does
  not accidentally certify it.

Public constructibility under cure (a): `MkLocalRelationalDiamond` may remain
public, but construction becomes safety-gated by the new erased argument. The
unsafe bare constructor shape disappears. R19 remains constructible with its
existing A/A proofs.

### Cure (b): opaque genuine producer input — FAIL under frozen spike text

`R45GenuineDiamondSafetyDesignPositive.idr` also defines a test-local
`export record CandidateOpaqueGenuineDiamond` whose constructor is private and
whose contents are the base diamond plus safety. This confirms that the opaque
sealing mechanism itself is viable.

The positive boundary probe
`frozenAdjacentConsumesOnlyProjectedBare` shows the problem: the current
adjacent function accepts the wrapper only after
`revealOpaqueGenuineBase`. The body then receives a bare
`LocalRelationalDiamond` and has no route back to the hidden safety.

`R45OpaqueGenuineAdjacentInputNegative.idr` passes the opaque value directly to
the exact frozen argument position. The expected diagnostic is:

```text
Mismatch between: CandidateOpaqueGenuineDiamond ...
and: LocalRelationalDiamond ...
```

Therefore cure (b) can work only if `adjacentSwapSuffixSpike` changes its input
type, which changes the byte-frozen declaration and is prima facie
disqualified.

Fate of R19 under a true narrow opaque-producer cure: its direct public
`MkLocalRelationalDiamond` fixture could no longer enter the adjacent path. The
four genuine producer functions also require conditions (notably distinct
actors for A/A) absent from R19's repeated-same-actor fixture. R19 would need
retirement/replacement or a newly broadened opaque producer. Public bare
constructor use could remain elsewhere, but would be excluded from the adjacent
consumer. This is a larger and less compatible change than cure (a).

### Cure (c): protocol-quantified discipline transport — not opened

The campaign ruling requested cure (c) only if (a)/(b) failed probes. Cure (a)
passes both directions and the construction-site inventory. No protocol-
quantified transport probe was added.

This remains disfavored because `LocalRelationalDiamond` is not protocol-indexed;
a universal discipline transformer would add substantially stronger temporal
machinery than the exact protocol-independent exclusions already owned by
producers. It would also revive the previously rejected transport-machinery
shape rather than retain first-party producer capital.

## 4. Frozen-surface and manifest delta

Machine-readable proposal:
`research-tests/cp5-r21-proposed-manifest-delta.json`.

### Existing frozen surface touched by cure (a)

| Surface | Change |
|---|---|
| `LocalRelationalDiamond` | append one erased `registrationSwapSafety` field; constructor arity changes |
| four `MkLocalRelationalDiamond` producer bodies | supply the branch-specific safety constructor; public types unchanged |
| R19 test constructor body | supply A/A constructor; public type unchanged |
| baseline record-field revision ledger | append revision-21 field entry at landing |

### New surface

- public indexed `RegistrationSwapSafety` family, with the four constructors
  above.

### Explicit non-changes

- `adjacentSwapSuffixSpike` declaration remains exactly 1183 bytes with SHA-256
  `e6d0c2d669355e5b7bef9efea1707f5853c708deb888bafe5770ba40dbd15a41`;
- its argument/result text, body-hole line, and external-order premise do not
  change;
- `AdjacentSwapResult`, `ReplayInvariantBundle`, RAR, and revision-20 map
  surfaces do not change;
- all existing `LocalRelationalDiamond` parameters and fields remain unchanged;
- `src/` and `dgamma.ipkg` remain byte-identical to production baseline
  `34b21c9`;
- CP3 remains blob `2c697e532e83989de8591fa6a4378747c6a501c0`.

`src/DGamma/CP3.idr` contains no reference to `LocalRelationalDiamond`,
`AdjacentSwap`, or CP5. Consequently immutable `confluenceTheorem` references
none of the proposed surfaces. The R16 theorem assembly reaches them only
through research-test pipeline imports.

## 5. Recommendation and implementation band

### Recommendation

**Select cure (a): append one erased indexed registration-swap safety field to
`LocalRelationalDiamond`.**

Implementation order after a separate supervisor authorization:

1. land `RegistrationSwapSafety` and the erased record field;
2. update all four producer constructor bodies and R19 in the same buildable
   unit;
3. preserve the concrete counterexample under a retired test-local bare shape;
4. flip the current bare-projection negative into a positive live projection
   check;
5. update the manifest ledger and frozen scans;
6. prove bundle field 2 by eliminating the retained safety once at the moved
   pair boundary, then use ordinary pointwise suffix transport; and
7. resume fields 3–15 in strict order.

Do not accept target `RegistrationDiscipline` as caller capital. Do not change
the adjacent signature. Do not add a protocol-quantified transport field.

### Honest band

Revision 68's prior upper remainder was 10 shifts, with its lower bound already
exhausted. The newly required frozen landing, historical counterexample
retirement, pair-local discipline transport, and fresh review gate add real
work. The post-design O6 remainder is therefore widened to **4–18
implementation shifts**:

- 1–2 for the reviewed record/producer/manifest landing;
- 2–6 for pair-local and recursive target-discipline transport, including all
  four safety branches; and
- 1–10 for bundle fields 3–15, opaque result assembly, and closure validation.

This is intentionally wider than the prior upper-only remainder and should not
be narrowed until field 2 is constructively closed.

## Status

- counterexample: **constructive and pinned positive + exact negative**;
- R16-chain constructor inventory: **complete, four of four own safety**;
- cure (a): **PASS both directions; recommended**;
- cure (b): **FAIL under byte-frozen adjacent declaration**;
- cure (c): **not opened by ruling**;
- implementation: **not authorized and not started**;
- bundle field 1: **proved at `875cd88`**;
- bundle field 2: **stopped pending revision-21 implementation authorization**;
- fields 3–15 and final assembly: **unopened**;
- holes: **20**, split **6/4/8/1/1**.
