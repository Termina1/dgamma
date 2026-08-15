# dgamma

`dgamma` is an executable Idris 2 mechanization of **“A Programming Paradigm for
Spatiotemporal Composability”** (Shi, Zhang, Cui). Runtime functions remain
computational data; laws and witnesses are erased with quantity `0`.

## Build

```sh
idris2 --build dgamma.ipkg
```

The package currently contains the Section 3 checkpoint. Section 4 modules are
added only after checkpoint approval.

## Design map

- `DGamma.Core`: equivalences and state-indexed `Undo after before` /
  `Loaded current initial` handles.
- `DGamma.Effects`: twisted composition, effect contexts, witnessed effect
  functions, tracking/recovery, generated transformation monoids and
  independence.
- `DGamma.Coeffects`: finite dependent coeffect tables, safe `get`/`set`,
  notifications, operations, isolation and interception.
- `DGamma.Unified`: finite context tower, observational equivalence, witnessing
  up to equivalence, operation tests, and coeffect-mediated programs.

`Pointwise` equality is used for functions rather than assuming function
extensionality.

## Paper correspondence

“Stated” means the proposition is present as an Idris `Type`, but no inhabitant
is exported. It is not a postulate and cannot be used as a proof.

| Paper | Idris name | Status |
|---|---|---|
| Def 1 | `DGamma.Effects.Twisted`, `twisted`, `twistedUnit` | proved/executable; monoid laws proved pointwise |
| Def 2 | `EffectContext` | executable |
| Def 3 | `track` | executable |
| Thm 4 | `trackProjection` | proved |
| Thm 5 | `trackUnit*`, `trackComposition*` | proved pointwise |
| Def 6 | `recover` | executable |
| Thm 7 | `recoverTracked` | proved |
| Def 8 | `EffFn`, `EffStar`, `Applied`, `Undo` | executable; witnesses erased |
| Def 9 | `diamond` | executable |
| Thm 10 | `diamondAssociative*`, `diamond*Unit*`, `fromTwistedStar` | proved pointwise |
| Thm 11 | `diamondStar`, `etaStar`, `fromTwistedStar` | proved |
| Def 12 | `effect` | executable |
| Thm 13 | `effectPreservesDiamond*` | proved on every forward/inverse field, pointwise |
| Thm 14 | `effectForwardProjection`, `effectInverseProjection` | proved |
| Thm 15 | `effectUndoCurrent`, `effectUndoRecovery` | recovery conclusions proved; iff/uniform characterization not yet isolated |
| Thm 16 | `EffectStack`, `pushStack` | proved as an indexed sound accumulator |
| Def 17 | `Generator`, `Transformation`, `runTransformation` | executable inductive generated monoid |
| Lem 18(1) | `generatorsSettleCommutation` | proved |
| Lem 18(2) | `diamondDoesNotEnlarge` | stated (`TODO(proof)`) |
| Def 19 | `Independent`, `PairwiseIndependent` | exact executable/proof interface |
| Thm 20 | `withdrawFirstOfTwo`; `outOfLIFOTheorem` | two-effect core proved; general theorem stated |
| Cor 21 | `Permutation`, `anyPermutationRecovery` | precisely stated |
| Def 22 | `Binding`, `CoeffectContext`, `lookupBinding` | executable finite dependent table |
| Def 23 | `get`, `setFresh`, `deleteInserted` | executable; successful set returns proved indexed undo |
| Def 24 | `CoeffectOperation`, `liftOperation` | executable partial operations |
| Def 25 | `CoeffectSpec`, `satisfies` | executable/decidable |
| Def 26 | `Notification`, `notify` | executable; activation/deactivation facts proved |
| Def 27 | `Realisation` | executable classification |
| Def 28 | `IsoContext` | executable |
| Def 29 | `resolveRealm`, `isoGet`, `isolate` | executable derived realization |
| Def 30 | `MetadataMonoid`, `InterContext` | executable; monoid laws erased |
| Def 31 | `interGet`, `intercept` | executable derived realization |
| Def 32 | `UnifiedLayer`, `ContextTower` | executable finite tower; literal fixed point rejected as non-positive |
| Def 33 | `MaybeRelated`, `TableRelated`, `StateRelated` | mechanized; equivalence laws proved |
| Def 34 | `OperationSuite`, `TestStep`, `runTest`, `Indistinguishable` | executable tests |
| Lem 35 | `OperationsRespectIndistinguishability`, `CoarsestRespectedEquivalence` | stated |
| Def 36 | `MapRespects`, `MapsRelated` | mechanized |
| Def 37 | `RelResult`, `RelEffStar`, `fromEffStar` | executable/witnessed |
| Lem 38 | `relDiamond`, `RelEffectStack`, `relPushStack` | proved relational composition and soundness invariant |
| Def 39 | `OperationsIndependent` | mechanized, including lifted effects and outcomes |
| Thm 40 | `distinctKeysIndependent` | stated |
| Def 41 | `Mediated`, `runMediated` | executable dependent continuation tree |
| Thm 42 | `MediatedIndependenceTheorem` | stated |
