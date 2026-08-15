# Mechanization notes

## Design decisions

### Runtime data and erased specifications

- Forward maps, inverses, accumulators, coeffect values and tables are runtime
  data.
- Algebraic laws and recovery witnesses are quantity `0` fields/arguments.
- `Undo after before`, `Applied before`, `Loaded current initial`,
  `EffectStack current initial`, and `RelEffectStack current initial` expose the
  state indices needed for a later linear API without prematurely forcing every
  runtime handle to quantity `1`.
- Idris does not assume function extensionality. Every equality of functions in
  the paper is therefore represented by `Pointwise` equality. This avoids an
  axiom and is the computationally relevant form of the statement.

### Partial coeffect operations

The paper writes partial arrows and says a violated precondition raises an error
and produces no transition. `get`, `setFresh`, and `liftOperation` therefore use
`Maybe`; no partial Idris function is used. A successful `setFresh` returns an
indexed `Applied before`, and `deleteInserted` proves that its inverse recovers
that exact table. The inverse deletes by key, so unrelated later registrations
are retained.

### The recursive context

Paper Definition 32 is the negative recursive equation
`Gamma = Gamma × (Gamma -> Gamma) × Sigma`. A literal inductive declaration is
not strictly positive and Idris correctly rejects it. `ContextTower n` is the
structurally recursive finite tower of `UnifiedLayer`s. Every finite program
observation uses a finite height, so this is executable and total, but it is not
a proof that the paper's unqualified domain equation has a set-theoretic least
fixed point.

### Observational equivalence

A coeffect table relation compares every dependent lookup using the equivalence
for that key. Its reflexive, symmetric and transitive laws are proved via the
indexed `MaybeRelated` family. `RelEffStar` carries both halves of Definition 37:
the effect result is stable on related inputs, and every yielded inverse both
respects the relation and recovers its application state up to that relation.
`relDiamond` and `relPushStack` prove the relational composition/soundness core
of Lemma 38.

## Paper ambiguities / possible errata

1. **Definition 32 is non-strictly-positive.** The recursive variable occurs to
   the left of an arrow. Calling `mu Gamma. Gamma × (Gamma -> Gamma) × Sigma` a
   routine recursive type requires a domain-theoretic solution or a guarded
   encoding not supplied by the paper.
2. **Lemma 35 under-specifies heterogeneous test equality.** Definition 34 lets
   operations have operation-indexed outcome types, but “same outcomes” for a
   word over heterogeneous operations needs an explicit dependent trace type.
   `OperationSuite`, `Observation`, and `runTest` supply one. A remaining proof
   obligation is prefix closure in the presence of state-indexed yielded
   inverses.
3. **Definition 24 and Theorem 40 mix partial and monoidal maps.** Operations are
   partial, while transformation monoids contain total endomorphisms. The paper
   says failures produce no transition. The mechanization totalizes a failed
   operation to the identity only inside the *statement* of operation
   independence; a complete proof must show this matches the intended partial
   transformation category.
4. **Theorem 15's “iff” needs scope clarification.** At a fixed input, the
   yielded inverse is only witnessed at that input. Equality of the lifted
   accumulator for every effect-context input is equivalent to a uniform law
   for that yielded inverse and the whole forward map. The state-recovery and
   soundness-invariant conclusions are proved; the global iff is not yet
   exported as a separate theorem.

## Escape-hatch and hole audit

There are no uses of `believe_me`, `assert_total`, `postulate`, unsafe FFI, or
`%default partial`. Every Idris module has `%default total`.

The following are statement-only `Type`s. They export no value and therefore
cannot silently introduce a proof:

- `diamondDoesNotEnlarge` — Lemma 18(2).
- `outOfLIFOTheorem` — general Theorem 20 (the two-effect core
  `withdrawFirstOfTwo` is proved).
- `anyPermutationRecovery` — Corollary 21.
- `OperationsRespectIndistinguishability` and
  `CoarsestRespectedEquivalence` — Lemma 35.
- `distinctKeysIndependent` — Theorem 40.
- `MediatedIndependenceTheorem` — Theorem 42.

Each is marked `TODO(proof)` at its declaration. These are honest uninhabited
statements, not holes accepted by the compiler.

## Checkpoint 1 — Section 3

### Scope completed

- Read the full extracted paper (`paper/cordis-paper.txt`, 3882 lines).
- Installed Idris 2 0.8.0 through Homebrew and created `dgamma.ipkg`.
- Mechanized every numbered Section 3 definition (Definitions 1–3, 6, 8–9,
  12, 17, 19, 22–34, 36–37, 39, 41) as executable Idris data/functions.
- Proved the monoid/tracking/recovery results, witnessed effect composition,
  every field of effect preservation, projection, lifted state recovery,
  LIFO accumulator soundness, generator commutation, finite dependent-table
  set recovery, notification facts, table-equivalence laws, and relational
  effect composition/soundness.
- Stated the remaining general theorems precisely as types rather than using
  axioms. See the audit above.

### Adversarial review

A fresh subagent reviewer could not be launched because this worker is governed
by a higher-level child-agent restriction forbidding further delegation. An
adversarial self-review was performed instead. It found and fixed:

1. Initially fieldwise Theorem 13 covered only the current-state projection;
   accumulator and lifted-inverse fields were added.
2. The initial Corollary 21 encoding merely represented an undo list and was
   vacuous as a theorem. It was replaced by `Permutation` plus the exact
   `anyPermutationRecovery` proposition over inverses collected at application
   states.
3. The initial Lemma 18(2) statement did not express submonoid inclusion. It was
   replaced by `JointTransformation` and a dependent pair giving a pointwise
   embedding target.
4. Operation independence initially mentioned outcomes only. It now also
   requires Definition 19 independence of the totalized lifted effect maps.
5. All source files were scanned for hidden escape hatches and missing
   `%default total`; none were found.

### Validation

`idris2 --build dgamma.ipkg` succeeds with Idris 2 0.8.0. Warnings concern only
auto-implicit names shadowing field names inside erased local theorem types.

### Deviations / residual work

Checkpoint 1 is buildable but not fully proved relative to every paper theorem:
Lemma 18(2), general Theorem 20, Corollary 21, Lemma 35, Theorem 40 and Theorem
42 remain precisely stated. The reasons are recorded above; no proof is claimed
for them. Section 4 work must not begin until checkpoint approval.

## Status

**Fully proved:** the Section 3 algebraic core through LIFO recovery; dependent
coeffect table recovery and notifications; observational table equivalence;
witnessing, composition, and accumulator soundness up to observational
equivalence.

**Partial:** independence/out-of-LIFO is proved for the two-effect withdrawal
core and generator commutation; the general sequence/permutation induction is
stated. Operation-level observational and distinct-key independence have exact
interfaces and executable interpreters but lack their generic proofs.

**Merely stated:** the six statement-only items listed in the escape-hatch audit.

**Next:** after checkpoint approval, encode Section 4's fiber registry and ten
rules as an indexed transition family, then prove preservation and the tractable
temporal/spatial lemmas before stating any remaining global trace obligations.
