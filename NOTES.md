# Mechanization notes

## Design decisions

### Runtime data and erased specifications

- Forward maps, inverses, accumulators, coeffect values and tables are runtime
  data.
- Algebraic laws and recovery witnesses are quantity `0` fields/arguments.
- `Undo after before`, `Applied before`, `CoeffectApplied before`,
  `Loaded current initial`, `EffectStack current initial`, and
  `RelEffectStack current initial` expose the
  state indices needed for a later linear API without prematurely forcing every
  runtime handle to quantity `1`.
- Idris does not assume function extensionality. Every equality of functions in
  the paper is therefore represented by `Pointwise` equality. This avoids an
  axiom and is the computationally relevant form of the statement.

### Partial coeffect operations

The paper writes partial arrows and says a violated precondition raises an error
and produces no transition. `get`, `setFresh`, `liftOperation`, all yielded
inverses, and `runMediated` therefore use `Maybe`; no partial Idris function is
used. A successful `setFresh` returns an indexed `CoeffectApplied before`, and
`deleteInserted` proves that its inverse recovers the same runtime dependent
map. The erased uniqueness witness is representation proof and deliberately not
part of that equality. The inverse deletes by key, so unrelated later
registrations are retained. `failurePropagates` executable-checks that a failed
mediated stage remains `Nothing`, rather than becoming identity.

### The recursive context

Paper Definition 32 is the negative recursive equation
`Gamma = Gamma × (Gamma -> Gamma) × Sigma`. A literal inductive declaration is
not strictly positive and Idris correctly rejects it. `ContextTower n` and
`GammaInfinityApprox` are explicitly named finite approximations. No claim that
they preserve every finite observation is made, because the paper supplies no
observation semantics for this fixed point. They are executable and total, but
are not Definition 32 itself and do not prove that the unqualified domain
equation has a set-theoretic least fixed point.

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
3. **Definition 24 and Theorem 40 mix partial and monoidal maps.** Operations
   and their inverses are partial, while Section 3.1 originally presents total
   endomorphisms. The revised mechanization uses Kleisli composition for
   `Maybe` in `PartialTransformation`/`PartialEffTransformation`; failures are
   never totalized. This is a faithful explicit interpretation, but the paper
   should have named the partial transformation category.
4. **Theorem 15's “iff” has a quantifier-scope subtlety.** At a fixed origin,
   the yielded inverse is only initially witnessed there. `effectLiftWitnessIff`
   now states and proves that accumulator restoration for all `phi` and probes
   is equivalent to that yielded inverse being uniform against the whole
   forward map. This resolves the mechanization issue but the paper could state
   the scope more explicitly.

## Escape-hatch and hole audit

There are no uses of `believe_me`, `assert_total`, `postulate`, unsafe FFI, or
`%default partial`. Every Idris module has `%default total`.

The following are statement-only `Type`s. They export no value and therefore
cannot silently introduce a proof:

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
- Mechanized the runtime content of every numbered Section 3 definition except
  the literal Definition 32 fixed point, for which the explicitly partial
  `GammaInfinityApprox` is provided and catalogued as a deviation.
- Proved the monoid/tracking/recovery results, witnessed effect composition,
  every field of effect preservation, projection, lifted state recovery,
  the exact Theorem 15 formula/iff, every intermediate LIFO boundary from
  Theorem 16, both clauses of Lemma 18, both equations at every intermediate of
  Theorem 20, arbitrary-permutation recovery (Corollary 21),
  intrinsically unique finite dependent-table set recovery, notification facts,
  table-equivalence laws, and the relational effect-composition/accumulator
  soundness core of Lemma 38.
- Stated the three remaining operation-observational theorems precisely as
  types rather than using axioms. See the audit above.

### Adversarial review

The orchestrating supervisor independently reviewed the repository and then
required a second hardening pass. This worker has no `subagent` tool exposed in
its tool namespace and is also governed by a child-agent instruction forbidding
further delegation, so the requested fresh reviewer process could not be
launched. Adversarial self-review plus the supervisor's independent review found
and fixed:

1. Initially fieldwise Theorem 13 covered only the current-state projection;
   accumulator and lifted-inverse fields were added.
2. The initial Corollary 21 encoding merely represented an undo list and was
   vacuous as a theorem. It was replaced by `Permutation` plus the exact
   `anyPermutationRecovery` proposition over inverses collected at application
   states.
3. The initial Lemma 18(2) statement did not express submonoid inclusion. It was
   replaced by `JointTransformation` and a dependent pair giving a pointwise
   embedding target.
4. Operation independence initially mentioned outcomes only. It was replaced
   with partial generated transformation monoids, commutation up to the suite
   equivalence, and inverse/outcome stability only under foreign generated
   transformations.
5. The supervisor rejected statement-only general independence. Lemma 18(2)
   is now proved by an explicit `JointTransformation` embedding. Theorem 20 is
   proved by `withdrawAcross` induction, including stability of every later
   yielded inverse. Corollary 21 is proved by deriving pairwise commutation of
   the concrete yielded inverses, showing adjacent swaps preserve evaluation,
   and relating every permutation to the independently proved LIFO recovery.
6. A fresh-context adversarial reviewer (run by the supervisor; full report in
   `review-cp1-adversarial.md`) found the following additional issues, all of
   which were addressed:
   - Theorem 20 exposed only the final withdrawal equality. The new
     `theorem20EveryIntermediateProof` quantifies by every prefix split and
     returns both forward factorization and withdrawal; the inverse-stability
     list remains separately proved.
   - Definitions 22/25 admitted duplicate list keys. `CoeffectContext` and
     `CoeffectSpec` now carry erased `UniqueKeys` witnesses.
   - Definition 24 lacked equivalence/partial-inverse laws and a lift witness.
     These are now in `OperationResultsRelated`, `CoeffectOperation`,
     `CoeffectInterface`, and `liftedInverseWitness`.
   - Definitions 27–31 omitted operational recovery, isolated/intercepted set,
     the realm injection, and `InterSpec`; all were added.
   - Lemma 35 and Theorems 40/42 had false weakened statement shapes. Lemma 35
     now includes aligned definedness, outcomes, successors and inverse respect;
     Theorem 40 is restricted by construction to dependent-table lifts; Theorem
     42 now carries the required shared-key commutativity hypothesis and
     operation-occurrence evidence.
   - Executable `runMediated` no longer totalizes failure to identity. It returns
     a partial effect and propagates `Nothing`; an executable regression theorem
     checks this.
   - README's Theorem 10(2) overclaim was fixed by actually proving the
     unconditional `embedTwisted` homomorphism.
   - Theorem 15's exact formula/iff and Theorem 16's intermediate clauses were
     added. Lemma 38 and Definition 32 are now explicitly marked partial rather
     than overclaimed.
7. All source files were scanned for hidden escape hatches and missing
   `%default total`; none were found.

### Validation

`idris2 --build dgamma.ipkg` succeeds with Idris 2 0.8.0 without warnings.

### Deviations / residual work

Checkpoint 1 is buildable. Lemma 35, Theorem 40 and Theorem 42 remain correctly
stated and explicitly unproved; no proof is claimed for them. Definition 32 is
an explicit finite approximation, and Lemma 38 has a proved relational core but
not a transport theorem covering every Section 3.1 declaration. Section 4 work
must not begin until checkpoint approval.

## Status

**Fully proved:** the exact-equality Section 3.1 algebraic core, including the
unconditional twisted homomorphism, exact lifted-undo formula/iff, every LIFO
boundary, both clauses of Theorem 20 at every intermediate, and arbitrary
permutation recovery; intrinsically unique dependent coeffect table recovery
and notifications; observational table equivalence; relational effect
composition and accumulator soundness.

**Partial/deviation:** Definition 32 is represented only by explicitly finite
approximations. Lemma 38's relational composition/stack core is proved, but the
single universal transport claim over every Section 3.1 theorem is not.

**Merely stated:** the three correctly shaped statement-only items listed in the
escape-hatch audit (Lemma 35, Theorem 40, Theorem 42).

**Next:** after checkpoint approval, encode Section 4's fiber registry and ten
rules as an indexed transition family, then prove preservation and the tractable
temporal/spatial lemmas before stating any remaining global trace obligations.
