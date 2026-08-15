# Checkpoint 1 adversarial review

**Target:** commit `7a80dfb659fa364abe77aa6c198e8496fc509ed7`  
**Scope:** paper Sections 3.1–3.3 (Definitions 1–42 as applicable, with particular attention to Definitions 1–37 and Theorems/Lemmas through Corollary 21)  
**Review mode:** adversarial, no source edits

## Validation performed

- Read `paper/cordis-paper.txt` from Section 3.1 through the end of Section 3.3 (paper lines 305–1094).
- Inspected all four files under `src/` and compared them with `README.md` and `NOTES.md`.
- Confirmed that `dgamma.ipkg` lists all four source modules: `DGamma.Core`, `DGamma.Effects`, `DGamma.Coeffects`, and `DGamma.Unified`.
- `idris2 --version`: **Idris 2 0.8.0**.
- `idris2 --build dgamma.ipkg`: **passed** in the working tree.
- Also built a fresh `git archive` of the target commit under `/tmp/dgamma-review-clean`: all four modules rebuilt (`1/4` through `4/4`) and the build passed. Thus the result is not merely stale TTC reuse.
- Scanned source for `believe_me`, `assert_total`, `postulate`, `%default partial`, `%default covering`, unsafe/foreign primitives, and named holes. None were found. Every source module has `%default total`.

## Findings

### BLOCKER — Theorem 42 drops the theorem's essential hypothesis and is false

**Files:** `src/DGamma/Unified.idr:413-421`, `README.md:79-80`, `NOTES.md:140-141`

The paper's Theorem 42 assumes that every key at which operations of both mediated effects occur is commutative. `MediatedIndependenceTheorem` has no premise about keys, operation occurrence, or commutativity at all:

```idris
(left, right : Mediated suite) ->
Independent (runMediated suite left) (runMediated suite right)
```

This is not a precise statement of Theorem 42. It claims that every two programs over every operation suite are independent. A concrete counterexample is a suite on `List Bool` with two valid revertible operations that prepend `False` and prepend `True`, each undone by `tail`. The forward maps do not commute (`[False, True]` versus `[True, False]`), so the displayed type cannot be inhabited for that suite. Marking it statement-only avoids an axiom, but does not make it the paper's theorem. The comments saying “stated precisely” and NOTES saying the statement-only theorems are “precisely stated” are false.

### BLOCKER — Definition 39 / Theorem 40 do not model keyed lifts, and the theorem type is false

**Files:** `src/DGamma/Unified.idr:344-392`, `README.md:77-78`, `NOTES.md:151-152`

There are several independent defects:

1. `KeyedOperationSuite` merely tags arbitrary homogeneous whole-state operations with a key. It does not encode a dependent coeffect table or prove that an operation reads/writes only its tagged key. The paper's proof of Theorem 40 depends exactly on that confinement.
2. Consequently, two noncommuting whole-state operations can be tagged with distinct keys, satisfying the Idris theorem's key-inequality premise while violating its conclusion. The prepend-`False`/prepend-`True` example above is again a counterexample.
3. The `eq : Equivalence value` parameter of `OperationsIndependent` is completely unused. `liftedEffectsIndependent` uses the exact-equality `Independent` record from Section 3.1, even though the paper explicitly reads commutation up to `≃` in Section 3.3.
4. `outcomesStableLeft` and `outcomesStableRight` quantify over an arbitrary `moved : value`; they never require `moved` to be obtained by a foreign transformation `g ∈ M(a')`. This is not Equation (35). It is an unrelated and generally much stronger condition. Even genuine operations on disjoint slots can fail it when the arbitrary `moved` changes the operation's own slot.

Therefore `distinctKeysIndependent` is not an honest precise statement of Theorem 40, and `OperationsIndependent` is not Definition 39.

### MAJOR — `outOfLIFOProof` proves a weakened endpoint theorem, not paper Theorem 20

**Files:** `src/DGamma/Effects.idr:598-716`, `README.md:58`, `NOTES.md:98-99,125-128,153-154`

Paper Theorem 20(1) quantifies over **every** `u` with `j ≤ u ≤ n` and proves both

- `δ_u = f_j(δ'_u)`, and
- `g_j(δ_u) = δ'_u`.

`outOfLIFOTheorem` exposes only the second equality at the final endpoint `u = n`. It never states the forward factorization `δ_u = f_j(δ'_u)`, and it has no quantifier or indexed trace representing every intermediate `u`. Its second field does correctly align the later yielded inverse functions, corresponding to Theorem 20(2).

`withdrawAcross` uses forward commutation internally, but its result type still omits the missing factorization and intermediate-state family. Thus the README claim that Theorem 20 is proved, and the source comment “including both conclusions,” overstate the result.

### MAJOR — Lemma 35's statement-only types are not the paper's universal property

**Files:** `src/DGamma/Unified.idr:299-342`, `README.md:73`, `NOTES.md:53-58,80-86,102-103,140-141`

`OperationsRespectIndistinguishability` only relates the two yielded inverse maps at the **same** input `x` (`Indistinguishable (undoL x) (undoR x)`). It does not state that each yielded inverse carries arbitrary indistinguishable inputs to indistinguishable outputs, which is part of operation respect in Definitions 24/37 and is used in the paper's proof.

`CoarsestRespectedEquivalence` is more seriously malformed: `SuccessorAgreement` checks only aligned definedness and related successors. It omits equal outcomes and all inverse-respect obligations from the premise “every operation respects the equivalence.” The resulting proposition is false. For example, let `value = Bool`, let `candidate` be the universal relation, and use one everywhere-defined identity-state operation whose outcome is the current Boolean. The `SuccessorAgreement` premise holds, but the one-step tests distinguish `False` and `True` by their outcomes.

The holes themselves are catalogued, but the repeated claim that their *types* are exact/precise is not honest.

### MAJOR — Definition 24 omits required observational laws and partial inverses

**Files:** `src/DGamma/Coeffects.idr:83-113`, `src/DGamma/Unified.idr:257-290`, `README.md:62,72`

Paper Definition 24 packages a value type, an equivalence, and a set of operations, and requires each operation to respect that equivalence: aligned definedness, related successors, relation-respecting/related inverses, and equal outcomes. `CoeffectOperation` has no equivalence parameter and no respect fields. `OperationSuite` likewise has no connection to `CoeffectOperation` or its recovery witness.

The paper's operation and yielded inverse are partial. Here a successful operation returns a total `value -> value` inverse. `runTest` can fail when selecting the inverse at its origin, but once selected the inverse application itself can never be undefined. This changes the observer language in Definition 34.

Finally, `liftOperation` returns a raw triple and exports no proof that its first two fields form the witnessed lifted effect required by Definition 24. These are substantive missing parts, not merely presentation differences.

### MAJOR — Definitions 27–31 are incomplete; `Realisation` is vacuous

**Files:** `src/DGamma/Coeffects.idr:174-176,198-226,251-279`, `README.md:65-69`, `NOTES.md:94-95`

- Definition 27 is reduced to the unused enum `InPlace | Derived`. It encodes none of the paper's semantic content: aliasing/mutation and inverse execution for in-place realization, or preservation of the input, fresh derivation, identity inverse, and discard recovery for derived realization.
- Definition 29 requires isolated `get`, `set`, and `isolate`; there is no isolated `set` effect or its inverse.
- `IsoContext.baseRealm : key -> realm` does not enforce the paper's `R ⊇ K`/self-realm convention and may collapse unrelated keys by default.
- Definition 30 includes both `Σ_inter` and the interception specification `D_inter`; no `D_inter` type is defined.
- Definition 31 requires intercepted `get`, `set`, and `intercept`; there is no intercepted `set` effect or its inverse.

The README rows selectively list the functions that exist while presenting the numbered definitions as executable, and NOTES nevertheless claims every numbered Section 3 definition was mechanized. That correspondence is materially incomplete.

### MAJOR — Definition 32 is an unproved finite approximation, not `Γ∞`

**Files:** `src/DGamma/Unified.idr:10-49`, `README.md:70`, `NOTES.md:27-35,49-52,94-95`

`ContextTower n` is not the fixed point `μΓ. Γ × (Γ → Γ) × Σ`. It is a family of finite types with a special base `(base, coeffects)` and no self-similar type on which the paper's `effect` maps the context to itself. The source claim that it preserves “every finite observation” has no observation semantics or proof behind it.

The non-strict-positivity problem is correctly disclosed, so this is not a hidden escape hatch. It is nevertheless a partial replacement for Definition 32 and should not be counted as full mechanization.

### MAJOR — The coeffect “partial function” type admits duplicate keys

**Files:** `src/DGamma/Coeffects.idr:10-47,115-120`, `src/DGamma/Unified.idr:57-64`, `README.md:60,63`

`CoeffectContext` is definitionally an unrestricted `List (Binding key value)`, with public `Bind` and `insertBinding`. No uniqueness invariant is carried by the type. `lookupBinding`, deletion, and `TableRelated` observe only the first occurrence. Thus the runtime type includes states that are not finite partial functions as required by Definition 22, and the claimed domain/value relation of Definition 33 is faithful only under an unstated, unenforced invariant.

`CoeffectSpec` similarly claims to be a duplicate-free set but is an unrestricted list; the comment defers well-formedness to a Section 4 calculus that is not present in this checkpoint.

### MAJOR — Lemma 38 is only partially mechanized

**Files:** `src/DGamma/Unified.idr:187-255`, `README.md:76`, `NOTES.md:41-45,146-149`

Paper Lemma 38 says **every equality of states asserted in Section 3.1** carries over with `=` replaced by `≃`, and also gives accumulator respect. The code proves relational effect composition and a relational stack soundness invariant. It does not provide relational counterparts of all relevant tracking/recovery/lifting/out-of-LIFO/permutation claims, nor a relational version of `Independent`/commutation for Definitions 19–21. This is a useful core, but not the stated scope of Lemma 38.

### MAJOR — Theorems 15 and 16 are incomplete

**Files:** `src/DGamma/Effects.idr:298-337,821-835`, `README.md:52-53`, `NOTES.md:65-70,146-149`

For Theorem 15, the code proves underlying-current recovery and recovery-target preservation. It does not state the paper's exact full result
`g'(Δ) = (γ, φ ∘ g ∘ f)`, nor the accumulator-restoration iff. NOTES acknowledges the iff omission, but the exact accumulator formula is also absent.

For Theorem 16, `EffectStack`/`pushStack` establish the soundness invariant for forward application states, and `reverseCollectedRecovery` establishes final LIFO recovery. No theorem states that **each individual revert** recovers its own application state and that **every intermediate revert state** satisfies the invariant. The final endpoint theorem is weaker than the two-clause paper theorem.

### MAJOR — Theorem 10(2)'s homomorphism is missing and README points to the wrong theorem

**Files:** `src/DGamma/Effects.idr:156-224`, `README.md:47-48`

The paper's Theorem 10(2) proves that the assignment from every twisted pair `(f,g)` to `λγ.(f γ,g)` preserves unit and multiplication. No exported theorem states that preservation. `fromTwistedStar` instead requires the additional `UniformInverse` premise and proves witnessed membership (paper Theorem 11(2)); it is not a proof of the unconditional monoid homomorphism in Theorem 10(2). The README lists it under both theorem rows and therefore overclaims Theorem 10.

### MAJOR — Failure totalization is broader than NOTES admits

**Files:** `src/DGamma/Unified.idr:351-359,402-411`, `NOTES.md:59-64`

NOTES says failure is totalized to identity “only inside the *statement* of operation independence.” `runMediated` also turns an operation failure into `(x, id)` in the executable interpreter, silently converting an undefined mediated computation into successful no-op termination. Paper Definition 41 constructs mediated effects from partial operations; it does not prescribe this behavior. The documented deviation is therefore incomplete.

### NOTE — `diamondDoesNotEnlargeProof` does substantively prove Lemma 18(2)

**Files:** `src/DGamma/Effects.idr:390-458`

Within the mechanization's syntactic generated-monoid representation, this proof is non-vacuous and matches the paper: every identity/generator/composite in `M(left ⋄ right)` receives a pointwise-equal representative in the submonoid generated by `M(left)` and `M(right)`. The yielded inverse case uses the right inverse at the original state followed by the left inverse at the intermediate state, as required.

### NOTE — `anyPermutationRecoveryProof` substantively proves Corollary 21 (exact-equality version)

**Files:** `src/DGamma/Effects.idr:718-857`

The permutation relation is generated by adjacent swaps; collected inverses are exactly those yielded at original application states; pairwise `Independent` supplies global commutation of those concrete inverse functions; and the proof connects any permutation to independently proved reverse/LIFO recovery. I found no weakening in this particular endpoint theorem. The missing up-to-`≃` transport belongs to the incomplete Lemma 38 layer, not to the exact Section 3.1 corollary.

### NOTE — No hidden compiler escape hatch found; statement-only declarations still do not count as proofs

**Files:** all `src/DGamma/*.idr`, `NOTES.md:72-86`, `dgamma.ipkg:9-12`

The syntactic escape-hatch audit is accurate: no unsafe proof primitive or partiality override was found, and quantity-0 use is ordinary proof erasure rather than an observed cast. Lemma 35, Theorem 40, and Theorem 42 are indeed catalogued as statement-only. However, a build only checks that these type synonyms are well formed; it does not attest that they are inhabited, true, or faithful to the paper. As shown above, the Theorem 40/42 types and one Lemma 35 type admit concrete countermodels.

## Residual risks

- There are no executable examples or tests in this checkpoint that instantiate the abstract interfaces and would expose the false Theorem 40/42 statement shapes or duplicate-table states.
- Exact-equality Section 3.1 is substantially stronger than the later up-to-observation layer; because relational independence is absent, the central claim that observational quotienting supplies effect independence remains unmechanized.
- The clean build attests typechecking only. It cannot validate the semantic correspondence claims in README/NOTES, especially for statement-only `Type` aliases.
- The unresolved fixed-point/domain-theory issue for Definition 32 remains architectural, not a localized proof TODO.

## Final verdict

**REJECT** — the repository builds cleanly and the Lemma 18(2)/Corollary 21 proofs are substantive, but critical correspondence claims are false: Theorem 20 is weakened, Definitions 24 and 27–32 are materially incomplete, Lemma 35 is misstated, Definition 39 is not relational/key-confined, and the statement-only Theorems 40 and 42 are not the paper's theorems and are concretely false.
