# Checkpoint 1 adversarial re-review — round 2

**Target:** `c3586e76734e0fda81bab21d752982eaf627d66c` (`harden Section 3 against adversarial review`)  
**Scope:** paper Sections 3.1–3.3, with every prior BLOCKER/MAJOR rechecked  
**Mode:** independent adversarial review; no source changes and no commit

## Validation performed

- Confirmed `HEAD` is exactly `c3586e76734e0fda81bab21d752982eaf627d66c`.
- Read the prior report, the Section 3 paper text, all five Idris modules, `dgamma.ipkg`, `README.md`, and `NOTES.md`.
- `idris2 --version`: **Idris 2 0.8.0**.
- `idris2 --build dgamma.ipkg`: **passed** in the working tree.
- Built a fresh `git archive c3586e7` in `/tmp/dgamma-review-round2-clean.Ple60b`: all five modules rebuilt (`1/5` through `5/5`) and **passed**. The result is not masked by repository TTC artifacts.
- Confirmed that every `src/DGamma/*.idr` module is listed in `dgamma.ipkg`.
- Scanned source for `believe_me`, `assert_total`, `postulate`, unsafe/foreign escapes, named holes, and `%default partial`/`covering`: none found. Every module has `%default total`.
- Independently encoded and typechecked a finite countermodel to the first Lemma 35 statement in the clean archive (`Lemma35Counterexample.idr`). Idris accepted a total function of type `OperationsRespectIndistinguishability suite -> Void`.

## Previous-finding disposition

| Previous BLOCKER/MAJOR | Round-2 disposition | Evidence |
|---|---|---|
| Thm 42 omitted shared-key commutativity and was false | **FIXED as to the old falsity; fidelity caveat remains** | `src/DGamma/Unified.idr:691-720` adds occurrence evidence and same-key `LiftedOperationsIndependent` premises. They are substantive, not vacuous. However this is occurrence-pair independence, weaker than the paper's interface-wide “key is commutative” premise; see MINOR below. |
| Def 39 / Thm 40 allowed arbitrary whole-state operations tagged by distinct keys and was false | **PARTIALLY FIXED** | `src/DGamma/Unified.idr:505-528,633-667` confines Thm 40 to genuine dependent-table lifts, removing the old counterexample. The resulting Thm 40 type appears non-falsifiable. Def 39 still lacks the paper's named key-commutativity predicate and the lifted operation path discards witnessing; see findings. |
| Thm 20 exposed only an endpoint | **FIXED** | `src/DGamma/Effects.idr:722-768` quantifies every prefix split and proves both `delta_u = f_j(delta'_u)` and `g_j(delta_u) = delta'_u`; `:798-849` separately aligns every later yielded inverse. |
| Lemma 35 statement omitted the universal inverse/outcome obligations | **NOT FIXED** | The obligations are now present at `src/DGamma/Unified.idr:341-387`, but the first proposition is false for the actual `runTest` semantics. A total checked countermodel is described under BLOCKER. |
| Def 24 omitted equivalence laws and partial inverses | **PARTIALLY FIXED** | `src/DGamma/Coeffects.idr:204-249` adds genuine partial inverses, recovery witnesses, aligned definedness, successors, outcomes, and inverse respect. But `LiftedOperationResult`/`keyedPartialEff` discard the witness, and `CoeffectInterface` does not independently contain an equivalence for an empty operation set. |
| Defs 27–31 were incomplete/vacuous | **PARTIALLY FIXED** | Recovery constructors and executable isolation/interception APIs now exist, but the isolation realm table again admits duplicate keys, and isolated/intercepted `set` discard indexed recovery evidence and expose total raw inverses. |
| Def 32 finite tower was overclaimed as Gamma-infinity | **FIXED as disclosure; mathematical gap remains** | `src/DGamma/Unified.idr:10-32`, `README.md:73`, and `NOTES.md:31-40` explicitly call it only a finite approximation/deviation. |
| Coeffect table/spec admitted duplicate keys | **FIXED for Defs 22 and 25** | `src/DGamma/Coeffects.idr:24-40,345-360` carries intrinsic erased `UniqueKeys`. A new duplicate-map hole remains specifically in Def 28's `Assoc`. |
| Lemma 38 was overclaimed as full transport | **FIXED as disclosure; theorem remains partial** | `README.md:79` and `NOTES.md:192-194` accurately limit the result to relational composition/stack soundness. |
| Thms 15 and 16 were incomplete | **PARTIALLY FIXED** | Thm 15's exact formula and iff are present at `src/DGamma/Effects.idr:346-394`. Thm 16 still does not model the actual lifted accumulator after each revert; see MAJOR. |
| Thm 10(2) unconditional homomorphism was missing | **FIXED** | `src/DGamma/Effects.idr:218-243` proves unit and multiplication on state and inverse fields without an inverse-law premise. |
| `runMediated` totalized failure to identity | **FIXED** | `src/DGamma/Unified.idr:677-688` returns `Nothing` on either stage failure; `src/DGamma/Section3Example.idr:191-197` checks this by reduction. |

## Findings

### BLOCKER — Lemma 35's new “exact” first statement is false under the mechanized tests

**Files:** `src/DGamma/Unified.idr:293-387`, `README.md:76`, `NOTES.md:58-63,85-86,110-111,177-178,196-197`

The result shape now mentions all Definition-24 obligations, but `runTest` cannot justify the cross-yield inverse obligation in `IndistResultAgreement`. An `InverseStep` fixes one concrete `origin` and therefore uses the **same** yielded inverse in the two test runs (`:313-318`). By contrast, `PartialMapsPreserveIndistinguishability` (`:334-339`) compares the two potentially different inverses yielded when the operation is run at the two indistinguishable starting values. Prefix closure over one common test does not bridge that gap.

A finite total countermodel typechecked against the submitted API:

- values `L`, `R`, `P`; one total operation with constant `Unit` outcome and identity forward state;
- at `L`, it yields an inverse that is identity on `L/R` but undefined on `P`;
- at `R`, it yields an inverse that is identity on all three values;
- at `P`, it yields identity;
- the suite equivalence is exact equality, and the operation satisfies every `CoeffectOperation` field;
- `L` and `R` are `Indistinguishable`: every fixed inverse generator acts identically as far as tests starting from `L/R` can see, and all outcomes agree;
- `P` is indistinguishable from itself, but the inverses yielded at `L` and `R` disagree in definedness on `P`.

Idris accepted a total proof of:

```idris
OperationsRespectIndistinguishability suite -> Void
```

Thus the TODO is not merely difficult; its exported proposition is uninhabitable for a valid `OperationSuite`. The paper's Lemma 35 appears to need a stronger/dynamic test language or weaker inverse-respect conclusion. `NOTES.md` incorrectly calls this only a heterogeneous-prefix proof obligation, and README/NOTES incorrectly call the statements exact/correctly shaped without cataloguing the counterexample.

### MAJOR — Definition 24's executable lift still throws away the recovery witness

**Files:** `src/DGamma/Coeffects.idr:302-343`, `src/DGamma/Unified.idr:518-538`, `README.md:65`

`LiftedOperationResult` contains only `liftedAfter`, a raw partial function, and an outcome. It has no erased field tying `liftedUndo liftedAfter` to the indexed `before`. `liftedInverseWitness` proves a lower-level fact only when supplied the hidden lookup and operation equations separately; `liftOperation` does not package it. `keyedApply` and `keyedPartialEff` then erase even the `before` index and export bare partial effect functions.

Consequently the principal runtime interface used by Defs 39–42 does not intrinsically establish that the first two constituents are the witnessed lifted effect required by paper Def 24. This is especially material under the project's stated plugin-runtime/linear-token design constraint. The local ingredients now exist, but README's “witnessed table lift mechanized” overstates the exported interface.

A smaller completeness defect is at `src/DGamma/Coeffects.idr:251-263`: `CoeffectInterface` has only pairwise equality between operation-carried equivalences. If `OperationCode` is empty, it contains no equivalence at all, so it is not literally the advertised complete triple `(V, ~=, A)`.

### MAJOR — Definitions 28–31 reintroduce invalid map states and non-witnessed/totalized set inverses

**Files:** `src/DGamma/Coeffects.idr:449-521,569-582`, `README.md:69-72`, `NOTES.md:21-29,99-101,153-154`

The base table was hardened with `UniqueKeys`, but isolation's `realmOverrides` is `Assoc key realm = List (key, value)` with a public unrestricted `MkIsoContext`. Duplicate realm entries are therefore representable again. `lookupAssoc` observes only the first, so the purported `K ⇀ R` component of paper Def 28 is not intrinsic.

Moreover `isoSet` and `interSet` unwrap a witnessed `CoeffectApplied` and return a raw **total** function `Context -> Context`, discarding `coeffectUndoValid`. This contradicts both the comments claiming a witnessed/partial set and the paper's partial inverse types. The loss is operationally visible for isolation: after `isoSet k` installs in realm `r`, applying its returned inverse to a later context where `isolate k r'` changed resolution deletes at `r'` (or silently no-ops if absent), leaving the original registration in `r` while still returning a context as if recovery succeeded. A partial inverse should fail there, and an indexed token should at least prove recovery at the actual successor.

`Realisation` itself is no longer a vacuous enum, but `DerivedRealisation parent child` carries no derivation/freshness/identity-inverse invariant, and `isolate`/`intercept` do not return a `Realisation`. The previous omission is therefore improved, not fully repaired.

### MAJOR — Theorem 16 still substitutes a reconstructed base-state recovery map for the actual lifted accumulator

**Files:** `src/DGamma/Effects.idr:255-394,397-413,956-992`, `README.md:56`, `NOTES.md:104-106,165-167,185-190`

`lifoEveryIntermediateProof` proves that undoing each suffix reaches the corresponding **base-state** prefix endpoint. Its second field proves that a freshly reconstructed reverse list of the prefix's originally yielded inverses maps that prefix endpoint to the initial state.

Paper Theorem 16(2), however, concerns every intermediate state of the lifted effect-context trace. A lifted revert changes the actual accumulator by `track(g, f)` (and Theorem 15 explicitly shows the accumulator becomes `phi . g . f`), so after reverting a suffix the live accumulator is not definitionally the reconstructed inverse list for the remaining prefix. `EffectStack` and `pushStack` model applications only; there is no indexed revert transition or sequence theorem carrying the actual accumulator through reverse reverts.

The endpoint/state part is useful and each single-step recovery can be assembled informally from `effectUndoRecovery`, but the submitted `lifoEveryIntermediate` does not state the actual accumulator invariant that README and NOTES claim is proved at every boundary.

### MAJOR — `DGamma.Section3Example` is not the required end-to-end two-component lifecycle example

**Files:** `src/DGamma/Section3Example.idr:31-197`, `README.md:28-29`

The module checks one typed binding/specification, one single-stage toggle program, and one failure. It has:

- no component type or two component values;
- no two independent effects;
- no load/load/unload/unload execution;
- no coeffect interaction between two components; and
- no application of `recoverTracked`, `reverseCollectedRecovery`, `lifoEveryIntermediateProof`, `outOfLIFOProof`, or `anyPermutationRecoveryProof`.

Even the successful mediated example checks only the post-state; it does not apply the returned undo or prove recovery. The new module is non-vacuous as a smoke example, but it does not satisfy the requested end-to-end example and does not stress the interfaces whose soundness is at issue.

### MINOR — Theorem 42's premise is meaningful but is not the paper's exact key-commutativity premise

**Files:** `src/DGamma/Unified.idr:691-720`, `README.md:80,83`

`sharedKeysCommutative` requires `LiftedOperationsIndependent` only for pairs of operations that occur, one in each program, at equal keys. This is a substantive sufficient hypothesis and is not a restatement of whole-program independence. I found no old-style counterexample to the resulting theorem type.

It is nevertheless weaker than the paper's stated premise that every shared key is **commutative**, where Def 39 declares a key commutative when every pair of operations in its whole interface (including self-pairs) is independent. No `KeyCommutative` predicate is defined. The code states a plausible strengthening of the paper theorem (weaker assumptions, same conclusion), but README's “exact shared-key-commutativity hypothesis restored” and the source comment “exact hypothesis” are inaccurate, and the literal paper theorem has not been separately stated.

### MINOR — The repository's own full-paper/readiness statements exceed the checked artifact

**Files:** `NOTES.md:97-101,110-111,177-181,196-201`

The notes say the operation-observational statements are precise/correctly shaped and that runtime content of every numbered Section 3 definition except Def 32 is mechanized. The false Lemma 35 statement, un-witnessed lifted operation interface, and incomplete isolation map/set interface make those status claims too strong. The build validates well-formed declarations, not those semantic assertions.

### NOTE — Theorem 20 hardening is substantive

**Files:** `src/DGamma/Effects.idr:674-849`

The new prefix split is not cosmetic. For every `later = observed ++ remaining`, it exposes the paper's two state equalities at that intermediate prefix, while `outOfLIFOProof` aligns all later inverse maps between original and omitted traces. I found no weakening in this repair.

### NOTE — Failure propagation, unconditional embedding, packaging, and escape-hatch audits pass

**Files:** `src/DGamma/Unified.idr:677-688`, `src/DGamma/Section3Example.idr:191-197`, `src/DGamma/Effects.idr:218-243`, `dgamma.ipkg:8-13`

`runMediated` is genuinely partial, the executable regression checks first-stage failure, `embedTwisted` is unconditional, every source module is in the package, clean rebuilding succeeds, and no hidden compiler escape hatch was found. Statement-only declarations still provide no theorem inhabitants.

## Residual risks

- Lemma 35 requires a semantic redesign, not merely filling the current TODO. Any Section 4 argument relying on observational equivalence being admissible would inherit this defect.
- Theorem 40 and Theorem 42 remain statement-only. Their revised types are materially better, but no checked inhabitant tests the complex partial-map closure argument.
- The Def 24/29/31 runtime paths drop state-indexed recovery evidence exactly where a later linear plugin API would need it.
- Def 32 remains only a finite approximation and Lemma 38 remains partial, although both limitations are now honestly documented.
- The clean build attests typechecking, not paper correspondence; the accepted countermodel demonstrates that a well-formed statement can still be false.

## Final verdict

**REJECT** — the resubmission genuinely fixes Theorem 20, duplicate base tables/specs, the unconditional Theorem 10 homomorphism, old Theorem 40 confinement, and mediated failure propagation. It still contains a typechecked countermodel to the claimed Lemma 35 statement, drops lifted recovery witnesses, leaves isolation/interception set semantics unsoundly total/unindexed, overclaims Theorem 16's accumulator invariant, and lacks the required two-component lifecycle/recovery example.

**VERDICT: REJECT — BLOCKER Lemma 35 is false under `runTest`, with additional MAJOR runtime-interface, Theorem 16, and example gaps.**
