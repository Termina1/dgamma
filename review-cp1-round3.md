# Checkpoint 1 adversarial re-review — round 3

**Target:** `de24a53d979f656a5eca55871bf3b94cffa7612c` (`repair observation and witnessed runtime semantics`)  
**Scope:** paper Sections 3.1–3.3, with every round-2 BLOCKER/MAJOR and the Theorem 42 MINOR rechecked  
**Mode:** independent adversarial review; no source edits or commit

## Validation performed

- Read both previous reports first, then reread paper Sections 3.1–3.3 (`paper/cordis-paper.txt:295-1130`), all five Idris modules, `README.md`, and `NOTES.md`.
- Confirmed `HEAD` is exactly the target commit. The only pre-existing working-tree item before this report was the untracked `paper/` directory.
- `idris2 --version`: **Idris 2 0.8.0**.
- Built a fresh `git archive de24a53` at `/tmp/dgamma-review-round3-clean.MqzPus`. All five package modules rebuilt (`1/5` through `5/5`) and the build **passed**.
- Confirmed every `src/DGamma/*.idr` module is listed in `dgamma.ipkg`, every module has `%default total`, and a corrected literal/anchored scan found no `believe_me`, `assert_total`, postulate, unsafe/FFI primitive, named hole, or partial/covering default.
- Added an external review-only module to the clean archive (not the repository), `Round3Probe.idr`, and typechecked it. It establishes all of the following:
  1. the exact round-2 `L/R/P` hidden-probe model is distinguished by `[YieldedInverseStep op () P]` (`Nothing` from `L`, `Just []` from `R`), hence the old `Indistinguishable L R` proof is now impossible;
  2. the strengthened observer is not vacuous or merely equality: a nontrivial identity-operation suite has two distinct values `VL` and `VR` that remain `Indistinguishable`;
  3. `OperationsRespectIndistinguishability` is inhabited for that nontrivial suite; and
  4. for `Section3Example`, running the captured lifted undos in reverse after `applyActual` reduces to exactly the same `EffectContext` as `reverseActual`.

## Previous-finding disposition

| Round-2 finding | Round-3 disposition | Evidence |
|---|---|---|
| **BLOCKER:** Lemma 35 false under `runTest` via hidden probe | **FIXED by a semantic redesign** | `src/DGamma/Unified.idr:293-412` separates fixed-origin inverse steps (individual map respect) from dynamically yielded inverse steps (pointwise comparison). The external checked `L/R/P` reconstruction is now separated by the old hidden probe. Prefixing an arbitrary continuation after the dynamic step exposes indistinguishability of its results. |
| Lemma 35 redesign might overcorrect into vacuity | **NOT VACUOUS** | The external checked suite has an actual operation, distinct `VL`/`VR`, an inhabitant of `Indistinguishable suite VL VR`, and an inhabitant of the suite's complete first Lemma 35 statement. Reflexive inhabitants also exist for every suite. |
| **MAJOR:** Def 24 lift discarded the recovery witness | **FIXED** | `src/DGamma/Coeffects.idr:332-401` packages `LiftedUndo liftedAfter before` and `liftedUndoValid`; `src/DGamma/Unified.idr:543-561` makes `keyedApply` return `LiftedOperationResult` intact. `runMediated` obtains each stage through this witness-carrying path before composing its executable partial undos (`:704-717`). |
| **MAJOR:** Defs 28–31 admitted duplicate realm maps and total/unindexed set inverses | **FIXED in executable semantics; proof-interface caveat below** | `Assoc` is now the intrinsically unique `CoeffectContext` (`src/DGamma/Coeffects.idr:507-525`). `IsoSetResult`/`InterSetResult` carry partial table undo tokens, with application-state validity proofs (`:555-611`, `:674-712`). `runIsoUndo` rejects a changed realm rather than deleting at the wrong realm (`:567-578`). Isolation/interception now explicitly return derived realizations (`:623-626`, `:725-731`). |
| **MAJOR:** Thm 16 reconstructed a base-state recovery map rather than carrying the live lifted accumulator | **FIXED** | `src/DGamma/Effects.idr:426-504` recursively obtains each forward state and lifted inverse from the same call to `effect`; the inverse is applied to the recursively reverted live `EffectContext`. `reverseActualRecovery` proves current-state and `recover` invariants on this path, and `actualLifoEveryIntermediateProof` ranges over every prefix/suffix boundary. The external concrete equality against captured lifted undos also typechecked. |
| **MAJOR:** no end-to-end two-component load/load/unload/unload example | **FIXED** | `src/DGamma/Section3Example.idr:199-325` defines two components with provisions/requirements and independent-slot effects, checks consumer satisfaction after provider load, executes both loads, runs both captured inverses in reverse, applies both base and actual-lifted recovery theorems, and checks the consumer dependency is absent after final unload. |
| **MINOR:** Thm 42 premise weaker than interface-wide key commutativity | **FIXED** | `src/DGamma/Unified.idr:728-754` defines `keyCommutative` over every pair of operations at the key, including self-pairs. `sharedKeysCommutative` demands that whole-interface property for every key occurring in both programs. |

## Findings

### MINOR — Isolation/interception validity theorems expose only subtable recovery, not full-context recovery

**Files:** `src/DGamma/Coeffects.idr:555-595,674-699`, `README.md:71-73`, `NOTES.md:28-31,187-191`

The executable smart constructors are sound: `isoSet` and `interSet` retain the non-table fields, and their inverses preserve those fields from the later context. The prior wrong-realm and total-undo bugs are gone.

The exported certificates are nevertheless weaker than the phrase “state-indexed witnessed recovery” suggests. `isoUndoValid` proves only equality of `realmBindings`; it exposes no equality/pointwise equality for `defaultRealms` or `realmOverrides`. `interUndoValid` similarly proves only equality of `providerTable`, not the ambient metadata function. Since `MkIsoSetResult` and `MkInterSetResult` are public, their result types themselves permit an `isoAfter`/`interAfter` with unrelated non-table fields as long as a suitable table token is supplied. Thus the smart constructors have the right runtime behavior, but the token types do not intrinsically characterize full `Sigma_iso`/`Sigma_inter` effect recovery as Definition 8 would.

This is **MINOR**, not a reopened MAJOR: no bad state or unchecked total inverse is produced by `isoSet`/`interSet`, and the missing full-state relation can be added without redesigning their runtime algorithms. README/NOTES should either narrow “recovery” to the table projection or expose pointwise/full-context preservation fields.

### NOTE — The Lemma 35 repair deliberately strengthens paper Definition 34

**Files:** `src/DGamma/Unified.idr:293-331`, `NOTES.md:61-70`, `README.md:76-77`

`YieldedInverseStep` is not literally a fixed generator from the paper's monoid word: it chooses the inverse dynamically at the current origin and applies it to a separate probe. That stronger hyper-observation is exactly what closes the paper/prose countermodel, and the deviation is clearly catalogued rather than hidden. The checked distinct-value model shows the stronger relation has not collapsed to equality or emptiness. I found no variant of the probe attack against the revised first statement: forward prefixes expose aligned operation definedness/outcomes/successors, fixed-inverse prefixes expose each yielded map's respect, and dynamic-yield prefixes expose pointwise relatedness of the two yielded maps.

### NOTE — `reverseActualRecovery` is about the actual lifted execution path

**Files:** `src/DGamma/Effects.idr:426-504`

This is not a renamed version of `reverseCollectedRecovery` or `lifoEveryIntermediateProof`. `reverseActual` calls `effect`, retains the exact lifted inverse returned at that application state, recursively carries the live accumulator, and applies that lifted inverse on return. The proof uses `effectInverseProjection`, `liftedInversePreservesRecovery`, and `effectApplicationRecovery`. The external concrete captured-undo equality rules out a merely reconstructed base-state path in the submitted example.

### NOTE — The lifecycle example is now substantive

**Files:** `src/DGamma/Section3Example.idr:199-325`

The example is intentionally a Section-3 model rather than a Section-4 LTS, but it now has the requested two component records, coeffect requirement/provision data, two loads, two concrete inverse applications, satisfaction before consumer load, dependency withdrawal after provider unload, and direct theorem applications. Its coeffect table is a projection of the toy runtime rather than a `setFresh` registration stored directly in `ToyRuntime`; this keeps it lightweight but should not be mistaken for the later reactive scheduler.

### NOTE — Theorem 42 now has the literal interface-wide premise

**Files:** `src/DGamma/Unified.idr:728-765`

The quantification includes all operation pairs at a shared key and self-pairs. `ProgramUsesKey` is existential evidence that a branch contains an operation at the key; because `sharedKeysCommutative` is universal over every such key/evidence pair and demands whole-interface `keyCommutative`, the earlier occurrence-pair weakening is gone.

## Residual risks

- Lemma 35, Theorem 40, and Theorem 42 remain statement-only. Their revised types are materially sounder, but the clean build cannot attest their universal proofs.
- The Lemma 35 observer is a documented strengthening/correction of the paper's literal generator-word language; downstream correspondence should continue to state this deviation explicitly.
- Definition 32 remains an explicitly disclosed finite approximation, and Lemma 38 remains only the relational composition/stack core.
- Isolation/interception token certificates should be strengthened from table equality to a full runtime-context relation, as described in the MINOR finding.
- The example demonstrates the Section-3 lifecycle algebra, not scheduling, notification-driven activation, or the Section-4 transition system.

## Final verdict

I found **no BLOCKER and no MAJOR finding** in round 3. Every round-2 rejection item has received a substantive semantic repair; the remaining issue is a localized proof-interface weakness plus already disclosed statement-only/deviation risk.

ACCEPT
