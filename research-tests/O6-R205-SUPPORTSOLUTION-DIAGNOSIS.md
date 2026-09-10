# R205 — CP4SupportSolution resource diagnosis (read-only; proposal only)

## Observed evidence, not a causal claim

Source `src/DGamma/CP4SupportSolution.idr` is **byte-identical to ba880886**,
SHA256 `812d874baff27ce025c17ad09527e285079b6ee26a50fec2c4b231723593fda0`,
1827 lines. Its **pre-unfreeze isolated peak is UNKNOWN**: the retained seeded
builds did not freshly elaborate this source. The historical ~138GiB package
wall is not an authenticated isolated-module measurement.

- S31: isolated64GiB stop, peak67128512KiB,209.255s,exit−15.
- S31-2: isolated128GiB stop, peak134435632KiB,419.813s,exit−15.
- Both produced no flushed native Building lines and no native type diagnostic;
  neither is a proof PASS. No source mutation or foreign overlap occurred.
- S31-3: explicitly gated **FINAL**200GiB attempt,45min wall limit; query-only
  `memory_pressure -Q` plus `vm_stat` every5s. Three consecutive positive deltas
  in Swapouts OR occupied-compressor pages trigger a stop. Historical counter
  totals are baseline, not fresh pressure. Samples/actual result are in the
  invocation ledger/resource audit; no success is predicted here.

## Exhaustive answer to the requested patched-type match inventory

| Patched type/family | Token occurrences in this source | Functions matching it |
|---|---:|---|
| `ActorLifecycleOnly` / `ActorLifecycleCore` | 0 / 0 | **none** |
| `LocatedOpenEpisodeBlock` | 0 | **none** |
| `BlockBefore` | 0 | **none** |
| `CanonicalInputPlacement` | 0 | **none** |
| `OrderedForcedRootBundle` | 0 | **none** |
| `Attached*` names | 0 | **none** |

This was checked against the entire file, not merely exported signatures.
The complete99 type/function declaration inventory is in
`O6-R205-SUPPORTSOLUTION-STATIC-INVENTORY.json`.
Consequently **there is no direct exhaustive match over the new four-constructor
bundle grammar to factor here**. Attributing these measurements to multiplied
bundle-coverage cases would be invented evidence.

The module implements finite support-closure fixedness, soundness, uniqueness
and registration-provenance adapters. Its actual pattern families are the
unchanged lists/Nats/Bool/Dec/Maybe, registry/fiber/parent structures, rank
accessibility and registration discipline. Illustrative nested case sites:

- `listDecEqWith`:362–375 — list/equality decisions;
- `supportFuelLengthStable`:385–449 — finite support fixedness and equality;
- `supportClausePredicateMonotone`:1215–1255 — lookup/Root/ChildOf;
- `candidateIncludedAtAccessibleRank`:1645ff — accessibility/rank argument;
- `registrationStepDisciplineProvenance`:1770–1789 — unchanged Action tags;
- `registrationDisciplineProvenance`:1795–1809 — unchanged discipline spine.

These are **inspection locations, not measured hotspots**. No per-declaration
compiler trace or heap profile was obtained, so there is no justified ranking
of which function consumes the heap.

## Direct CP3 surface actually referenced

Static name intersection finds23 CP3 names, all defined in the unchanged early
support/provenance section (lines14–747), before the first signed edit at1781.
Twenty-two initial declaration blocks compare byte-exact old/new; the23rd name,
`MkSupportWellFoundedResult`, is the constructor inside the unchanged record.
The machine inventory contains coordinates and hashes. This is a static direct
surface check, not an invented complete elaborator call graph.

Names: `listMember`, `PrecedenceAcyclic`, `RegistrationProtocol`,
`RegistrationStepProvenance`, `RegistrationProvenance`,
`RegistrationStepDiscipline`, `RegistrationDiscipline`, `ReachedFromEmpty`,
`providerFromPredicate`, `allList`, `supportClause`, `SupportSolution`,
`providerFromCandidate`, `parentFromCandidate`, `supportCandidate`,
`supportPassEntries`, `supportPass`, `supportFuel`, `isSupported`,
`supportPassEntriesEligible`, `SupportWellFoundedResult`,
`MkSupportWellFoundedResult`, `supportWellFoundedTheorem`.

Indirect compiler-environment effects of importing the enlarged CP3 module are
not excluded, but are **unmeasured**. The direct bundle-match hypothesis is not
supported by the source. No new paper erratum or failed theorem follows from an
RSS stop.

## PROPOSED production repair — only if profiling justifies it; NOT APPLIED

**Do not add an OrderedForcedRootBundle helper or fictional cases to this
module.** There is no such match to repair. No lexical CP3 rename applies here.

If S31-3 cannot complete, the source-preserving engineering candidate for a
SEPARATE production gate is **module decomposition at existing proof seams**,
not a changed theorem or additional premise:

1. Extract the finite support-list/fuel kernel (current lines15–449) to a new
   `DGamma.CP4SupportSolutionFinite` module; preserve all types and bodies.
2. Extract soundness/solution construction (451–1143), and predicate/rank
   uniqueness (1145–1732), into explicitly imported support modules only after
   a declaration dependency inventory determines their exact shared interface.
3. Retain the existing public production entry points
   `supportSolutionUniqueFromRanks`, `supportWellFoundedTheoremProof`,
   `registrationDisciplineProvenance`, `supportWellFoundedUnderDiscipline`
   in `CP4SupportSolution` under their existing public names/statements.
4. Give proof-only cross-module helpers quantity0 deliberately; preserve
   quantities of existing computational helpers. Preserve reducibility only
   where actually needed. DIRECTLY import each defining module in normalization
   consumers (the Idris0.8 binding reduction rule). Do not insert postulates,
   holes, assumed callbacks, `believe_me`, `assert_total`, or weaker premises.
5. The gate must cover exact new module paths, visibility deltas, package module
   list and a full dependent validation plan. This is an architectural/code
   relocation proposal, **not an authorized R205 lexical repair**. Existing
   source uses legacy `with`/`let`; copying/reworking it is not silently exempt
   from R205's no-new-with/no-let-alias repair rule and needs its own scope.

Expected benefit is bounded per-process elaboration context **if retained
module-wide state is the cause**; a single pathological declaration could still
exceed the guard after extraction. Therefore no build or memory improvement is
claimed. Obtain compiler-stage/declaration-cost evidence under a new explicit
gate before choosing exact split boundaries. There is no justified exact source
patch to apply during this no-proof shift, and no fourth S31 attempt is planned.

## Subsequent supervisor-owned pressure recalibration gate

S31-3 stopped at147.61GiB on the conservative compressor-growth rule, not the
200GiB RSS or45min limit. Raw Swapouts stayed flat and query free was97%.
Supervisor explicitly acknowledged pressure-rule miscalibration and authorized
ONE additional S31-4 under a NEW gate:200GiB/60min; stop on two query samples
free<15% OR three rising Swapouts, never compressor counts alone. The earlier
FINAL/no-fourth language above describes the prior gate and is superseded only
by this exact new authority (O6-R205-GATE-LEDGER.json). The static diagnosis and
proposal-only status are unchanged. A pre-unfreeze isolated peak is still unknown.
