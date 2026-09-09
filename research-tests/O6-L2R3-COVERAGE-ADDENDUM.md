# L2R3 — owner-authorized A20–A24 coverage addendum

This extends, rather than rewrites, the ratified/read-only-reviewed **4194087e** milestone. Original review: **ACCEPT-WITH-NOTES, no proof blocker**, scoped to that commit. The later declarations below are fresh-checked additions, not retroactively included in that review.

The supervisor explicitly directed use of the five remaining A slots. The precision ruling approved: nonvacuous membership through real root-region/global catalogs; honestly vacuous post-attachment NF at the two empty residual gaps; genuine universal separation only if derivable, otherwise leave it open/conditional. No grammar or separation premise may be weakened. All **A24/B12/C14** slots are now used; no A25/B13/C15 attempt.

## New declarations and exact fresh PASS receipts

| Unit | New declaration | Fresh PASS | Commit | Status |
|---|---|---|---|---|
| A20 | `L2R3FixtureCoverage:emptyGapHasNoOccurrence` | A20-1 | `358f8bf3` | Proved: empty actual occurrence impossible by native decomposition/counts. |
| A21 | `L2R3FixtureCoverage:FixtureCoverage` | A21-2 | `9efd3cb0` | Defined: actual catalog and actual residual-gap NF package, no universal separation field. |
| A22 | `L2R3FixtureCoverage:fixtureCoverage` | A22-1 | `b81a98cf` | Proved: three nonvacuous memberships, selected interval endpoints, both honestly vacuous actual residual NF and residual coverage. |
| A23 | `L2R3FixtureCoverage:NoBundleStraddlesCut` | A23-1 | `10d59dc3` | DEFINED PREDICATE ONLY: precise open all-bundle no-straddling obligation; no inhabitant supplied. |
| A24 | `L2R3Separation:separateBundleObserved` | A24-1 | `138aef3e` | Proved CONDITIONALLY: genuine all-bundle no-straddling entails interval separation using one observed decision. |

## Nonvacuous catalog versus honestly vacuous residual NF

`FixtureCoverage`/`fixtureCoverage` supplies actual `AttachedBundleOccurrence` records:

| Catalog entry | Global trace | Global ordinal | Actual trailing interval |
|---|---|---|---|
| C12 R3 | SAME inherited seven-edge smallTrace | 4 | [4,5) |
| Barrier R3 | Actual eight-edge barrierTrace | 4 | [4,6) |
| Barrier S4 | Actual eight-edge barrierTrace | 5 | [4,6) |

Each entry contains the real located attached block, extended core, checked forced root bundle, actual local occurrence, exact body decomposition/global ordinal link and bounds. R uses actual Remove1/shared True release. Barrier S uses `EarlierForcedRoot Here` after consumed R; the output order is R then S. The C12 member reuses `smallInsertedBundleMember`; R/S members are constructed simultaneously from the SAME `barrierAttachedBlocks` and native one-origin states. This is actual catalog membership, not an action word or an invented release.

The chosen catalog intervals end at the following block's Begin2 cut (5/6), so these actual chosen bundles do not straddle that cut. This is NOT a proof about every possible located bundle of the global trace.

Both actual post-attachment residual gaps are NoTransitions. `emptyGapHasNoOccurrence` proves that a LocatedActionOccurrence in NoTransitions would give S(n)=0 by exact native decomposition plus count-additivity. The two `AttachedNormalForm` callbacks then eliminate such an impossible occurrence. **Their NF is necessarily, honestly VACUOUS.** Residual-head coverage is Unit for these same actual empty gaps and is inhabited as (). These instances are present in the checked `fixtureCoverage` result, indexed by the exact `attachedBetweenBlocks` projections of the original fixture block witnesses, not unrelated empty traces.

To reduce repeated closed dependent elaboration, `FixtureCoverage`'s two gap traces are erased parameters. `fixtureCoverage` instantiates them with the actual physical gaps. No field or actual-gap link is removed; no zero-length assumption is added to the attached grammar or conditional theorem.

**VACUOUS-RISK remains:** an actual finite catalog (including all three displayed concrete births) is not a general universally quantified AttachedNormalForm coverage producer. Empty residual NF does not normalize anything and does not remove the warning. Nonempty pre-attachment root regions cannot at the same time satisfy separation from the bundles that contain them; no gap1/gap2 region is claimed to have zero count.

## Universal separation: exact remaining producer, not an assumed catalog fact

The attempted extension from the catalog to universal separation exposes this missing structural bridge:

> If a cut lies strictly inside the physical interval of ANY authenticated dependent bundle decomposition of the global trace, locate its native bundle transition at that global ordinal. ForcedBundleStep makes that transition root OInsert; actual Begin2 at cut5/cut6 then contradicts it.

The existing interval/count fields and the three catalog members do not supply that **arbitrary-decomposition ordinal-to-transition localization** theorem. A proof limited to selected catalog endpoints cannot establish the existing universal `separated` callback. No false arithmetic/proof-identity replacement was attempted, and no exhausted nested producer was reopened. This remains a proof-development park at the bounded A24 cap, not a claim that universal separation is false.

A23 makes the exact open statement explicit:

```idris
NoBundleStraddlesCut nameEq keyEq global cut =
  (action : Action name key value world error) -> (ordinal : Nat) ->
  (member : AttachedBundleOccurrence name key world error value nameEq keyEq global action ordinal) ->
  LT (bundleOffset member) cut ->
  LT cut (bundleOffset member + transitionCount (memberBundle member)) -> Void
```

The needed actual inhabitants are `NoBundleStraddlesCut %search %search smallTrace 5` and `NoBundleStraddlesCut %search %search barrierTrace 6`. **Neither is produced.** A24 is only the valid conditional next step: observe `isLTE end cut`; Yes gives the left separation branch, No gives cut<end and no-straddling forces cut<=start. It quantifies over a real arbitrary bundle occurrence and consumes the genuine universal no-straddling premise; there is no assertion that a catalog can discharge it.

Accordingly the unchanged `attachedZeroGapInNormalForm` is **NOT presented as unconditionally applied to these fixtures**. Its residual coverage and honestly vacuous NF are now supplied; universal separation remains the explicit missing producer. The earlier direct literal gap0 fixture proofs remain valid independently.

## Independent reviewer P2 repairs

Committed **2e305a79**, artifact-only:

1. Main audit adds the explicit VACUOUS-RISK warning and distinguishes isolated nonvacuous membership from general coverage. The later empty-gap NF instances are explicitly labeled vacuous above and in source docstrings.
2. `O6-L2R3-COMPILER-LEDGER.json.matchingSourceCommitsMeaning` and `run-l2r3-archive.py` now say byte matches—including baseline matches—are independent of PASS/commit authorization. Rejected V0 correctly matches unchanged baseline target bytes; that never made V0 a PASS or authorized its commit.

No raw compiler record/source snapshot or original evidence archive was rewritten. The original archive hash remains `37f154ca9ecefad417d9023b86e6e396748513998208c94bafd8b0ed18ff07a6`.

## Additional copied-definition inventory

- `emptyGapHasNoOccurrence`: new count proof; reuses exact `LocatedActionOccurrence` decomposition (CP3:2102) and `extendedCountAppend` (L2R1 research), not a copied canonical theorem.
- `FixtureCoverage`: new packaging of the existing AttachedBundleOccurrence/AttachedNormalForm types; actual gap indices are erased parameters. No new grammar.
- `fixtureCoverage`: C12 member reuse plus two B8 actual attached-block/bundle constructor instances; does not copy or shrink a general coverage/normal-form theorem.
- `NoBundleStraddlesCut`: new explicit type-level producer obligation matching the existing universal separation quantifier, not a postulate or an inhabited theorem.
- `separateBundleObserved`: new elementary Nat-order implication; generic over every actual bundle, conditional on genuine no-straddling. No reverse coercion, scalar observer over a nested builder, or supplied whole-suffix oracle.

## Addendum attempt/resource/validation evidence

- A20-1 PASS, A21-1 rejected because the fully qualified record accessor omitted the record namespace; A21-2 PASS. A22-1/A23-1/A24-1 PASS. No micro-unit failure3/3.
- All five source commits have their own exact fresh PASS/hash receipt with no intervening compiler invocation.
- Closed fixture catalog/NF elaboration exceeded the <2GiB expectation: maximum A21-2 **5,883,536 KiB (~5.61GiB)**; A22 ~5.30GiB, A23 ~5.09GiB. No ≥19GiB check, no heavy lock, no 18GiB unlocked interruption. Generic A24 is in a separate module to avoid another closed fixture elaboration; A24 ~1.69GiB.
- The separately immutable **ADDENDUM-VALIDATION-PLAN** was committed in2e305a79 BEFORE launching V13/V14. Both fresh-PASS with own Building lines and unchanged current hashes: V13 (FixtureCoverage)5,335,600KiB; V14 (Separation)1,479,536KiB. Original V1–V12 still authenticate their unchanged sources; the original plan is unchanged.
- Original evidence archive remains immutable. The addendum archive/ledger contain all records including A20–A24/V13–V14; separate verification authenticates BOTH original and addendum archives plus both immutable plans and every guarded receipt.

Cumulative totals: **50 source commits / 57 source attempts; 73 compiler invocations = 65 PASS / 8 rejected; 14 current modules freshly checked; 0 interruptions/mutations/heavy locks.** Recorded compiler seconds ~363.21; not elapsed shift duration. No source work after A24.

## Final status and next step

**Checked additions:** real three-entry global catalog and selected interval endpoints; both exact residual-gap coverage/NF instances (honestly vacuous); conditional all-bundle no-straddling→separation lemma.

**Still open:** the actual universal no-straddling-at-Begin2/ordinal-localization producer for both fixtures, general nonvacuous AttachedNormalForm coverage, global release/placement/decomposition normalization, remaining local dispatcher roles, whole R191 replay and global root normalization. No unchanged theorem premise was weakened or secretly supplied.

**Next:** owner/reviewer decides whether to schedule the genuine arbitrary-bundle localization/no-straddling proof in a new bounded shift. No A/B/C cap extension, new source work, production integration or stand-down claim is made without the final owner ruling.
