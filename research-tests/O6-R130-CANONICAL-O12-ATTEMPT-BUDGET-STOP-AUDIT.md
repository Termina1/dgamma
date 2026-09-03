# O6 revision 130: CanonicalSort O12 attempt-budget stop audit

## Scope and coordinate

This grind shift started at the required coordinate
`4ec721878f243192a7fb02d83ff1828a8be73c6f` on branch
`cp5-thm73-scoping`. The worktree contained only the permitted untracked
`paper/` directory and `review-o6-body-adversarial.md`.

The supervisor-ratified O6 closure was treated as immutable. The deferred
adjacent-swap end-to-end test was not reattempted, the private
`MkAdjacentSwapResult` constructor was not exported, and no producer theorem
was added for that result.

## Unit B: R128 coordinate correction

The pending bookkeeping correction was made in
`research-tests/O6-R128-ADJACENT-SUFFIX-SPIKE-CLOSED-AUDIT.md`. The corrected
sentence now records that the successor lemma was committed separately at
`27c1e52`, while the positional producer followed at `065c0d0`. The correction
landed as `a871b09` (`correct adjacent spike commit coordinate`).

The edit used one attempt. Its first post-commit validation command timed out
because an orphaned revision-129 `run-r11-suite.sh --fresh` process was still
compiling `R23CorrectedInternalFixturePositive` at 99% CPU. That inherited
process group was terminated before any retry, restoring the binding one-Idris-
process invariant. A subsequent visible fresh check passed with:

```text
1/1: Building DGamma.CP5ConfluenceLocalDiamondSpike
exit 0; no Error: diagnostic
```

## Unit C: O12 attempt budget

Only the first CanonicalSort hole,
`closingFreeTraceShapeSpike_rhs` (obligation O12), was opened. The candidate
used top-level total helpers to:

1. classify every selected lifecycle occurrence by the existing installed-
   continuation producer;
2. turn a closing continuation into a forbidden located closed episode;
3. turn a surviving installed continuation at a quiet endpoint into an Active
   endpoint;
4. derive the supported actor's last opening from `extractLastOpening`; and
5. prove opening-ordinal uniqueness through an executable first-selected-
   lifecycle ordinal scan.

No second CanonicalSort hole and no other hole class was opened.

The unit's binding three-attempt budget was exhausted:

| Attempt | Result |
|---:|---|
| 1 | Infrastructure failure before Idris invocation: a shell process guard was composed with `&&`/`;` incorrectly, leaving the temporary-output variable unset. No elaborator process ran. |
| 2 | Parser failure: the candidate used bare `prefix` as a binder, but `prefix` is reserved syntax. The binder was renamed without changing the proposed proof. |
| 3 | Elaboration failure. Two occurrence-classification calls needed an explicit proof that `transitionActor (Fired ...) = actionOwner action`; the executable ordinal helper's signature lacked its explicit `name/key/value/world/error` telescope; and `activeImpliesInstalled` is private to `DGamma.CP3`. |

The decisive attempt-3 diagnostics included:

```text
Can't solve constraint between:
  case transitionAction (Fired nameEq keyEq action tag checked) of ...
and actionOwner action.

Can't bind implicit ... value ...

Name DGamma.CP3.activeImpliesInstalled is private.
```

These are elaboration/interface failures, not a proof that O12's statement is
false and not yet a stored-vs-reconstructed existential-index correlation wall.
Nevertheless the three-attempt budget is binding. The complete candidate was
removed, the CanonicalSort source was restored byte-for-byte to the committed
boundary, and no restated route or disposable copy-probe was attempted.

## Retained state and validation

The research-hole census therefore remains **19**, split **6/4/8/0/1**:
CanonicalSort 6, CrossTrace 4, DeletionChain 8, LocalDiamond 0, and
RenamingComposition 1. `THM73-PLAN.md` was not changed because no obligation
class progressed.

The exact seeded package closure passed after deleting only the terminal
`CP4ProgressProof.ttc/.ttm` interfaces:

```text
207/207: Building DGamma.CP4ProgressProof (src/DGamma/CP4ProgressProof.idr)
exit 0; no Error: diagnostic
```

The frozen release and O6 coordinates remained exact:

```text
src/DGamma/CP3.idr blob = 2c697e532e83989de8591fa6a4378747c6a501c0
production diff from 34b21c9 across src/ + dgamma.ipkg = empty
adjacent full definition = 1470 bytes
adjacent full SHA-256 = 2d01486bf953f11191b758ac3cfb5722d1d02b1a192b6e552adc8a3f58199ecf
adjacent statement prefix = 1154 bytes
adjacent statement-prefix SHA-256 = 3aae5a9fbc5b14e0411b4a91e557a6f3dc68c9a6282b9ec2b3fc658cec337adf
```

## Disposition

Per the standing stop rule, the shift ends at this safe committed boundary
rather than opening O14, O15, O16, O17, O18, or any DeletionChain hole. A future
authorized O12 shift should begin by supplying explicit top-level actor-owner
projection and active-to-installed helpers in the research module, plus the
complete telescope for the ordinal scan, before spending its first elaborator
attempt.
