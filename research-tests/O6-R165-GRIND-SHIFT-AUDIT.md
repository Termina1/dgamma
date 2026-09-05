# O6 R165 — EXEMPT-LADVANCE landed; enrichment advanced; alignment 3/3 stop

## Baseline, scope, and stopping rule

Started 2026-09-05 15:57:48 +0200 on `cp5-thm73-scoping` at exact short HEAD
`dc6fce6`. Initial `git status --short` contained only the permitted untracked
`paper/` and `review-o6-body-adversarial.md`. Idris 2 reports version **0.8.0**.
`idris2 --help` verified both `--source-dir <dir>` and `--check` before the first
check. R164, R162, R161 audits and the R146 strategy memo were read first; the
five specified R163 wall-crack diffs were studied.

Proof-source changes are confined to
`research/DGamma/CP5ConfluenceDeletionChainSpike.idr`. Production `src/` and
`dgamma.ipkg` remain byte-identical to `34b21c9`; LocalDiamond is unchanged.
This audit is the only other changed file. No README/NOTES or package/API edits,
no O14/O17/O19 bodies, no O21 withdrawal work, and no semantic route change.

**STOP:** micro-unit B26 `scopedNamedAlignedAt` failed its third check at
17:13:59 +0200. Its entire declaration was immediately restored away; proof
work stopped at checked commit **`1170c73`**. No attempt budget was reset and no
post-stop proof edits were made. This is an elaboration stop, not a semantic
counterexample or proof of structural impossibility. The R146 route-B stop
condition was not met. O9/O10/O11 were not opened.

All checks used the seeded package interfaces and one Idris process at a time.
The check wrapper inspected runtime processes before each invocation and would
terminate an orphan (none was found) or block on another owned Idris process.
Fresh source checks were forced by touching the individual source's mtime;
**no build directory or TTC/TTM file was deleted**, and no from-scratch rebuild
was run. No standalone probe module was compiled. Temporary source snippets
used to assemble declarations were outside the repository and were removed at
the gate; the failed B26 has no source or compiled declaration residue after
the successful fresh DeletionChain gate check.

## Unit A — complete

The supervisor was asked to resolve the single-with placement before proof
attempts. The recorded reply was:

> PLACEMENT RULING: YES — your proposed placement is within the exemption, and
> it is in fact the BETTER reading of it. The exemption's substance is "at most
> ONE with-block, no nesting, for the LAdvance conversion wall"; it was never a
> requirement that the with live lexically inside the root theorem. Structure
> approved as proposed: ordinary no-with observed-value workers for
> lookup/lifecycle/capability/target, the single EXEMPT-LADVANCE with-block on
> runStepEffect in one top-level resolved-reloading worker (all implicits
> explicit, EXEMPT-LADVANCE comment citing the R164 audit on THAT worker), and
> the exact root theorem wrapping the worker with no with.

`scopedAdvancePreservesUnretired` proves precisely the requested implication:

```text
applyAction (LAdvance child) before = Just (tag, afterState) ->
ScopedUnretiredFiberAt ... child before ->
ScopedUnretiredFiberAt ... child afterState
```

The ONE exempt block is in `scopedAdvanceResolvedUnretired` (`e43636f`), with
scrutinee `runStepEffect step capability (MkLocalState ambient normalizedTable)`
(the source inlines the normalization, with no let alias). Its inputs, universe
parameters, component, table, capability and program are explicit top-level
arguments. It matches `Left failure` / `Right (localAfter, undo)` only; there is
no nesting, dotted pattern, or forcing of an erased existential index. The
worker carries the required `EXEMPT-LADVANCE` comment citing the R164 audit.
The exact root theorem is at `ddba554`, with no with-block.

Concrete raw-outcome equation producers (`scopedAdvanceRaisedRaw`,
`scopedAdvanceDivertedRaw`, `scopedAdvanceFinishedRaw`,
`scopedAdvanceIteratedRaw`) prove an explicit successful evaluator equation
first. Determinism composes it with the supplied equation, and
`scopedUnretiredAfterRuntimeReplace` transports the endpoint lookup. This avoids
conversion of two stuck let-containing cases. Empty continuation, missing
capability, and impossible lifecycles are separate ordinary workers.

A1–A12: **12 immediately checked commits, 14 invocations**. The exempt worker
and root each passed 1/3; A8 and A10 each passed 2/3 after a source-generation
newline error and clause-arity error respectively. Every invocation added only
one new top-level declaration. No other new with-block was added (lexical
`with (` occurrences go 7 -> 8 across the file).

## Unit B clause map

| Clause | Gate status | Exact retained capital / outstanding producer work |
|---|---|---|
| parent-recovery transport | **COMPLETE, inherited** | `scopedRecoveryStepReflects`, `scopedNoParentRecoverySubsequence`; unchanged R164 capital. |
| child-retirement transport | **COMPLETE** | `ScopedUnretiredNext`, `scopedUnretiredStep`, retained-current-generation contradiction, `scopedChildRetiresBeforeSubsequence` (`af46be7`), `scopedChildRetirementSubsequence` (`0332bd1`). The recursion stops at the *first* source retirement even if the supplied witness names a later one; otherwise it threads source unretired presence and exact currentness. This avoids incorrectly trying to preserve unretiredness through an earlier O-Retire. |
| combined per-step discipline-preserving certificate | **COMPLETE** | `scopedSameActionRegistrationStepDiscipline` (`a36036b`) combines the R163 parent-yield transport with child-retirement transport, launches fresh-fiber/currentness after kept child insertion, and retains root registration rank. It consumes the explicit source checked step, source tail alignment, tail subsequence/tags, and kept-site parent control bridge. |
| subsequence-level discipline transport | **COMPLETE as a certificate consumer** | `GenerationSubsequenceParentControlsPreserved` is a constructor-indexed data family; `scopedRegistrationDisciplineSubsequence` (`3a456d7`) returns **surviving-trace** `RegistrationDiscipline`. Live fold producers do not yet emit this entire bridge family. |
| ready-to-subsequence parallel RuleTag certificate | **COMPLETE conversion capital** | `ScopedTaggedGenerationResult` and its kept/deleted constructors; `scopedTaggedReplayReadyResultAt` (`9411cc2`) eliminates only `ReplayReadyEndsAt`, using its constructor-owned tail readiness rather than independently paired ready/ends patterns. Separately `scopedReadyFinal`, `scopedReadyTrace`, `scopedReadySubsequence`, and `scopedReadySubsequenceTags` (`c16c4a1`) expose the exact canonical trace/subsequence and tags directly from readiness. |
| selected fold-output discipline retention | **SURFACE COMPLETE; producer migration pending** | `ScopedSelectedClosedEpisodeFoldOutput` now takes `protocol` and requires `selectedOutputDiscipline` of the canonical surviving ready trace (`60709f5`). Its existing raw producer `scopedSelectedClosedFoldFromPremises` still returns the old untagged fold; no enriched producer was claimed. |
| post-close fold-output/consumer discipline retention | **OUTPUT CONSTRUCTORS COMPLETE; live fold migration pending** | `ScopedPostCloseSuffixFoldOutput` requires `postCloseOutputDiscipline`; end, kept-prepend and deleted-prepend output constructors all retain it (`775d5e9`). Kept prepend accepts the *survivor-side* head discipline, reindexes only its action by the named action equation, and combines it with surviving tail discipline. It cannot substitute source discipline. The raw `scopedPostCloseSuffixFold` and old deletion assembler are not yet migrated. |
| all folds emit RuleTags and parent-control bridges | **PARTIAL** | Existing tagged output fields and the new exact ready/tag converters are available; selected interior/close, post-close and relational fallback live producers still need constructor-local tag/bridge emission. |
| survivor alignment | **BLOCKED at B26 3/3; failed worker removed** | `ScopedNamedAligned` constructor surface (`1170c73`) remains checked capital. `scopedNamedAlignedAt` failed at the stored checked-proof index (`checkedEq` vs `Refl`). No alignment theorem is claimed. |
| surviving TraceComponentsTotal; quiet/noFailed endpoint transport | **NOT COMPLETED** | Remain producer obligations. |
| final target ReplayInvariantBundle / nextPremises | **NOT COMPLETED** | Final assembler must emit the full bundle. No weaker bundle, caller-chosen target capital, or source-discipline downgrade was introduced; O9 remains untouched rather than consuming under-specified capital. |

The two output record blocks were moved after the new canonical ready-trace
projections to respect Idris declaration order. B23 changes one existing
surface. B24 migrates the connected existing post-close record and its three
existing consumers in one check; it adds **no** new top-level declarations.
This is distinct from the prohibited multi-new-declaration checks in R164.

## O9 / O10 / O11

| Unit | Attempts | Outcome |
|---|---:|---|
| O9 `enrichDeletionChainStepSpike` | 0/3 | Not opened: live producer enrichment and target bundle incomplete. |
| O10 `deleteClosingEpisodesCoreSpike` | 0/3 | Not opened; depends on O9. |
| O11 `assembleClosingFreeAccountingSpike` | 0/3 | Not opened; depends on O10. |

No call to frozen `deletionTheoremProof` was added. No
`NoDependentClosingEpisodeForGeneration` value was cast to the raw predicate.
There is no new hole, postulate, `believe_me`, `assert_total`, `partial`, or let
alias in the retained diff. `%default total` remains in force.

## Micro-unit ledger and fresh-check evidence

Each row's retained commit was preceded by the direct command below, returning
zero, no `Error:` diagnostic, and its own
`Building DGamma.CP5ConfluenceDeletionChainSpike` marker. These are actual
fresh checks, not cached no-op claims. Columns give local check attempts and the
successful check's end time (+0200).

```sh
idris2 --source-dir src --source-dir research --check \
  research/DGamma/CP5ConfluenceDeletionChainSpike.idr
```

| Unit | Declaration / change | Attempts | Commit | Successful check ended |
|---|---|---:|---|---|
| A1 | concrete runtime replacement | 1/3 | `1309f71` | 2026-09-05 16:02:51 +0200 |
| A2 | empty advance preservation | 1/3 | `7f6a71b` | 2026-09-05 16:05:47 +0200 |
| A3 | raised raw equation | 1/3 | `56a1e6c` | 2026-09-05 16:07:07 +0200 |
| A4 | diverted raw equation | 1/3 | `f5a7a1a` | 2026-09-05 16:09:07 +0200 |
| A5 | finished raw equation | 1/3 | `2f6057b` | 2026-09-05 16:09:57 +0200 |
| A6 | iterated raw equation | 1/3 | `79009db` | 2026-09-05 16:10:46 +0200 |
| A7 | matching yielded preservation | 1/3 | `fe9fcaf` | 2026-09-05 16:12:14 +0200 |
| A8 | observed yielded-target dispatch | 2/3 | `6e97ca0` | 2026-09-05 16:14:27 +0200 |
| A9 | EXEMPT-LADVANCE resolved run split | 1/3 | `e43636f` | 2026-09-05 16:15:47 +0200 |
| A10 | observed capability dispatch | 2/3 | `9781c59` | 2026-09-05 16:17:58 +0200 |
| A11 | remaining-program dispatch | 1/3 | `2661af5` | 2026-09-05 16:19:21 +0200 |
| A12 | exact LAdvance root theorem | 1/3 | `ddba554` | 2026-09-05 16:20:40 +0200 |
| B1 | non-retirement/current-stability record | 1/3 | `375ad8f` | 2026-09-05 16:24:22 +0200 |
| B2 | same-owner source-step classification | 1/3 | `5be7e24` | 2026-09-05 16:25:34 +0200 |
| B3 | same-owner index transport | 1/3 | `450e203` | 2026-09-05 16:26:43 +0200 |
| B4 | arbitrary-owner source-step classification | 1/3 | `b363fea` | 2026-09-05 16:27:52 +0200 |
| B5 | aligned checked-head projection | 1/3 | `310573d` | 2026-09-05 16:29:18 +0200 |
| B6 | child-retirement tail projection | 1/3 | `f59da18` | 2026-09-05 16:30:17 +0200 |
| B7 | retained-current-generation deletion contradiction | 1/3 | `f62daa3` | 2026-09-05 16:31:17 +0200 |
| B8 | kept child-retirement step | 1/3 | `3e84c84` | 2026-09-05 16:32:47 +0200 |
| B9 | deleted child-retirement step | 1/3 | `f2db7cc` | 2026-09-05 16:34:04 +0200 |
| B10 | child-retirement subsequence recursion | 1/3 | `af46be7` | 2026-09-05 16:36:04 +0200 |
| B11 | both retirement-provenance alternatives | 1/3 | `0332bd1` | 2026-09-05 16:37:08 +0200 |
| B12 | combined per-step discipline transport | 1/3 | `a36036b` | 2026-09-05 16:39:51 +0200 |
| B13 | parent-controls parallel family | 1/3 | `5c3dbd0` | 2026-09-05 16:41:28 +0200 |
| B14 | surviving discipline recursion / data-family correction | 2/3 | `3a456d7` | 2026-09-05 16:45:45 +0200 |
| B15 | tagged filter output record | 1/3 | `dee4f05` | 2026-09-05 16:48:48 +0200 |
| B16 | tagged deleted prepend | 1/3 | `cae5316` | 2026-09-05 16:50:23 +0200 |
| B17 | tagged kept prepend | 1/3 | `33bb1c5` | 2026-09-05 16:51:29 +0200 |
| B18 | single-ends-elimination ready/tag converter | 1/3 | `9411cc2` | 2026-09-05 16:52:45 +0200 |
| B19 | canonical ready endpoint | 1/3 | `892144e` | 2026-09-05 16:55:43 +0200 |
| B20 | canonical ready trace | 1/3 | `7c6c711` | 2026-09-05 16:56:43 +0200 |
| B21 | canonical ready subsequence | 1/3 | `e65ed99` | 2026-09-05 16:57:55 +0200 |
| B22 | canonical ready tag projection | 1/3 | `c16c4a1` | 2026-09-05 16:59:01 +0200 |
| B23 | selected-output surviving discipline retention | 1/3 | `60709f5` | 2026-09-05 17:02:07 +0200 |
| B24 | post-close output + connected consumer retention | 1/3 | `775d5e9` | 2026-09-05 17:03:56 +0200 |
| B25 | aligned-named constructor surface | 1/3 | `1170c73` | 2026-09-05 17:07:47 +0200 |
| B26 | `scopedNamedAlignedAt` | 3/3 | — | failed; fully removed |

Total implementation invocations: **43** = 37 successful commit-boundary
checks + 6 failed checks. No new proof attempt followed the third B26 failure.
A1–A12 and B1–B22/B25 add one top-level declaration per invocation. B14 also
corrects its already-committed B13 family in the same successful invocation;
it adds only the one new discipline-transport declaration.

## Exact failed-check diagnostics

All disposable failed spellings are absent from the retained source. B13's
first computed-family spelling was replaced by the constructor-indexed data
family, not retained as a compatibility path. The transcripts below quote the
compiler errors verbatim (the repeated pre-existing shadowing warning and
start/end wrapper lines are omitted).

### A8 attempt 1/3

```text
Error: While processing type of scopedAdvanceYieldUnretiredAt. Sorry, I can't find any elaboration which works. All errors:
If ===: When unifying:
    targetMatches (targetFiber (MkFiber component parent retiredFlag table (Reloading (step :: rest) accumulator view)) source) view = observed
and:
    targetMatches (targetFiber (MkFiber component parent retiredFlag table (Reloading (step :: rest) accumulator view)) source) view = True
Mismatch between: observed and True.

DGamma.CP5ConfluenceDeletionChainSpike:18108:53--18108:60
 18104 |   capability localAfter undo found resolved ran True matches afterState tag
 18105 |   notRetired raw =
 18106 |     scopedAdvanceMatchedUnretired name key world error value nameEq keyEq child
 18107 |       ambient source component parent retiredFlag table step rest accumulator view
 18108 |       capability localAfter undo found resolved ran matches afterState tag
                                                             ^^^^^^^

If ~=~: When unifying:
    targetMatches (targetFiber (MkFiber component parent retiredFlag table (Reloading (step :: rest) accumulator view)) source) view = observed
and:
    targetMatches (targetFiber (MkFiber component parent retiredFlag table (Reloading (step :: rest) accumulator view)) source) view = True
Mismatch between: observed and True.

DGamma.CP5ConfluenceDeletionChainSpike:18108:53--18108:60
 18104 |   capability localAfter undo found resolved ran True matches afterState tag
 18105 |   notRetired raw =
 18106 |     scopedAdvanceMatchedUnretired name key world error value nameEq keyEq child
 18107 |       ambient source component parent retiredFlag table step rest accumulator view
 18108 |       capability localAfter undo found resolved ran matches afterState tag
                                                             ^^^^^^^

Error: No type declaration for DGamma.CP5ConfluenceDeletionChainSpike.scopedAdvanceYieldUnretiredAt.

DGamma.CP5ConfluenceDeletionChainSpike:18110:1--18124:13
 18110 | scopedAdvanceYieldUnretiredAt name key world error value nameEq keyEq child
 18111 |   ambient source component parent retiredFlag table step rest accumulator view
 18112 |   capability localAfter undo found resolved ran False matches afterState tag
 18113 |   notRetired raw =
 18114 |     scopedUnretiredAfterRuntimeReplace name key world error value nameEq child
 18115 |       (MkSystemState ambient source) afterState tag LDivertTag component parent
Did you mean any of: scopedAdvanceEmptyUnretiredAt, or scopedAdvanceMatchedUnretired?
```

### A10 attempt 1/3

```text
Error: Patterns for scopedAdvanceCapabilityUnretiredAt have differing numbers of arguments.

DGamma.CP5ConfluenceDeletionChainSpike:18224:1--18228:54
 18224 | scopedAdvanceCapabilityUnretiredAt name key world error value nameEq keyEq child
 18225 |   ambient source component parent retiredFlag table step rest accumulator view
 18226 |   Nothing found resolved afterState tag notRetired =
 18227 |     rewrite found in rewrite resolved in
 18228 |       (\equation => void (nothingIsNotJust equation))
```

### B14 attempt 1/3

```text
Error: While processing right hand side of scopedRegistrationDisciplineSubsequence. When unifying:
    GenerationSubsequenceParentControlsPreserved name key world error value nameEq deletable ordinal live originalFirst originalFinal survivingFirst survivingFinal (MoreTransitions sourceStep sourceRest) survivorTrace (DeleteGenerationAction sourceStep sourceRest deleted tail)
and:
    GenerationSubsequenceParentControlsPreserved name key world error value nameEq deletable (S ordinal) (advanceGenerationEnvironment ordinal (transitionAction sourceStep) live) middle originalFinal survivingFirst survivingFinal sourceRest survivorTrace tail
Mismatch between: originalFirst and middle (implicitly bound at DGamma.CP5ConfluenceDeletionChainSpike:18977:4--18977:30).

DGamma.CP5ConfluenceDeletionChainSpike:18981:62--18981:69
 18977 |   (RegistrationDisciplineStep _ _ headDiscipline tailDiscipline) =
 18978 |     scopedRegistrationDisciplineSubsequence name key world error value protocol
 18979 |       nameEq keyEq registered deletable retireOwned insertFresh (S ordinal)
 18980 |       (advanceGenerationEnvironment @{nameEq} ordinal (transitionAction sourceStep)
 18981 |         live) _ _ _ _ sourceRest survivorTrace tail tailTags bridges
                                                                      ^^^^^^^
```

### B26 attempt 1/3

```text
Error: While processing right hand side of scopedNamedAlignedAt. When unifying:
    checkedEq
and:
    Refl
Mismatch between: checkedEq and Refl.

DGamma.CP5ConfluenceDeletionChainSpike:19380:32--19380:77
 19376 |     rewrite checkedEq in
 19377 |       (\fires => replace
 19378 |         {p = \observedNamed => ScopedNamedAligned name key world error value
 19379 |           nameEq keyEq action before observedNamed}
 19380 |         (justInjective fires) (MkScopedNamedAligned afterState tag checkedEq))
                                        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
```

### B26 attempt 2/3

```text
Error: While processing right hand side of scopedNamedAlignedAt. When unifying:
    Just (MkNamedTransition afterState tag (Fired nameEq keyEq action tag checkedEq) Refl) = Just (MkNamedTransition afterState tag (Fired nameEq keyEq action tag checkedEq) Refl)
and:
    with block in fireNamed error world key value name before action keyEq nameEq (Just (tag, afterState)) = Just (MkNamedTransition afterState tag (Fired nameEq keyEq action tag checkedEq) Refl)
Mismatch between: checkedEq and Refl.

DGamma.CP5ConfluenceDeletionChainSpike:19386:35--19386:39
 19382 |         (trans
 19383 |           (sym (the (fireNamed nameEq keyEq action before =
 19384 |             Just (MkNamedTransition afterState tag
 19385 |               (Fired nameEq keyEq action tag checkedEq) Refl))
 19386 |             (rewrite checkedEq in Refl))) fires))
                                           ^^^^
```

### B26 attempt 3/3

```text
Error: While processing left hand side of scopedNamedAlignedAt. Can't solve constraint between: case applyAction ?action ?before of
  { Nothing => Nothing
  ; Just (tag, afterState) => if registryWellFormed afterState then Just (tag, afterState) else Nothing
  } and Nothing.

DGamma.CP5ConfluenceDeletionChainSpike:19371:1--19372:27
 19371 | scopedNamedAlignedAt name key world error value nameEq keyEq action before
 19372 |   Nothing Refl named fires = void (nothingIsNotJust fires)
```

### Alignment wall diagnosis and owner decision

`fireNamed` is frozen and internally uses `with (checkedApplyAction ...) proof
checked`; the successful result stores that particular checked proof in its
`Fired` constructor. Rewriting an independently observed evaluator equation
makes the generated branch carry `Refl`, whereas the attempted
`ScopedNamedAligned` constructor is indexed by the caller's `checkedEq`.
Even the explicitly typed concrete firing-equation attempt fails this
conversion. Pattern-matching the equality itself cannot unify the stuck
`checkedApplyAction` with `Nothing`.

This is **not** evidence that alignment is false or that route B fails. The
next owner decision should choose a genuinely different constructor-owned
firing view/proof transport, or a separately authorized narrow elimination
exemption. Reusing the Unit A exemption for this worker was not permitted and
was not attempted. No unchecked equality-proof irrelevance assumption was
introduced. B26 is parked at its 3/3 budget; the current shift stands down.

## Gate validation

Checks below were sequential and used the existing 207-module seed. Target
research/fixture mtimes were touched rather than removing compiled files.

```text
START 2026-09-05 17:15:21 +0200 idris2 --source-dir src --source-dir research --check research/DGamma/CP5ConfluenceDeletionChainSpike.idr
EXIT 0 END 2026-09-05 17:16:00 +0200

START 2026-09-05 17:16:00 +0200 idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R11DeletionCertificateProjectionPositive.idr
EXIT 0 END 2026-09-05 17:16:01 +0200

START 2026-09-05 17:16:01 +0200 idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R11DirectDeletionStepCloneNegative.idr
EXIT 1 END 2026-09-05 17:16:02 +0200

START 2026-09-05 17:18:08 +0200 idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R11DeletionFillerMapCertificateNegative.idr
EXIT 1 END 2026-09-05 17:18:08 +0200

START 2026-09-05 17:18:08 +0200 idris2 --source-dir src --source-dir research --source-dir research-tests --check research-tests/DGamma/R10DeletionStepMapCloneNegative.idr
EXIT 1 END 2026-09-05 17:18:09 +0200

START 2026-09-05 17:16:37 +0200 idris2 --build dgamma.ipkg
EXIT 0 END 2026-09-05 17:16:53 +0200

Negative fixtures rejected for their intended mandatory symbol + diagnostic:
  R11DirectDeletionStepCloneNegative:
    cloneDeletionStepWithAlternateMap; occurrences and alternate
  R11DeletionFillerMapCertificateNegative:
    fillerMapCannotConstructDeletionCertificate; generationSubsequenceSourceOrdinal
  R10DeletionStepMapCloneNegative:
    replaceDeletionStepOccurrenceMap; alternate and step .deletionOccurrenceCorrespondence
```

No new test fixture was added or changed; all three existing rejecting
boundaries remained rejecting, and the existing positive projection fixture
remained accepted. The entire R11 suite was not rerun; these are targeted
regression checks plus the full seeded production package closure.

Frozen surfaces and package evidence:

```text
Package modules: 207 seeded TTC: 207 / 207 missing: []
full definition: 1470 2d01486bf953f11191b758ac3cfb5722d1d02b1a192b6e552adc8a3f58199ecf
statement prefix: 1154 3aae5a9fbc5b14e0411b4a91e557a6f3dc68c9a6282b9ec2b3fc658cec337adf
CP3 2c697e532e83989de8591fa6a4378747c6a501c0
ipkg da0c007ee08c4648e459296eb6f0e72a40e2ac89
production diff exit: 0
LocalDiamond diff exit: 0
staged diff exit: 0
diff --check exit: 0
with-block count before/after: 7 8
added prohibited \bbelieve_me\b : []
added prohibited \bassert_total\b : []
added prohibited ^\s*partial\b : []
added prohibited \?\w+ : []
added prohibited \bdeletionTheoremProof\b : []
added prohibited ^\s*let\b : []
Header contains %default total: True
holes CanonicalSort 2
holes CrossTrace 4
holes DeletionChain 3
holes LocalDiamond 0
holes RenamingComposition 1
review file sha256 61fc23ae4cea4565b442c840be39c41746ecbac73b8c2f73d04f1e3b4f4681e8
research diff stat .../DGamma/CP5ConfluenceDeletionChainSpike.idr     | 1931 ++++++++++++++++++--
 1 file changed, 1787 insertions(+), 144 deletions(-)
```

The full-surface extraction is from `0 adjacentSwapSuffixSpike :` through the
last non-newline byte; it excludes `public export` and the trailing newline.
Two initial local audit-script range mistakes were corrected before the final
asserting SHA check above. No source surface was changed.

`review-o6-body-adversarial.md` was never edited, staged, committed, or removed;
it remains untracked together with `paper/`. The repository has no other
untracked proof/probe files and no staged files at the gate.

## Status

**Fully proved this shift:** the LAdvance unretired-presence theorem; the
first-retirement/current-generation walk; child-retirement provenance
transport; combined per-step and subsequence-level surviving registration
discipline transport; ready-indexed tag conversion with a single endpoint
elimination; canonical ready endpoint/trace/subsequence/tag projections; and
all revised post-close output constructors' surviving discipline retention.

**Partial:** live selected/post-close/relational-fold migration to the enriched
outputs. Selected output discipline is now required by its type, but its live
producer is not migrated. Parent-control bridge and RuleTag producer emission,
survivor alignment/totality, endpoint quiet/no-failure transport, and final
`ReplayInvariantBundle` assembly remain unfinished.

**Merely stated:** the same 10 pre-existing research holes:
CanonicalSort **2** / CrossTrace **4** / DeletionChain **3** / LocalDiamond **0** /
RenamingComposition **1**. Hole delta **0**. O9/O10/O11 remain their original
holes with 0/3 attempts.

**Next, only after the owner gate:** resolve the B26 proof-index wall without
silently extending EXEMPT-LADVANCE; connect live local replayers to the tagged,
control-bridged outputs; derive and retain all target bundle clauses at the
assembler; then open O9, O10, O11 in that order. The substantial checked prefix
remains capital; the stop does not claim a completed deletion chain.
