# O6 L2R16 audit

## Boundary and authority

First record (printed before integration):

> L2R15 FINAL GATE at a0e50ce0 ACCEPTED (Tier 1 signed handoff); production unfrozen by the owner in R205 (CP3 blob eeaa70aa…, CP3StatementChecks migrated, CanonicalSort re-baselined eb0ab7b9…, sealed at 452420c7); lane 2 released.

Worktree `/Users/vyacheslavshebanov/Work/dgamma-lane2`, branch `cp5-thm73-lane-a8a10`. Initial HEAD `a0e50ce016cc6a05fd8ee453803d975d7fdfa905`, initially clean. No main-tree entry/edit/build/commit occurred. The sole authorized main-tree filesystem read was the build rsync below.

1. Exact production `452420c73c59a6af2d204cafa6e722b3a0fff995` merged cleanly at `28da551de112f123eb5dc8f997945c26b919d281`.
2. Sole full reseed: `rsync -a --delete /Users/vyacheslavshebanov/Work/dgamma/build/ ./build/`. 485 TTCs were recorded and 741 Idris sources backdated to 2025-01-01. There was no cold/package rebuild.
3. Explicit mid-run second-merge authority: V19 `bfe2e8d506f2ca77f2e96086f61ed19cc2bde642`, merged at `b16591547b55dd05f13c1ac95da8f2b69433b50b`. This was an authorized exception to the original one-merge limit, not an unreported rebase.
4. Main-owned `CP5ActorLifecycleOnlyExtended.idr` was freshly checked at V1001, never edited by this lane. Its SHA256 is `8a4230942d52ba11fa7d9a599f3c0683b8d526cf97c01c7eb1720d0d2342ef13`. The valid new main lemma is `actorLifecycleCoreIntoAttached`; the old attached→extended coercion was not silently retained.

Imported main changes are distinguished from lane-owned edits. Protected `src/`, root documents and protected research modules are compared against the authorized V19 boundary. Production `src/` additionally matches `452420c7`. All authorities, before/after trees, merge parents and hashes are archived.

`CP4SupportSolution.ttc` was neither rebuilt nor touched: seeded SHA256 `0572d487cd7d341c091a94b5fa1d6d6685eade50c2b618f38ffc19fca7dce340`, with its seeded mtime preserved. Its historical 160.8 GiB datum was not a permission to rebuild it.

## Closure and repair policy

The original globs selected 193 modules, not at most40. The supervisor clarified that40 was a **repair cap**, not a validation cap; authorized six inherited `research/DGamma/CP5L2R1*.idr` prerequisites plus the main-owned V19 module bring the inventory to200. The early verbal count of seven prerequisites was corrected to the actual six. All six authorized source-copy files were eligible for bounded research repairs; protected production copies were not.

R205 TTCs marked `usableAsImport=false` were not accepted merely because cached files existed. External blockers propagate through non-lane intermediaries. The authoritative state file identifies every exact source hash, latest receipt and blocker/error; UNCHECKED is not PASSED.

Mid-run ruling exempts **qualification-only** CP3/research collisions from the40-module cap. Each such module has at most2 attempts and a separate guarded source commit. Only research namespace prefixes are added; references are never redirected to production by qualification. All other lexical repairs remain capped at40. The module→qualified-names/occurrences table is generated from the raw decisions.

At the completed light boundary: **186/200 fresh green** (97 unchanged, 89 repaired). The89 consisted of84 qualification-only modules,2 EOF cleanups and3 authorized semantic restatements. Every one of those repair checks passed first attempt. Eight long fixture/dependent targets and six externally blocked targets remained. Final counts below supersede this boundary; they do not retroactively relabel it.

## Authorized semantic restatements

- **S1 `fbe4a837`:** retire `L2R3Attached.oldIntoAttached`; introduce genuine `coreIntoAttached` from `ActorLifecycleOnlyExtended` to `ActorLifecycleOnlyAttached` through the existing empty-root-history embedding. No attached→core implication is claimed. No other Idris consumer of `oldIntoAttached` was found.
- **S2 `30f03de5`:** introduce erased specification TYPE `StrictRootBeforeAnyLifecycle`; restate `smallStrictPlacementRejected` against that retired strict clause. The contradiction is unchanged: root3 at ordinal4 would precede actor0's lifecycle at ordinal0. This does not reject the new production placement or consume its own-lifecycle projection.
- **S3:** migrate `BarrierOrderEvidence.strictRejected` to `StrictRootBeforeAnyLifecycle barrierTrace -> Void`; remove only that field's now-unused support-state/order parameters. Same contradiction, no weakened native premise. Exact signature deltas and authority are in the raw records/ledger.

Two known inherited references to the retired main coercion in `L2R1R191Relocation.idr` are not repaired by pretending blockActorOnly supplies Core. Their externally blocked status and exact sites are retained.

## Tier2: actual native different-anchor fixture

The supervisor prioritized this probe before thin production adapters. Seventeen new declarations were retained across T1–T18; **T12 was fully reverted**. All source commits were guarded by exact passing source hashes, one own-target Building line and no intervening compiler invocation.

- T1/T2: two independent provision-key components and literal operation-built snapshots. Nat selectors are total fixture accessors; fallback indices assert no additional transition.
- T3 is only the `AnchorNativeExecution` obligation record TYPE. **T4 `anchorNative` inhabits it**, proving initial well-formedness and all twelve actual checked edges used by the two nine-action native words.
- T5/T6 construct the two words and actual **production AvailabilityTrace** snapshots. T7 is a total, generic, identity-on-native-data bridge to the nominal research scanners.
- T8 is executable observation data. **T9 `anchorDistanceAgreement` proves** `(3,0,3,8) → (2,1,3,7)` for root4 distance, root5 distance, totalDistance and root5 target respectively. No expected-distance or global-frame oracle is an input.
- T10 constructs **four genuine ForcedRootPhase inhabitants**, both roots in both words, at anchors4/6. These are concrete phases, not a general producer. Core1 ends at Remove1 and core2 at Remove2; the contract has no maximal-core condition.
- T11 authenticates every actual raw insertion ordinal. It is not silently advertised as the unassembled UniqueRawNameInsertions record.
- T13 proves FrontNormal and ForcedRootNeverRetired in both words.
- T14 constructs the actual foreign-child Retire/root classified native square, including an independently proved endpoint relation. It is not an AdmittedDistanceMove.
- T15/T16 provide exact prefix/suffix reifications and the full genuine root5 native suffix frame hypothesis.
- T17 authenticates the complete old catalog with explicit `All` data: each entry has its native phase and cannot be earlier than ordinal7. Generic `indexAll` supplies the quantified antecedents.
- **T18 `anchorGlobalFrameRejectedGivenUnique`, commit `071f4dd0`:** the exact `GlobalDistanceFramesFromNativeSuffix` instance is impossible **given UniqueRawNameInsertions as the sole unassembled explicit premise**. Every other antecedent is constructed. The assumed frames imply3=4. This is a conditional negative theorem, not unconditional retirement and not a Confluence/normalization proof.

The live Tier2 status document explains the arithmetic and the proposed lexicographic per-root direction. That direction is not yet a proved normalizer. The finding concerns this research frame contract, not an asserted erratum in the paper.

## Bounded failures, repairs and evidence corrections

### Exhausted: T12 (no fourth or renamed retry)

**`L2R16 T12: UniqueRawNameInsertions on the anchor fixture via if-reduction` — interface-vs-primitive wall.**

T12-1 found identically printed conditional result types with `right`/`left` mismatch. The expressly authorized **R87 visibility companion** (`a3e1c261`, V1168) changed only `export`→`public export` and one docstring sentence for NEW `anchorInsertionAt`; no declaration, body or type changed. Exact before/after hashes are guarded. It counts as one other-lexical repair within40.

T12-2 still failed. T12-3 eliminated the outer Bool before the record and observed `selected == 4` with an equation, but failed matching the producer conditional to primitive `equalNat`. The full attempted module was removed, its exact source/errors archived, and no `anchorUnique` declaration retained. T13's subsequent module at the same path contains different front/catalog statements, not a renamed uniqueness retry.

The supervisor-authorized **different** uniqueness data-agreement statement remains UNATTEMPTED, first L2R17 unit: explicit DecEq/Eq dictionaries, computed concrete-word uniqueness, Refl at the ω definition, erased Bool=True consumer, no `if` over selected. No existing checked generic checker→record consumer was invented to fit the one-unit permission.

### Other bounded attempts

- T11-1 omitted the explicit type parameters of `rawInsertionNameAt`. T11-2's Refl LHS caused a coverage explosion (267.813s) and failed. T11-3 uses the observed equality plus rewrite and passed in0.898s. No unsafe totality assertion was used.
- T17-1's dependent case consumer hit the18GiB guard: **maximum sampled RSS over command-matching idris2 processes 19,023,792KiB**, interrupted, no flushed Building line, no PASS. T17-2 was a **preflight-only** rejection because the conservative guard found the word `with` in a docstring; no compiler started. T17-3 replaced the consumer representation by explicit All data and passed (1.189s,899680KiB). Three requests, only two compiler records; the missing request is not hidden or reused.
- T18-1 mistakenly supplied equality Refl where least forced-root closure evidence was required; repaired to genuine `KeyForces Here Refl`. T18-2 exposed a stuck `nativePairTrail` because its defining module was only transitive. **Directly importing `L2R13TerminalMove`** obeyed the binding reduction rule and T18-3 passed (2.626s,1261136KiB).
- The R1 receipt's copied “one new declaration” label was wrong; the enforced delta was zero. The original receipt is preserved and an explicit correction record is archived.
- V1024 was an EOF-whitespace **preflight rejection**, not a compiler failure. Its identifier was not reused; an authorized rstrip repair received its own fresh check.
- A premature T3 commit command was rejected because its compiler receipt did not yet exist. `set -e` stopped the surrounding command; nothing was staged/committed or edited after that rejection, and the running compiler was not interrupted. The later commit used the actual completed receipt.

## Long checks and final validation

Long checks started at04:02:23 UTC after the five approved independent companions. Seven historical long fixture targets were predeclared48GiB, before their first long invocation. The default remains18GiB elsewhere. There is at most one lane-owned Idris check at a time. No shared lock/rebuild-window operation and no foreign compiler signal occurs; overlaps are timestamps only.

The lane-owned finish plan reserves the last few minutes for every new module's final dependency-ordered check. Unfinished long fixtures are listed UNCHECKED with pre-unfreeze receipts, not semantic failures. Externally blocked obligations remain blocked. No package or cold build is used as a shortcut. `CP4SupportSolution` hash and mtime are checked before/after every compiler invocation.

**Final inherited closure:** all eight deferred targets freshly PASSED. Final inherited counts are **194/200 fresh green: 105 unchanged + 89 repaired; six BLOCKED-ON-R206**. No inherited target remains UNCHECKED or blocked solely on a lane dependency. Current-source import-invalidation audit found **zero** later changed-dependency invalidations. All twelve new modules also freshly PASSED final validation V1177–V1188 by05:29:10 UTC, with exactly one own-target Building line each.

**Final state / commands / review:** populated in `FINAL-VALIDATION-PLAN`, `FINAL-SUMMARY`, `RECHECK-STATE`, generated ledgers and the independent report at the archive boundary. The mechanical verifier checks exact source/log hashes, declaration deltas, gate-specific visibility changes, request/attempt budgets including preflight gaps, merge/scope boundaries, archive membership, own-compiler absence and no staged files. Twenty-three adversarial compiler-free evidence tests pass. Mechanical verification is **not** parent-owned mathematical review.

## Status

Fully checked at the stated scopes: the light inherited closure; authorized qualification/EOF/strict-clause/core restatements; all seventeen retained Tier2 declarations including actual native execution, production snapshots/bridge, measured vectors, four concrete phases, native square/suffix frames and complete catalog coverage.

Partial: inherited closure remains externally blocked in six R206 cases (all deferred lane targets passed); the global-frame negative theorem is conditional **only on the unassembled uniqueness premise**. Generic phase/normalizer/lifecycle/cross-bundle residues remain open. No new hole, postulate or unsafe escape was introduced; production source and its existing hole census remain unchanged by this lane.

Next: the explicitly different L2R17 uniqueness data-agreement unit, then—if that premise is assembled—the unconditional frame-contract refutation and a carefully specified lexicographic strategy. Do not retry the exhausted if-reduction statement. Parent-owned mathematical review remains the acceptance gate.
