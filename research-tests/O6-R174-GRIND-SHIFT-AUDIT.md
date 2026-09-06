# R174 grind-shift audit

Start 2026-09-06 20:31:31 UTC: `cp5-thm73-scoping`, required HEAD `8b68e37`,
only allowed untracked `paper/` and frozen adversarial review. Four-hour deadline
2026-09-07 00:31:31 UTC; no new attempts after 23:51:31; safe final gate by
00:16:31. Idris 2 0.8.0; `--source-dir` and `--check` verified from help.
All checks seeded, serialized, detached with diagnostic-aware monitoring; no
build deletion or from-scratch rebuild. Paper's complete 3883 lines read;
R173/R172 audits, R172 recon and R146 strategy read before proof work.

## Unit A — owner-requested freshness reclassification

`b7f0e80` updates README, THM73-PLAN and NOTES only. Definition 47's local
absence premise is distinguished from global freshness used by the Lemma-71
sorting step of Theorem 73, satisfied by §5.1's never-reused UID implementation.
R137/R172/Finding-8 reuse countermodels are necessity evidence, not paper or
implementation bugs. UniqueRawNameInsertions is implemented in R173, not future
work. CP3 has a missing hypothesis at the frozen surface; raw-premise
satisfiability under uniqueness must be re-verified. Historical audits and the
R146 memo are unchanged. Documentation whitespace check passes; no compiler
invocation or source change belongs to Unit A.

## Hygiene H1

`2a9b960`, zero new declarations, fresh ordinal-capital check PASSED 1/3,
20:34:37–20:39:50 UTC, exit 0, sampled peak 39,832,656 KiB. Removes only the EOF
blank line at `CP5UniqueRawNameOrdinalCapital.idr:48` (R173 warning).
The two explicitly authorized stale disposable-probe outputs were removed:

- `build/ttc/2025081600/DGamma/R173O17FreshNameProbe.ttc` (22,974 bytes)
- `build/ttc/2025081600/DGamma/R173O17FreshNameProbe.ttm` (29,275 bytes)

No other TTC/TTM or directory was deleted; LocalDiamond's seed is preserved.
The 938-MB ordinal TTC/import-cost debt is not claimed cured by whitespace.

## Unit B — C58 observed-value cure, PASSED

The archived `canonicalWorkActivationInsertDistinct` statement/body was never
restated. Instead, separate exact constructor equations and scalar installation
observations are composed. Top-level types fully instantiate all five model
arguments at installedAt applications. No output-shaped actor-distinctness
hypothesis is supplied to the operational producer. These implementation-only
helpers remain private under the R173 ruling.

| Unit | Declaration | Commit | Attempts / fresh check UTC | Sample peak KiB |
|---|---|---|---|---:|
| B1 | `canonicalWorkInsertOwnerExact` | `59368fd` | PASS 1/3, 20:40:11–20:41:06 | 19927024 |
| B2 | `canonicalWorkFiredInsertActorExact` | `bf905d2` | PASS 1/3, 20:41:27–20:42:22 | 19964672 |
| B3 | `canonicalWorkObservedActivationInstalled` | `f4fbcc4` | PASS 1/3, 20:42:45–20:43:40 | 19952704 |
| B4 | `canonicalWorkCheckedInsertUninstalled` | `82a98ee` | PASS 1/3, 20:44:03–20:45:00 | 19952048 |
| B5 | `canonicalWorkInstalledScalarsDistinct` | `bb4d854` | PASS 1/3, 20:45:20–20:46:19 | 19938608 |
| B6 | `canonicalWorkObservedActivationInsertDistinct` | `0584144` | PASS 1/3, 20:46:45–20:47:42 | 19965760 |

B3 takes the actor VALUE and its erased projection equation. B4 derives actual
source absence from successfulInsertAbsent and uses public installedAtMissing,
not an independently restated anonymous case tree. B5 never sees a transition
under lookup. B6 compares observed raw scalars, consuming the actual checked
OInsert, not the archived generic projection-indexed C58 telescope. No
count-equality bridge is needed in this local fixed-state seam. B1/B2 are
checked constructor-equation capital; the actual root integration below uses
the B3–B6 observed-value route, not B2 as a false dependency claim.

## Unit C — actual root insertion producer integration

| Unit | Declaration | Commit | Attempts / fresh check UTC | Sample peak KiB |
|---|---|---|---|---:|
| C1 | `canonicalWorkObservedPairInsertDistinct` | `ec686ea` | PASS 1/3, 20:48:49–20:49:44 | 21799888 |
| C2 | `canonicalRootInsertionHoistActual` | `81b0887` | PASS 1/3, 20:50:11–20:51:06 | 21780496 |

C1 authenticates the actual insertion from the SAME aligned adjacent pair and
passes its equation to the observed-value cure. C2 returns the actual sealed
root-hoist result from the source bundle/decomposition and activation/root
classification alone: no caller-supplied actor inequality, diamond, early
transition, target, or external relation. This closes the local A/Insert scalar
bridge operationally, not just as a detached proposition. It does NOT sort all
root inputs or close O17.

### Root-placement semantic concern — analysis, NOT a checked countermodel

While inspecting the next root-hoisting seam, a different potential obstruction
appears: local provision disjointness, not raw-name reuse. Consider the R172
shape with THREE distinct births (parent 0, generated child 1, later root 2),
but child 1 and root 2 declare the same nonempty provision key K:

0. insert parent 0 (empty dependency/provision, one identity tagged yield);
1. begin parent 0;
2. insert child 1 under 0 (empty dependencies, provision [K], empty program);
3. retire child 1;
4. remove child 1;
5. insert DISTINCT root 2 (same child component, provision [K]);
6. retire root 2;
7. finish parent 0.

The intended raw insertions are unique. The child/root never become Active,
so their empty programs do not obviously contradict the trace-indexed
provision-totality premise; that MUST be checked, not assumed. The local
remove-1/insert-2 crossing would try to insert root 2 while child 1's DECLARED
provision is still present, violating provisionsDisjointFrom even though name
2 is fresh. Root-first would leave root 2 (no external removal) occupying K
before parent 0 can register its accounted child 1. Registration discipline
requires that child after parent begin; both names are distinct throughout.

This is a semantic *candidate*, not a proved impossibility of the revised O17,
not a bug classification, and not authority for a new premise or surface change.
The full revised O17 bundle/shape/order/uniqueness has NOT been constructed for
it. Work pauses at `81b0887` for a supervisor decision on bounded local
provision-collision reconnaissance versus another authorized continuation. No
proof budget is exhausted; no failed probe or hidden declaration is retained.

## Remaining producer census at this checkpoint

1. Root-input placement/hoisting: actual single A/root-Insert producer now
   derives distinctness; whole root phase (including retire/remove and crossings
   of internal orchestration) OPEN, concern above.
2. A/Insert scalar bridge: CLOSED locally (B6/C1/C2); A/A–O/A–O/O applicability
   and full orientation dispatch OPEN.
3. Sealed adjacent results: actual A/root-Insert result produced by C2 with
   transported bundle/discipline/external evidence through existing O6;
   all other selected grouping cases OPEN.
4. Reached closing-free shape preservation: OPEN.
5. Simultaneous updated blocks/ranges/finite derivation: initializer capital
   only, complete progress producer OPEN.
6. Structural BlockBefore across actual pieces: OPEN.
7. Global strictly decreasing sorting measure: OPEN; one-root ordinal decrease
   is not a whole-sort measure.
8. Exact registration-accounting fold alignment: OPEN.

O17 body 0/3; holes remain six, expected split 1/4/0/0/1 (fresh gate census to
follow). Unit D not yet begun. No O19 body, O21 withdrawal, G31/global-negation,
production edit, new with, unsafe escape, or frozen theorem call.

## Validation protocol / pending final gate

Every retained declaration has its own fresh Building marker, exit 0, no Error
diagnostics, and immediate commit; one new top-level per invocation. All checks
use `idris2 --source-dir src --source-dir research --check
research/DGamma/<Spike>.idr`. Detached supervisor and logs/serialized ledger
are `/tmp/dgamma-r174-{launch,check}.py` and `/tmp/dgamma-r174/ledger.jsonl`.
Final seeded package, census, frozen hashes, ledger, source diff and no-staging
checks will be appended before the final acceptance gate.
