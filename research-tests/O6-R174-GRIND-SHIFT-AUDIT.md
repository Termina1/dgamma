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

## Supervisor-ratified bounded provision reconnaissance

Supervisor ratifies `6065bb4` and authorizes at most SIX micro-units or 90 minutes,
whichever first, inside Unit C: paper-clause reading, then actual input
inhabitation, then (ONLY if both succeeded) the local obstruction. No O17 body,
surface/hypothesis change or O19/O21/G31 work. Cap hit or dissolved concern
returns to the producer chain; no independent extension of this fixture budget.

### Step (1), exact paper/Idris clause map — move IS required literally

Paper Theorem 73(1), extracted lines 2300–2305 (printed p.52):

> "a sequence that takes the same orchestration steps in their original order,
> those at a fiber the orchestrator inserted preceding every lifecycle step
> and each of the rest following the step that registered the fiber it acts on"

The paragraph using Lemma 71, lines 2322–2331:

> "With a lifecycle step of the same fiber there is nothing to exchange, an
> O-Insert of n already preceding every step of n and an O-Retire or O-Remove
> of n applying only outside A, which takes no lifecycle step. Moving each to
> the front in turn preserves their relative order. An orchestration step at a
> fiber some activation registered cannot go to the front, its premises
> requiring that fiber to be present, so it stays where the registration put it"

For the candidate, root 2 is a fiber the orchestrator inserted. The first
explicit clause therefore places its insertion before parent 0's L-Begin,
and Definition 47 places the generated child 1 after that begin. The relative
order phrase does NOT exempt root 2 from the explicit root-before-every-lifecycle
requirement. Read as preserving all generated orchestration order too, it adds
another constraint; it does not license leaving root 2 after the child removal.
Root 2 is retired/outside A, so the quoted same-fiber exception does not remove
the crossing past parent 0. Lemma 72 removes closing episodes and their births;
parent 0 stays open, so that deletion does not remove its generated child here.

`SortedClosingFreeTrace.sortedInputPlacement` uses
`CanonicalInputPlacement.allRootInputsFirst`, whose `RootInputsBeforeLifecycle`
(CP3:2037–2049) excludes every later `RootOrchestrationStep` after ANY lifecycle
step. `RootInsertStep` is unconditional on support. Thus the explicit root-first
clause is directly represented; this concern does not dissolve as merely an
Idris requirement stricter than that literal paper clause. This is not a
conclusion that the full paper theorem is refuted: input inhabitation is next.

Input-totality check of the DEFINITIONS only: CP3:826–858 samples the actual
actor's post-state Active table (`TransitionComponentTotal`), not hypothetical
completion of an unused empty program. A child retired and removed without
activation therefore has a vacuous Active obligation on this trace. To avoid
confusing that research specialization with paper Definition 69's component
condition, a concrete fixture may instead use the existing genuinely installing
`CalculusChecks.providerComponent` for BOTH distinct names 1 and 2; neither is
executed on the proposed trace. Single-source legality still has to be checked
at EVERY actual insertion. No such fixture/premise proof has been compiled yet.
The trace has EIGHT actions including initial parent insertion (seven after it).

Step (1) is submitted at the required mid-shift gate BEFORE any step-(3) spend.

## Provision-recon cap outcome — SIX units spent, full inputs NOT inhabited

`r174ProvisionExecution` uses actual `CalculusChecks.providerComponent` for both
child 1 and distinct root 2. This is the existing installing program
`[providerInstall, providerFinish]`, not an empty non-providing impostor. The
parent has an empty provision. The successful eight-action execution exercises
the live single-source check at all three insertions. The returned
CertifiedActionTrace owns actual TraceComponentsTotal. The checked tuple gives
length 8 (excluding the empty fallback), quiet = True, noFailedFibers = True,
allFibersTotalOnProvision = True, supportSet = [0]. These are computed facts,
not a supplied-capital fixture. Neither provider program is executed here;
there is no new universal component-totality proof about it.

The actual insertion ordinals are 0, 2, 5 for raw names 0, 1, 2; the strong
UniqueRawNameInsertions premise is proved. This does NOT inhabit all revised
O17 inputs. Exact RegistrationProtocol/Discipline, TraceIndependent,
ReplayInvariantBundle, NoClosingEpisodes, ClosingFreeTraceShape, and actual
O14 ordering have NOT been built for this candidate. No step-(3) local
obstruction was attempted. There is no checked revised-O17 countermodel or
canonical-form revision proposal in code.

| Unit | Declaration | Commit | Attempts / fresh check UTC |
|---|---|---|---|
| P1 | `r174ProvisionParentStep` | `87bdad1` | PASS 1/3, 21:00:05–21:00:07 |
| P2 | `r174ProvisionParent` | `aa027c2` | PASS 1/3, 21:00:24–21:00:26 |
| P3 | `r174ProvisionExecution` | `788478f` | PASS 1/3, 21:00:49–21:00:51 |
| P4 | `r174ProvisionExecutionChecks` | `db836ce` | PASS 1/3, 21:01:17–21:01:20 |
| P5 | `r174ProvisionBirthPosition` | `2200588` | PASS 1/3, 21:01:52–21:01:54 |
| P6 | `r174ProvisionUniqueInsertions` | d44993a | PASS 3/3, 21:19:20–21:19:22 |

P6 attempts 1 and 2 were consciously interrupted after 10 and 6 minutes of
unexpected normalization (not tool-window failures). Both are CHARGED without
compiler verdict: empty buffered logs, exit 143, actual sampler peak unavailable.
The supervising wrapper terminated the compiler's process group; process
inspection confirmed no orphan before the next invocation. The first
post-kill assertion accidentally matched its own shell's textual search string,
then exact PID inspection confirmed all three PIDs absent at 21:12:30. This was
a monitoring assertion error, not a compiler error, orphan, or pass.

P6-1: 21:02:18–21:12:30 UTC (end is quiescence-observation upper bound).
P6-2: 21:12:55–21:18:58 UTC. Attempt 2 supplied every constructor index explicitly;
it still normalized pathologically. Attempt 3 moves the SAME proof into a
consumer module. The execution VALUE is exported opaquely (consumers need its
trace, not the builder's proof-term reduction); its producer-owned observation
proof is exported as an opaque proof. P4/P5 still compute inside their owner.
BOTH modules freshly pass in 2.1 seconds. No new theorem premise, weaker proof,
or escape is involved. The visibility change is confined to this shift's new
fixture: `r174ProvisionExecution` public export → export;
`r174ProvisionBirthPosition` private → export. LocalDiamond is untouched.
This is a measured success of the opaque producer-boundary cure, NOT a claimed
fix of the separate 938-MB ordinal TTC debt.

### Archived interrupted P6 declarations (no retained unfinished proof)

P6-1 source declaration SHA256 `4a43d76999abf51a559bd7c27edcaba668986891942184cd80b03b5cd8191dc2`; complete compiler diagnostic transcript: EMPTY (interrupted, no verdict).

```idris
||| Strong whole-trace uniqueness really holds for the provision candidate.
||| Full RegistrationDiscipline/independence/closing-free O17 inputs remain open.
export
0 r174ProvisionUniqueInsertions :
  (UniqueRawNameInsertions Nat ToyKey ToyRuntime String ToyValue %search %search
    (certifiedTrace r174ProvisionExecution))
r174ProvisionUniqueInsertions = MkUniqueRawNameInsertions
  (\selected, leftParent, rightParent, leftComponent, rightComponent, left, right =>
    trans (r174ProvisionBirthPosition selected (locatedActionOrdinal left)
      (rawInsertionNameAtLocated Nat ToyKey ToyRuntime String ToyValue
        (certifiedTrace r174ProvisionExecution) selected leftParent leftComponent left))
      (sym (r174ProvisionBirthPosition selected (locatedActionOrdinal right)
        (rawInsertionNameAtLocated Nat ToyKey ToyRuntime String ToyValue
          (certifiedTrace r174ProvisionExecution) selected rightParent rightComponent right))))
```

P6-2 source declaration SHA256 `f64cad96736e609990de93421aa15ef3932323f332652d58f943319c81741416`; complete compiler diagnostic transcript: EMPTY (interrupted, no verdict).

```idris
||| Strong whole-trace uniqueness really holds for the provision candidate.
||| Full RegistrationDiscipline/independence/closing-free O17 inputs remain open.
export
0 r174ProvisionUniqueInsertions :
  (UniqueRawNameInsertions Nat ToyKey ToyRuntime String ToyValue %search %search
    (certifiedTrace r174ProvisionExecution))
r174ProvisionUniqueInsertions = MkUniqueRawNameInsertions
  {name = Nat} {key = ToyKey} {world = ToyRuntime} {error = String} {value = ToyValue}
  {nameEq = %search} {keyEq = %search}
  {initial = MkSystemState (MkToyRuntime False False) emptyContext}
  {finalState = certifiedFinal r174ProvisionExecution}
  {trace = certifiedTrace r174ProvisionExecution}
  (\selected, leftParent, rightParent, leftComponent, rightComponent, left, right =>
    trans (r174ProvisionBirthPosition selected (locatedActionOrdinal left)
      (rawInsertionNameAtLocated Nat ToyKey ToyRuntime String ToyValue
        (certifiedTrace r174ProvisionExecution) selected leftParent leftComponent left))
      (sym (r174ProvisionBirthPosition selected (locatedActionOrdinal right)
        (rawInsertionNameAtLocated Nat ToyKey ToyRuntime String ToyValue
          (certifiedTrace r174ProvisionExecution) selected rightParent rightComponent right))))
```

### Owner-only possible future resolution (NOT acted on)

Supervisor notes that IF full input inhabitation and the obstruction are later
proved, “keys never re-provided” would be unfaithful to Cordis: it rejects only
duplicate LIVE providers (`reflect.ts:187–188`), while disposal/HMR may legitimately
re-provide a service. A possible canonical-form revision would place root
insertions at the earliest position where their declared provisions are free.
That is a paper-facing owner decision, NOT an adopted hypothesis or surface
change in this shift. The six-unit cap is reached; no seventh fixture unit is
authorized. O17 producer work on the current surface resumes only subject to
the required cap-outcome gate; Unit D remains deferred until C gate/stop.

## Second supervisor-bounded window (12 units / 75 minutes)

At the cap gate supervisor ratifies P1–P6 and CHANGES continuation: first execute
the concrete root-first prefix with root 2 RETIRED BUT PRESENT, then test child 1
insertion. If admitted, dissolve concern and resume root producers. If rejected,
use the remaining window to inhabit all original O17 inputs before the local
obstruction theorem. After the window only surface-independent producers are
authorized unless the concern dissolves. The clock starts Q1 at 21:25:54 UTC;
75-minute cutoff is 22:40:54 UTC. No surface/hypothesis change authorized.

### Step (2b): REJECTED, branch (ii), not dissolved

Q1 `r174SortedProvisionPrefix` (`3fcd566`, PASS 1/3) builds actual actions
insert0; insert2; retire2; begin0. Q2 `r174SortedProvisionGuardChecks` (PASS 3/3)
computes a tuple `(4, Just True, False, False)`: actual prefix length four,
root 2 lookup is retired, the child provision is not disjoint, and
`isJust (checkedApplyAction (OInsert 1 (ChildOf 0) providerComponent) ...)`
is False. This is the explicitly requested guard experiment, not the deferred
step-(3) full-input local obstruction theorem. Both providers use the genuinely
installing existing program. Retirement DOES NOT remove a declared provision
from `provisionsDisjointFrom` (Calculus:1349–1355 checks every registry fiber).

Q2 attempts 1/2 failed only on missing explicit observation instantiations:
first registryFibers, then lookupFiber/map retired. Attempt 3 instantiates ALL
of name/key/value/world/error on those projections and passes. Full diagnostics:

Q2-1:

```text
2/2: Building DGamma.R174O17SortedProvisionGuard (research-tests/DGamma/R174O17SortedProvisionGuard.idr)
Error: While processing type of r174SortedProvisionGuardChecks. Can't solve constraint between: ToyKey and ?key [no locals in scope].

DGamma.R174O17SortedProvisionGuard:43:24--43:75
 39 |   ((transitionCount (certifiedTrace r174SortedProvisionPrefix),
 40 |     map retired (lookupFiber 2 (registry (certifiedFinal r174SortedProvisionPrefix))),
 41 |     provisionsDisjointFrom {name = Nat} {key = ToyKey} {value = ToyValue} {world = ToyRuntime} {error = String}
 42 |       (componentProvisions providerComponent)
 43 |       (registryFibers (registry (certifiedFinal r174SortedProvisionPrefix))),
                             ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

```

Q2-2:

```text
2/2: Building DGamma.R174O17SortedProvisionGuard (research-tests/DGamma/R174O17SortedProvisionGuard.idr)
Error: While processing type of r174SortedProvisionGuardChecks. Can't solve constraint between: ToyKey and ?key [no locals in scope].

DGamma.R174O17SortedProvisionGuard:40:33--40:84
 36 | ||| Retirement leaves the declared provision in the registry guard's domain.
 37 | export
 38 | 0 r174SortedProvisionGuardChecks :
 39 |   ((transitionCount (certifiedTrace r174SortedProvisionPrefix),
 40 |     map retired (lookupFiber 2 (registry (certifiedFinal r174SortedProvisionPrefix))),
                                      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

```

The remaining full-input work proceeds under the same bounded window; no conclusion about revised O17 yet.
