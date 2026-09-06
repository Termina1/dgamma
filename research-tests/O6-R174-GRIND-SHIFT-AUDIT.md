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

## Second-window operational stop: Q9 charged 3/3, NO compiler verdict

Q3–Q8 prove and assemble an actual `RegistrationProtocol ToyKey ToyValue
ToyRuntime String` with catalog tag 0 → genuinely installing providerComponent.
The executable rank admits only dependency-free components: tagged programs
rank 0, tag-free programs rank 1. An actual tagged member structurally proves
rank 0; the real provider has rank 1. Precedence is excluded by admitted
consumer dependencies, NOT by an empty key type. This removes the previous
protocol-definition gap but does NOT construct the trace's RegistrationDiscipline.

| Unit | Declaration | Commit | Result |
|---|---|---|---|
| Q3 | `r174ProvisionCatalog` | `e73c4e2` | PASS 1/3 |
| Q4 | `r174ProvisionRank` | `36eb276` | PASS 1/3 |
| Q5 | `r174AllRecursiveContainsFalse` | `ce69a73` | PASS 1/3 |
| Q6 | `r174ProvisionYieldRanks` | `2b73b19` | PASS 1/3 |
| Q7 | `r174ProvisionPrecedenceRanks` | `c667f9a` | PASS 1/3 |
| Q8 | `r174ProvisionProtocol` | `23058fc` | PASS 1/3 |
| Q9 | `r174ProvisionAligned` | FULLY REVERTED | 3 charged interrupted runs, NO verdict |

Q9 tries to align the SAME eight-action builder trace. Nested AlignedStep
construction causes pathological normalization. Attempt 1 supplies concrete
actions/tags and Refl equations; attempt 2 lets the exact target trace determine
its already-owned equation fields; attempt 3 additionally leaves action/tag
slots to the exact target, while explicitly instantiating all universes and
dictionaries at each constructor. None returns a compiler verdict within its
engineering bound (8, 6, 6 minutes). Each is charged. Inference did NOT cure this
wall and is NOT retained as an implementation style. Peak RSS unavailable on
interruption; samples include 31,717,536 KiB (Q9-1) and 47,790,208 KiB (Q9-3),
which are lower bounds, not claimed peaks. This is a checking-cost frontier,
NOT a proof of uninhabitability or a compiler rejection.

All compiler groups were terminated and quiescence checked before each next
invocation. Q9 is fully reverted, including its newly added unused protocol
import. Reverted candidate freshly REBUILT/PASS at 21:54:03–21:54:05; its opaque
uniqueness consumer passes a seeded unchanged-source invocation at
21:54:20–21:54:23 (no re-elaboration claimed). No partial trace-alignment proof
or new hole remains, no new TTC debt file was deleted. Existing fixture TTCs
remain small; Q9 never emitted a successful expanded TTC.

Second window used NINE units and about 28 minutes before the mandatory 3/3
gate; Q10–Q12 were NOT attempted. Exact trace alignment, discipline,
TraceIndependent, full bundle, NoClosingEpisodes, shape, O14 order remain open.
The successful executable guard rejection and global uniqueness do not fill
those premises. NO step-(3) local obstruction theorem, O17 body, surface change,
or root-phase continuation occurred. Root placement stays PAUSED, not disproved.
This gate asks the owner to ratify the operational stop before surface-independent
producer work or Unit D. A future producer-owned aligned/certified trace builder
is a possible REPRESENTATION redesign, not an authorized fourth Q9 restatement.

### Complete archived Q9 declarations and transcripts

Q9-1, SHA256 `34479dcd6a242b3b00ec20d2db9b33b0753ea9d6363a037ac236d1f905aeaa92`. Compiler transcript EMPTY (interrupted before verdict).

```idris
||| Exact dictionary alignment of the SAME built trace, computed at its owner.
export
0 r174ProvisionAligned : AlignedTransitions Nat ToyKey ToyRuntime String ToyValue %search %search
  (certifiedTrace r174ProvisionExecution)
r174ProvisionAligned = AlignedStep (OInsert 0 Root r174ProvisionParent) OInsertTag Refl _
  (AlignedStep (LBegin 0) LBeginTag Refl _
    (AlignedStep (OInsert 1 (ChildOf 0) providerComponent) OInsertTag Refl _
      (AlignedStep (ORetire 1) ORetireTag Refl _
        (AlignedStep (ORemove 1) ORemoveTag Refl _
          (AlignedStep (OInsert 2 Root providerComponent) OInsertTag Refl _
            (AlignedStep (ORetire 2) ORetireTag Refl _
              (AlignedStep (LAdvance 0) LFinishTag Refl _ AlignedEnd)))))))
```

Q9-2, SHA256 `1e8d7f237ba167c591c2e2c55fad091a6487515a57e4d628ee49581f5d59578b`. Compiler transcript EMPTY (interrupted before verdict).

```idris
||| Exact dictionary alignment of the SAME built trace, computed at its owner.
||| Equation/rest constructor slots are fixed by the exact expected trace index;
||| do not force a new Refl to normalize against the builder-owned equation.
export
0 r174ProvisionAligned : AlignedTransitions Nat ToyKey ToyRuntime String ToyValue %search %search
  (certifiedTrace r174ProvisionExecution)
r174ProvisionAligned = AlignedStep (OInsert 0 Root r174ProvisionParent) OInsertTag _ _
  (AlignedStep (LBegin 0) LBeginTag _ _
    (AlignedStep (OInsert 1 (ChildOf 0) providerComponent) OInsertTag _ _
      (AlignedStep (ORetire 1) ORetireTag _ _
        (AlignedStep (ORemove 1) ORemoveTag _ _
          (AlignedStep (OInsert 2 Root providerComponent) OInsertTag _ _
            (AlignedStep (ORetire 2) ORetireTag _ _
              (AlignedStep (LAdvance 0) LFinishTag _ _ AlignedEnd)))))))
```

Q9-3, SHA256 `dea85370333c6ae1068d75ebeac6ff16f7cfb51dd0cecb759a66714ed655a4a7`. Compiler transcript EMPTY (interrupted before verdict).

```idris
||| Exact dictionary alignment of the SAME built trace, computed at its owner.
||| All action/tag/equation/rest slots are fixed by the exact expected trace
||| index; the universe and dictionaries are explicit at each constructor.
||| No caller premise is added and no named hole may survive elaboration.
export
0 r174ProvisionAligned : AlignedTransitions Nat ToyKey ToyRuntime String ToyValue %search %search
  (certifiedTrace r174ProvisionExecution)
r174ProvisionAligned = AlignedStep {name = Nat} {key = ToyKey} {world = ToyRuntime} {error = String}
    {value = ToyValue} {nameEq = %search} {keyEq = %search} _ _ _ _
    (AlignedStep {name = Nat} {key = ToyKey} {world = ToyRuntime} {error = String}
    {value = ToyValue} {nameEq = %search} {keyEq = %search} _ _ _ _
    (AlignedStep {name = Nat} {key = ToyKey} {world = ToyRuntime} {error = String}
    {value = ToyValue} {nameEq = %search} {keyEq = %search} _ _ _ _
    (AlignedStep {name = Nat} {key = ToyKey} {world = ToyRuntime} {error = String}
    {value = ToyValue} {nameEq = %search} {keyEq = %search} _ _ _ _
    (AlignedStep {name = Nat} {key = ToyKey} {world = ToyRuntime} {error = String}
    {value = ToyValue} {nameEq = %search} {keyEq = %search} _ _ _ _
    (AlignedStep {name = Nat} {key = ToyKey} {world = ToyRuntime} {error = String}
    {value = ToyValue} {nameEq = %search} {keyEq = %search} _ _ _ _
    (AlignedStep {name = Nat} {key = ToyKey} {world = ToyRuntime} {error = String}
    {value = ToyValue} {nameEq = %search} {keyEq = %search} _ _ _ _
    (AlignedStep {name = Nat} {key = ToyKey} {world = ToyRuntime} {error = String}
    {value = ToyValue} {nameEq = %search} {keyEq = %search} _ _ _ _
    (AlignedEnd))))))))
```


## Unit D complete — analysis only after ratified C stop

Supervisor closes the second window at Q9 and ratifies the cost-bound stop.
Root placement becomes an OWNER decision and remains paused, not refuted.
Unit D ran after that explicit C stop with more than two hours remaining;
no Idris declaration/compiler attempt was made during D. Its analysis is in
`O6-R174-A8-CAUSE-SHARING-RECON.md` (completed about 22:06 UTC, well within
its ≤60-minute target).

It classifies the local O19 stop, other three CrossTrace holes, and each O21
withdrawal/outside-both branch by reuse / A8 / neither. It states an exact
UNCOMPILED existential raw-closing-maximum lemma sufficient to show the frozen
CP3 raw premise satisfiable under uniqueness, without assuming or proving it,
calling the frozen theorem, or casting generation-scoped evidence.

Key new findings: uniqueness is retained in the actual O17 worklist and
transported through actual deletion/adjacent derivations, but NOT stored in
IndependentCanonicalSchedule and NOT an argument of the unchanged CrossTrace/
O21 telescopes. O19's dependent-consumer early activation stop is a DIFFERENT
guard from A8's two-provider declaration collision. O21 endpoint vestigiality
does not imply prospective insertion-guard inertness.

The owner-decision section compares canonical-form revision against model
service-ownership/guard revision and rejects global never-reprovided keys as
implementation-unfaithful. Independently inspected upstream Cordis is pinned to
`c594d1aa4e901992f8836f9d747d5a640c9b9d58`: `reflect.ts:189–190` rejects occupied
service-store entries, and the disposer deletes them at 198. “Live” is STORE
occupancy, not simply Active; fiber uid retirement precedes asynchronous
cleanup. A one-line retired-flag exception is therefore not justified by this
inspection. This is an owner memo, not an adopted semantic change.

Per supervisor ruling, remaining work until the 40-minute guard is restricted
to surface-INDEPENDENT O17 producers. No root placement/hoisting, O19 body,
O21 withdrawal, CP3 proof, or fourth Q9 attempt is authorized.

## Surface-independent reached-shape/worklist milestone

S1–S17 are committed, each separately checked. S3 passes 2/3 after using the
aligned constructor's OWN `rest` instead of the outer `later` alias; all other
S1–S17 pass 1/3. Every fresh CanonicalSort compilation takes about 53–55 seconds
with sampled RSS about 18–22 million KiB. No root-phase/placement helper is
changed or called by this chain.

The complete semantic chain now proves:

1. A closed episode has an exact unload occurrence. An aligned empty-initial
   source with no closing episode cannot have such an occurrence (S1–S4).
2. NoClosingEpisodes survives an ACTUAL finite adjacent derivation via the
   sealed all-action origin map (S5); reached shape follows from its actual
   replay bundle (S6).
3. The EXISTING O17 ClosingFreeTraceShape input itself implies NoClosingEpisodes
   (S7–S14), by excluding unloads before an open episode, in its opening, and in
   its installed suffix, or by the unsupported actor's NoLifecycleBy witness.
   There is NO new source no-closing hypothesis or special O13-producer premise.
4. `canonicalWorkReachedShapeFromInput` discharges reached shape from exactly
   that unchanged source shape/bundle and the actual current replay (S15).
5. `canonicalWorkInspectReachedDerived` recomputes current block/range/order
   inspection with derived shape and transported global uniqueness (S16).
6. `canonicalWorkAcceptAdjacentResult` extends the actual finite derivation and
   rebuilds the bundle, shape, uniqueness, fixed order and inspection together
   from ONE sealed adjacent result at that current trace (S17). It does not
   choose a swap, claim the next inspection is ready, preserve an old completed
   prefix for free, or provide a global decreasing sorting measure.

This closes the reached-shape producer and a simultaneous REINSPECTION update
path; it does not close the selected applicability dispatcher, all selected
sealed-result producers, BlockBefore completion, global measure/accounting, or
O17 body. O17 body remains 0/3 and root placement is still owner-paused.

| Unit | Commit | Result |
|---|---|---|
| S1 | `cf15d43` | PASS 1/3 |
| S2 | `9539fe2` | PASS 1/3 |
| S3 | `1097f1f` | PASS 2/3 |
| S4 | `6925f58` | PASS 1/3 |
| S5 | `eaee137` | PASS 1/3 |
| S6 | `378b716` | PASS 1/3 |
| S7 | `70494d2` | PASS 1/3 |
| S8 | `9039825` | PASS 1/3 |
| S9 | `dfedb2d` | PASS 1/3 |
| S10 | `84dc522` | PASS 1/3 |
| S11 | `445c3ab` | PASS 1/3 |
| S12 | `11cd1f4` | PASS 1/3 |
| S13 | `5307ef3` | PASS 1/3 |
| S14 | `3d026a4` | PASS 1/3 |
| S15 | `2f0c6e6` | PASS 1/3 |
| S16 | `8feee6b` | PASS 1/3 |
| S17 | `b55902d` | PASS 1/3 |

S3-1 complete rejected declaration and diagnostic (fully replaced on success):

```idris
||| Consume the exact aligned occurrence returned by an operational origin map.
||| The dictionary and checked equation come from that same source occurrence.
0 canonicalWorkNoClosingRejectsLocatedUnload :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {initial, finalState : SystemState name key value world error} ->
  (global : Transitions initial finalState) ->
  AlignedTransitions name key world error value nameEq keyEq global ->
  bindings (registry initial) = [] ->
  NoClosingEpisodes name key world error value nameEq keyEq global ->
  LocatedActionOccurrence (LUnload selected) global -> Void
canonicalWorkNoClosingRejectsLocatedUnload name key world error value nameEq keyEq selected
  global aligned initialEmpty noClosing
  (MkLocatedActionOccurrence before afterState earlier step later actionExact decomposition) =
    case snd (alignedAppendSplit earlier (MoreTransitions step later)
      (replace {p = AlignedTransitions name key world error value nameEq keyEq}
        (sym decomposition) aligned)) of
      AlignedStep action tag checked rest tailAligned => case actionExact of
        Refl => canonicalWorkNoClosingRejectsUnloadPrefix name key world error value nameEq keyEq selected
          global earlier tag checked later
          (trans (appendTransitionsAssociative earlier
            (MoreTransitions (Fired {before} {afterState} nameEq keyEq (LUnload selected) tag checked) NoTransitions) later)
            decomposition) aligned initialEmpty noClosing

```

```text
5/5: Building DGamma.CP5ConfluenceCanonicalSortSpike (research/DGamma/CP5ConfluenceCanonicalSortSpike.idr)
Error: While processing right hand side of canonicalWorkNoClosingRejectsLocatedUnload. When unifying:
    appendTransitions earlier (MoreTransitions (Fired nameEq keyEq (LUnload selected) tag checked) rest)
and:
    appendTransitions earlier (appendTransitions (MoreTransitions (Fired nameEq keyEq (LUnload selected) tag checked) NoTransitions) later)
Mismatch between: rest and later.

DGamma.CP5ConfluenceCanonicalSortSpike:3046:13--3046:26
 3042 |         Refl => canonicalWorkNoClosingRejectsUnloadPrefix name key world error value nameEq keyEq selected
 3043 |           global earlier tag checked later
 3044 |           (trans (appendTransitionsAssociative earlier
 3045 |             (MoreTransitions (Fired {before} {afterState} nameEq keyEq (LUnload selected) tag checked) NoTransitions) later)
 3046 |             decomposition) aligned initialEmpty noClosing
                    ^^^^^^^^^^^^^

```

## Final surface-independent producer increment (S18–S39)

Proof work stops at `f157f8f`; last new-declaration attempt S39-1 started
23:37:55 and passed 23:38:50 UTC, before the 23:51:31 no-new-attempt guard.
The final review/validation window starts with all 39 S units retained.

- S18/S19 are total POSITIVE action/tag and four-orientation dispatchers.
  Nothing is not a proof of inapplicability, and no diamond follows merely from
  an orientation. Coverage of all actual selected cases and early applicability
  remain independent obligations.
- S20/S21 derive A/A actor distinctness from the SAME actual pair's
  foreign/owned evidence; no supplied actor inequality is smuggled in.
- S22–S25 authenticate both original and moved right occurrences in one sealed
  adjacent result and prove a strict decrease of that right node's ordinal.
  This is genuine LOCAL progress only: other nodes move, and a different
  worklist choice may increase it. It is NOT the global sorting measure.
- S26–S35 derive installation of the ACTUAL open-episode scan residual, exclude
  new Begin there, retain its right action through the EXISTING whole-episode
  selection producer, and show its activation alternative is Iter/Finish.
  No selector or public pair record is strengthened/replaced. Scalar action
  transport follows genuine trace equality; no proof-bearing Transition
  equality, generation/raw cast, or source endpoint guess is used.
- S36–S39 extend that provenance fact through the EXISTING whole worklist
  selector (including arbitrarily many ready nodes), and package its actual
  optional selected pair with the correlated no-Begin proof. Nothing still
  means no grouping choice, not success or an applicable ordering swap.

This distinction matters for the next applicability proof: a GENERIC foreign/
owned pair can place a consumer's first Begin just after its enabling provider,
so generic pair evidence alone does not justify early activation. The actual
O17 grouping producer now proves it cannot select such a Begin. This does not
prove early Iter/Finish applicability either; it identifies and closes one
real provenance sub-obligation without editing or refuting O19.

| Unit | Commit | Fresh result | Start–end UTC |
|---|---|---|---|
| S18 | `e711363` | PASS 1/3 | 22:47:31–22:48:26 |
| S19 | `d74e8ad` | PASS 1/3 | 22:49:12–22:50:07 |
| S20 | `08204b8` | PASS 1/3 | 22:50:53–22:51:48 |
| S21 | `ee33c08` | PASS 1/3 | 22:52:34–22:53:29 |
| S22 | `8aaf8ed` | PASS 1/3 | 22:56:56–22:57:51 |
| S23 | `56382ff` | PASS 1/3 | 22:59:07–23:00:02 |
| S24 | `f310683` | PASS 1/3 | 23:00:47–23:01:41 |
| S25 | `07b1595` | PASS 1/3 | 23:02:33–23:03:28 |
| S26 | `63a224f` | PASS 3/3 | 23:16:38–23:17:33 |
| S27 | `d28e20d` | PASS 1/3 | 23:18:06–23:19:01 |
| S28 | `66a3974` | PASS 1/3 | 23:19:33–23:20:28 |
| S29 | `a66bc76` | PASS 1/3 | 23:21:01–23:21:56 |
| S30 | `f5200aa` | PASS 1/3 | 23:22:33–23:23:28 |
| S31 | `3a62e18` | PASS 1/3 | 23:24:06–23:25:01 |
| S32 | `e34efd8` | PASS 1/3 | 23:25:54–23:26:49 |
| S33 | `a1846df` | PASS 1/3 | 23:27:31–23:28:26 |
| S34 | `855b4eb` | PASS 1/3 | 23:29:04–23:29:59 |
| S35 | `583557a` | PASS 1/3 | 23:30:46–23:31:41 |
| S36 | `a2fed63` | PASS 1/3 | 23:32:55–23:33:50 |
| S37 | `0a079eb` | PASS 1/3 | 23:34:34–23:35:29 |
| S38 | `9cda09a` | PASS 1/3 | 23:36:15–23:37:10 |
| S39 | `f157f8f` | PASS 1/3 | 23:37:55–23:38:50 |

S26 passes 3/3. Its first two diagnostics identify FORCED pattern positions:
`rest = appendTransitions tail later`, then `head = Fired ...`. The final
proof uses `_` in those forced positions and structurally recurses on `tail`;
it introduces no nonlinear pattern, with-block, local helper or alias. The
full rejected declarations/diagnostics follow. All other S18–S39 pass 1/3.
Across S1–S39: 37 pass 1/3, S3 passes 2/3, S26 passes 3/3; no S unit exhausts.

### S26-1 archived rejection

```idris
||| Preserve installed-at-every-boundary evidence on an actual suffix.
0 canonicalWorkInstalledAppendRight :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (earlier : Transitions first middle) -> (later : Transitions middle finalState) ->
  InstalledTrace name key world error value nameEq keyEq selected (appendTransitions earlier later) ->
  InstalledTrace name key world error value nameEq keyEq selected later
canonicalWorkInstalledAppendRight name key world error value nameEq keyEq selected NoTransitions later installed = installed
canonicalWorkInstalledAppendRight name key world error value nameEq keyEq selected (MoreTransitions head tail) later
  (InstalledStep action tag checked rest installed tailInstalled) =
    canonicalWorkInstalledAppendRight name key world error value nameEq keyEq selected tail later tailInstalled
```

```text
5/5: Building DGamma.CP5ConfluenceCanonicalSortSpike (research/DGamma/CP5ConfluenceCanonicalSortSpike.idr)
Error: While processing left hand side of canonicalWorkInstalledAppendRight. When unifying:
    MoreTransitions (Fired ?nameEq ?keyEq ?action ?tag ?checked) ?rest
and:
    MoreTransitions ?head (appendTransitions ?tail ?later)
Pattern variable rest unifies with: appendTransitions ?tail ?later.

DGamma.CP5ConfluenceCanonicalSortSpike:3473:37--3473:41
 3469 |   InstalledTrace name key world error value nameEq keyEq selected (appendTransitions earlier later) ->
 3470 |   InstalledTrace name key world error value nameEq keyEq selected later
 3471 | canonicalWorkInstalledAppendRight name key world error value nameEq keyEq selected NoTransitions later installed = installed
 3472 | canonicalWorkInstalledAppendRight name key world error value nameEq keyEq selected (MoreTransitions head tail) later
 3473 |   (InstalledStep action tag checked rest installed tailInstalled) =
                                            ^^^^

Suggestion: Use the same name for both pattern variables, since they unify.
```

### S26-2 archived rejection

```idris
||| Preserve installed-at-every-boundary evidence on an actual suffix.
0 canonicalWorkInstalledAppendRight :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) -> (selected : name) ->
  {first, middle, finalState : SystemState name key value world error} ->
  (earlier : Transitions first middle) -> (later : Transitions middle finalState) ->
  InstalledTrace name key world error value nameEq keyEq selected (appendTransitions earlier later) ->
  InstalledTrace name key world error value nameEq keyEq selected later
canonicalWorkInstalledAppendRight name key world error value nameEq keyEq selected NoTransitions later installed = installed
canonicalWorkInstalledAppendRight name key world error value nameEq keyEq selected (MoreTransitions head tail) later
  (InstalledStep action tag checked _ installed tailInstalled) =
    canonicalWorkInstalledAppendRight name key world error value nameEq keyEq selected tail later tailInstalled
```

```text
5/5: Building DGamma.CP5ConfluenceCanonicalSortSpike (research/DGamma/CP5ConfluenceCanonicalSortSpike.idr)
Error: While processing left hand side of canonicalWorkInstalledAppendRight. When unifying:
    MoreTransitions (Fired ?nameEq ?keyEq ?action ?tag ?checked) (appendTransitions ?tail ?later)
and:
    MoreTransitions ?head (appendTransitions ?tail ?later)
Pattern variable head unifies with: Fired ?nameEq ?keyEq ?action ?tag ?checked.

DGamma.CP5ConfluenceCanonicalSortSpike:3472:101--3472:105
 3468 |   (earlier : Transitions first middle) -> (later : Transitions middle finalState) ->
 3469 |   InstalledTrace name key world error value nameEq keyEq selected (appendTransitions earlier later) ->
 3470 |   InstalledTrace name key world error value nameEq keyEq selected later
 3471 | canonicalWorkInstalledAppendRight name key world error value nameEq keyEq selected NoTransitions later installed = installed
 3472 | canonicalWorkInstalledAppendRight name key world error value nameEq keyEq selected (MoreTransitions head tail) later
                                                                                                            ^^^^

Suggestion: Use the same name for both pattern variables, since they unify.
```

## Final validation and exact retained frontier

- Idris 2 **0.8.0** reconfirmed. Every proof module remains `%default total`.
- Fresh seeded package invocation PASS **23:39:51–23:40:08 UTC** (16.3s,
  sampled RSS 219,952 KiB), preserving all **207/207** production TTC seeds.
  This is not a from-scratch production rebuild.
- The final retained CanonicalSort source freshly rebuilt on S39-1
  **23:37:55–23:38:50**; no Idris source edit follows it.
- Final R8 `R8FullPipeline.idr` freshly rebuilt PASS **23:40:25–23:42:04**,
  99.7s, sampled RSS 36,443,568 KiB; transcript says `Building DGamma.R8FullPipeline`.
- Final conditional R16 `R16ConfluenceTheoremAssemblyPositive.idr` freshly
  rebuilt PASS **23:42:42–23:42:44**; transcript says `Building ...R16...`.
  Its zero RSS counter means no nonzero sample before completion, not zero
  memory usage. R16 is still CONDITIONAL through the six open obligations.
- Final micro/check ledger is committed as
  `research-tests/O6-R174-COMPILER-LEDGER.json`: **77** serialized checks,
  **67** clean passes, **5** diagnostic rejections, **5** charged engineering
  interrupts with NO compiler verdict (P6-1/2, Q9-1/2/3). The latter are not
  rejection or uninhabitability proofs. All exact commands and timestamps are
  retained; zero/new-source distinctions are in this audit and each transcript.
- No aggregate R11 run or independent reviewer pass is claimed. The supervisor
  owns any independent review fanout; this is a self-audited producer milestone.

**Fully proved here:** C58's observed-value cure and actual local A/Insert
sealed integration; executable distinct-birth/nonempty-provision schedule,
its uniqueness, actual sorted-prefix guard rejection and genuine registration
protocol (NOT discipline); reached closing-free shape from unchanged O17
inputs and real adjacent derivations; simultaneous reached reinspection;
positive orientation dispatch and derived A/A inequality; genuine local
right-ordinal decrease; actual worklist-selected non-Begin provenance.

**Partial/open:** O17 sorting. Root placement remains OWNER-PAUSED. Early
applicability and actual sealed results for every selected grouping/ordering
case remain open. Reinspection is proved, not preservation of the already-ready
prefix; `BlockBefore`, a global strictly decreasing measure and exact
registration-accounting fold alignment remain open. Shared original/reduced
support order and `CanonicalReplayAccountingLaws` producers remain supplied by
conditional late records, not discharged. O17 body stays **0/3**.

**Merely stated/open:** six inherited holes, **1/4/0/0/1**. O19/O21 bodies and
frozen CP3 proof surfaces are untouched; no new hypotheses/escapes/holes. The
provision candidate is still NOT a full revised-O17 countermodel: Q9 exhausted
3/3 at normalization cost, was entirely reverted and restoration-checked; the
full replay bundle, discipline, shape and O14 inputs are not constructed.
Global freshness is not silently added downstream to CrossTrace/O21, and the
frozen raw CP3 maximal-closing premise remains unverified under uniqueness.

**Next:** owner resolves canonical-form versus actual store-ownership guard
semantics using the Unit-D memo, then separately authorizes any surface work.
For the unchanged surface-independent path, combine the now-correlated actual
selection/non-Begin evidence with early Iter/Finish or registration
applicability, consume sealed results through S17, and prove a global measure
and completed-prefix/accounting preservation before any O17 body attempt.
The large ordinal TTC/import-cost debt remains measured but uncured.
