# O6 R142 — Deletion O9 crossing-check budget stop audit

## Scope and verdict

**Verdict: STOP O9 under route C; Step 1 was inconclusive after its disposable
3-attempt budget.**

R142 began from checked research coordinate `661548b` on
`cp5-thm73-scoping`. Production remained frozen: no path under `src/` and no
`dgamma.ipkg` content was edited. The O9 body was not opened and remains at
**0/3** attempts. No scoped-to-raw coercion was proposed or implemented.

The supervisor's crossing-branch ruling required evidence before choosing
between:

- broadening R137 to overlapping activations; and
- keeping R137 and deriving pre-interval crossing exclusion from prior
  unload/reliance history.

The first required unit was a disposable concrete check: make a consumer open
while the selected provider is Active, retain its committed provider view
across the provider's leave, and ask the evaluator to unload the provider while
the consumer remains installed. A successful unload would seed the overlapping
countershape; `Nothing` at the unload reliance guard would seed the operational
refutation.

## Why this is the exact O9 obstruction

Frozen `crossingActivationExcludesSelectedProvider` is the semantic use of
`NoDependentClosingEpisode` in the selected-center replay. The foreign
lifecycle occurrence is inside the selected closed episode, but
`closingOccurrenceGivesLocatedActivation` only retains an installed prefix from
the consumer's `LBegin` target to that occurrence. Its public type does **not**
show that the consumer's opening lies in `closedInside selectedEpisode`.

R137's `GenerationScopedClosingStart` requires exactly that stronger inside
opening. Therefore `selectedNoDependentClose candidate` cannot be applied to
the production crossing branch when the consumer activation began before the
selected opening. This is distinct from R140's already-audited raw/scoped
adapter mismatch.

The post-close route is different. It constructs
`DirectProviderFrameEvidence` from the selected plan's exact Inactive fiber, so
its raw predicate is administrative plumbing through a generic evidence
eliminator rather than semantic input. Removing that plumbing research-side was
separately authorized, but it does not solve the selected-center crossing case.

## Step-1 disposable fixture and attempt accounting

The disposable module was
`research-tests/DGamma/R142O9CrossingCountershapeCheck.idr`. It reused the
checked R137 model and assembled these intended states:

1. `ActorB` is `Reloading` with committed view `LinkKey -> ActorA`;
2. `ActorA` is Active and then retired;
3. `ActorA` successfully performs `LLeave`, becoming Unloading; and
4. the attempted `LUnload ActorA` should be blocked while `ActorB` remains
   installed and `relied ActorA registry = True`.

The independent budget was exhausted without a checked fixture:

1. **Attempt 1/3.** The module was rejected first because
   `r137FirstAActiveRetired` is private. Subsequent evaluator equations stayed
   unreduced.
2. **Attempt 2/3.** The private fiber was replaced by
   `retireFiber r137FirstAActive`. Cross-module `applyAction`, `installedAt`, and
   `relied` equations still did not normalize through the imported explicit
   dictionaries and opaque model constants.
3. **Attempt 3/3.** Local dictionary aliases were introduced, but the disposable
   spelling omitted the direct `Decidable.Equality` import. The aliases were
   consequently rejected and all intended evaluator equalities remained
   unchecked.

The failure is an elaboration/probe-budget failure, not evidence for either
calculus outcome. In particular, the source tree contains strong generic
reliance facts such as `committedSelectedContradictsUnload`, but the ruling
required the concrete countershape check first; citing an existing theorem is
not a substitute for the missing checked disposable fixture.

After attempt 3 the fixture source and its terminal TTC/TTM were deleted. No
unchecked countershape claim is retained.

## Administrative direct-evidence probe

The separately authorized administrative-removal unit also used a fresh 3/3
budget. A research helper attempted to factor the already public
`foreignLifecycleGuardFrameFromProviderExclusion` path, thereby avoiding the
raw predicate after direct occurrence-local provider exclusion was available.

1. **Attempt 1/3.** The first full replay join lacked the direct import exposing
   `providerCandidate`; the lower lifecycle dispatcher was reported
   inaccessible.
2. **Attempt 2/3.** Importing the lifecycle core exposed `providerCandidate`, but
   `SelectedSurvivorCleanInactive` still lacked its defining direct import and
   the dispatcher remained inaccessible.
3. **Attempt 3/3.** The helper was narrowed to the guard-frame join alone and a
   control-core import was added. The clean-Inactive type was still not exposed
   from its defining selected-boundary module, and the provider-frame helper
   itself was reported inaccessible at this research boundary.

The whole probe was restored. No helper, import delta, unsafe escape, or new
hole remains. A future authorized retry would need its own differently scoped
unit and must begin from explicit defining-module imports rather than respelling
this exhausted helper.

## Consequence

The supervisor's route-C condition is met: Step 1 is inconclusive after its
budget. Therefore this run does **not** choose route A or B, does not revise the
R137/O8 surface, does not clone CP4 proof modules, and does not continue to O10
or later DeletionChain obligations.

The remaining honest next step is a new supervisor-authorized unit that either:

- constructs the concrete evaluator blocker with definitions local enough to
  normalize; or
- replaces the concrete-first gate with an explicitly authorized generic
  application of the existing installed-consumer/unload contradiction.

Only after that evidence may the campaign select overlapping scoping or the
pre-interval operational theorem.

## Fresh validation and invariants

After restoring both disposable units and deleting only terminal artifacts:

```text
idris2 --check --source-dir src --source-dir research \
  research/DGamma/CP5ConfluenceDeletionChainSpike.idr
2/2: Building DGamma.CP5ConfluenceDeletionChainSpike
exit 0

idris2 --check --source-dir src --source-dir research \
  --source-dir research-tests \
  research-tests/DGamma/R7DeletionBoundariesPositive.idr
1/1: Building DGamma.R7DeletionBoundariesPositive
exit 0
```

The research-hole census is unchanged at **16**, split **5/4/6/0/1**
(CanonicalSort/CrossTrace/DeletionChain/LocalDiamond/RenamingComposition). O9 is
still the single `enrichDeletionChainStepSpike_rhs` hole and remains at 0/3 body
attempts.

No `believe_me`, `assert_total`, postulate, `unsafePerformIO`, `partial`, or
`covering` annotation was added. Production diff from `34b21c9` remains empty;
the R141 generation-scoped surface revision and exact start-ordinal helper
remain the retained boundary.
