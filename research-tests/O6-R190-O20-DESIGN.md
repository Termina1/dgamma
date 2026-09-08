# R190 O20 design gate (Unit 0; no proof declarations)

## Authenticated baseline

Start 2026-09-08T13:21:47Z, branch `cp5-thm73-scoping`, HEAD
`4c6cfb176251e205d8ee0b98f287adff8e33d2da`. Tracked clean, only permitted
paper/ and immutable review file untracked; Idris2 0.8.0; no orphan.
Attempt cutoff16:41:47Z, safe final gate17:06:47Z, timeout17:21:47Z.
Detached seeded S0-1 checked the REAL CrossTrace in4.156s, max sampled
RSS5,409,024KiB, own70/70 Building line; no cache deletion. R190 wrappers
are adapted from R189, retain48GiB limit and missing/empty/own-line guards.
Read R189 audit/clause map FIRST, both exact types, R146, R183/184/186/187
selector inventories, R180/181/183/184 synchronization, R175 Unit C and
WorkMeasure. Entire extracted paper read through3883 including references.

## Exact protected types (source at start)

### `selectOperationalCanonicalPermutationSpike` — lines 277–298

```idris
0 selectOperationalCanonicalPermutationSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (leftTrace : Transitions initial leftFinal) ->
  (rightTrace : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace
    rightTrace) ->
  (leftCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq leftTrace) ->
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq rightTrace) ->
  (0 leftUnique : UniqueRawNameInsertions name key world error value nameEq keyEq leftTrace) ->
  (0 rightUnique : UniqueRawNameInsertions name key world error value nameEq keyEq rightTrace) ->
  (0 leftRightGeneratedMatched : GeneratedOrchestrationMatched name key world error value nameEq
    leftTrace rightTrace (generatedGenerationBijection sameInputs)) ->
  (matching : MappedCanonicalSupportOrders name key world error value protocol
    nameEq keyEq leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)) ->
  CertifiedOperationalCanonicalPermutation name key world error value protocol
    nameEq keyEq leftTrace rightTrace sameInputs leftCapital rightCapital matching
```

### `canonicalSchedulesConvergeSpike` — lines 537–561

```idris
0 canonicalSchedulesConvergeSpike :
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (protocol : RegistrationProtocol key value world error) ->
  {initial, leftFinal, rightFinal : SystemState name key value world error} ->
  (leftTrace : Transitions initial leftFinal) ->
  (rightTrace : Transitions initial rightFinal) ->
  (sameInputs : SameOrchestrationModuloGenerated nameEq keyEq leftTrace
    rightTrace) ->
  (leftCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq leftTrace) ->
  (rightCapital : IndependentCanonicalSchedule name key world error value protocol
    nameEq keyEq rightTrace) ->
  (0 leftUnique : UniqueRawNameInsertions name key world error value nameEq keyEq leftTrace) ->
  (0 rightUnique : UniqueRawNameInsertions name key world error value nameEq keyEq rightTrace) ->
  (0 leftRightGeneratedMatched : GeneratedOrchestrationMatched name key world error value nameEq
    leftTrace rightTrace (generatedGenerationBijection sameInputs)) ->
  {matching : MappedCanonicalSupportOrders name key world error value protocol
    nameEq keyEq leftTrace rightTrace
    (currentNameBijection (endpointRenaming sameInputs))
    (canonicalSchedule leftCapital) (canonicalSchedule rightCapital)} ->
  (operational : CertifiedOperationalCanonicalPermutation name key world error
    value protocol nameEq keyEq leftTrace rightTrace sameInputs leftCapital
      rightCapital matching) ->
  CanonicalConvergenceResult name key world error value protocol nameEq keyEq
    leftTrace rightTrace sameInputs leftCapital rightCapital operational
```

Selector body is299–300; convergence body562. Signature SHA256s are
`8db1b940921a3c0eb877b2112c25d5325f9058444f7d0a901a66965ffece0540` and
`4ed416287b6b068a2cf78208f4718c98f0e1084d4520a74dc8c67097af345f59`.
No statement/body/type rehome proposed. Census4=1/2/0/0/1.

## Field-by-field capital and hard gaps

### Selector: CP5O19SurfaceSpike:782–815

| Output | Available capital | Still to construct |
|---|---|---|
| selectedActorPermutation | CertifiedActorPermutation Done/Step; finite actual adjacent candidates; exact member/BeforeIn facts | fixed inverse-renamed right goal ranks, exact same set/uniqueness, finite directed complete selection loop |
| operationalTargetFinal / Trace | REAL o19ActualOperationalBlockSwap consumes every selected safe pair | fold actual results while choosing, not pure permutation then realize |
| operationalTargetBlocks | full blockSwapBlocks from same O19 result | retain at each reached selection, terminal order EXACTLY inverse-renamed right |
| operationalTargetPremises | full blockSwapPremises | same-chain threading, plus separate original/canonical/reached uniqueness |
| selectedPermutationRealized | OperationalActorDone/Step; whole nonempty certified O19 derivation | simultaneous certificate/result/recursive realized tail with strict descent |

R184 o20SelectSafeAdjacentBlocks produces both NoGeneratedChild clauses,
authoritative blocks/order, genuine empty gap and right-first Begin at the
pre-left cut. R187 o20SelectOrientedSafeBlocks checks all candidates against
a fixed target; o20OrientedCannotReverse excludes ONLY the immediate inverse.
o20OrientedSupportIncomparable still requires BOTH orders at the SAME state.
R189 closes the actual O19 step; its full finite derivation transports unique
via blockSwapUniqueInsertions; capitalCanonicalUniqueInsertions supplies the
initial unique. O19 has NO A9 field: GeneratedOrchestrationMatched stays on
the exact original pair, not manufactured on a reached trace.

### Convergence: CrossTrace:474–532 / RenamingComposition:1761–1819

permutedLeftExecution is already exact constructor assembly from
operationalPermutationEndpoint and operationalPermutationSameExternalInputs.
Its occurrence map is the sealed actual operational fold. The bridge is:

| Fixed-bijection bridge clause | Accepted capital | Remaining obligation |
|---|---|---|
| ambient equality | RenamedRuntimeEffects, empty origin, actual frame propagation | paired whole executions up to both final cuts |
| pointwise effect table equality | stronger ordered-binding synchronization, insert/set/replacement lemmas | global table preservation across paired Begin/Advance/Finish and gaps |
| ALL-name MaybeFiberRelatedBy | supported selected-actor invariant, one-sided endpoint packets, actual Begin observations | complete paired episode induction AND unsupported/absent/retired names |
| ALL generated registration origins and exact birth triangle | supportedReplayedBirthBridge has the EXACT clause at supported children; A9 + both original uniques | unsupported generated children, canonical presence/retirement and exact original/replayed origins |

SupportedCanonicalEpisodeSynchronization is a TYPE plus genuine zero instance;
R181 B8 supplies a nonzero insertion successor at actual supplied cuts, not
selection/alignment of all cuts. D1–D6 derive actual ViewRelatedBy from actual
successful resolvers and ordered global table agreement. R183 C4–C8 select
actual supported paired blocks and cuts conditional on already-real operational
capital. These CAN be consumed in convergence (operational is an input), but
NOT to manufacture selector's operational prerequisite. R184 C4–C8 observe
each real Begin's component/dependencies/view and propagate Begin effects;
same component/list identification and pre-cut effects still need production.
R179/R180 one-sided supported packets assert NO cross-side control equality.
R175 C4 original withdrawal branches belong to O21 and remain PARKED.

## Measure choice

Use R175 rankInversions on the FINITE ACTOR WORKLIST, ranked by positions in
one FIXED inverse-renamed right support order. This is a block-level instance
of the same proven global inversion algebra, not a resetting selected-actor
debt. Each actual adjacent actor inversion drops exactly1. The action-worklist
measure would drop a positive block product and needs rank projection through
all repeated generated/lifecycle actions; that extra O17-facing machinery is
unnecessary for O20, whose step already swaps whole blocks. It does NOT erase
barriers: safety still demands an actual zero gap, and completeness must derive
that from accepted input placement/reached provenance. No root hoisting or
frozen O17 integration is proposed. Finite supportOrder + DecEq name supplies
finite ranks and decidable search; membership excludes out-of-goal sentinels.

## Exact remaining selector obligations (R183 ten-item reconciliation)

1. Choose a compatible COMMON REFERENCE relation on the surviving supported
   actors under the fixed bijection and produce both linearizations. Do NOT
   strengthen this to full original-left SupportPath transfer: the existing
   CanonicalSupportTransport and bridge comments already exclude that through
   withdrawn intermediates. Canonical/reached restriction needs proof.
2. Construct fixed-goal rank membership, injectivity, exact finite-set matching
   and uniqueness, and pure finite linear-extension completeness.
3. Orient an actual adjacent inversion toward that fixed goal and connect its
   BeforeIn witness to rankCrossing=1, not merely no immediate reverse.
4. Actual reached authoritative block selection: positive capital exists;
   must re-run against EACH actual reached decomposition.
5. Both child exclusions: positive capital exists; semantic completeness must
   derive success on a selected legal inversion.
6. Right-first guard at pre-left cut: positive capital exists; derive success
   from common-order semantics, original provenance and actual matched views.
7. Empty actual gap: positive capital exists; derive from accepted input
   placement and preserve through replay, never discard immovable root events.
8. O19 is CLOSED; fold its same trace/blocks/full bundle/whole derivation and
   derive reached uniqueness from exact source uniqueness.
9. Produce rank decrease simultaneously with chosen pair + O19 + reached state;
   total loop recurses on that finite measure; retain exact fixed goal.
10. Prove exhaustive-search completeness and terminal equality. Nothing alone
    is neither sortedness nor a proof there are no legal candidates.

## Exact remaining convergence obligations

B1 actual paired execution/cut alignment at the prescribed order; B2 whole
pre-cut ambient and ordered-table agreement; B3 same component/dependency-list
and actual Begin view/control successor; B4 real corresponding Advance outcomes
and accumulator/continuation successors; B5 actual Finish and terminal supported
control; B6 external/generated gap synchronization; B7 unsupported/absent/retired
control classification; B8 unsupported generated birth clause with exact fixed
bijection/origin triangle; B9 all-name table and control assembly, then only the
existing bridge/result constructor. No O21 withdrawal theorem consumed.

## Ranked plan and first disposable probe (gate request)

1. **Open selector first, probe-first (<=3 checks).** Size the one-step seam
   by consuming an explicit real O20OrientedSafeSwap, invoking the now-real O19
   result, and asking for reached common-reference linearization plus fixed-goal
   inversion descent. Isolate the unavailable conversion as a native diagnostic;
   do not add it as a public hypothesis, assert existence, or call either O20
   hole. Remove probe fully and archive all snapshots/transcripts. Then <=24
   producer-owned single-declaration micro-units: rank/descent algebra and
   simultaneous one-step result first, semantic reselection/completeness next.
   Body only when actual total loop is committed, fresh <=3 attempts.
2. **Convergence after A gate reply or A stop.** Disposable four-clause sizing
   probe, <=16 real producer micro-units directed to actual synchronization
   successors/birth coverage; body ONLY if all four clauses are produced.
3. Suspected gap: countershape + fixture then gate BEFORE any surface change.
   No full original-state common-order transfer restatement; no unsupported
   child assumption substituted for a bridge proof. Structural wall is audited
   park; two3/3 in one seam stop that unit, then next authorized branch.

No production/API, LocalDiamond, O17/root-phase, O21 withdrawal, O19, or
adjacentSwapSuffixSpike edit. All constructive witnesses quantity0. No new
hole, unsafe/partial/postulate/with, local aliases/computed existentials or
scalar Refl observer on nested builders. Independent review remains required.
