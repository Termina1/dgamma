# O6 revision 94: checked owner-separation countermodel stop

## Scope

Grind shift #102 (overall #156) executed the owner-separation campaign authorized
at the accepted revision-93 gate. It stopped before adding any research proof or
opening the pair RAR. The proposed separation conclusion is false for the frozen
input surface: two checked O-Retire steps for the same owner form an aligned
source pair and an aligned moved pair satisfying revision-21 registration
safety.

No frozen or production declaration changed.

## Unit 1: classification/independence expected-failure pin

The temporary probe `/tmp/R93ClassificationAloneNegative.idr` attempted:

```text
CandidateRegistrationSwapSafety left right ->
TraceIndependent ... (left :: right :: []) ->
Not (transitionActor left = transitionActor right)
```

Attempt 1 failed before the intended boundary because `DecEq` was not imported.
Attempt 2 reached the intended body and was rejected with:

```text
When unifying:
  TraceIndependent ... (MoreTransitions left
    (MoreTransitions right NoTransitions))
and:
  Void
Mismatch between: TraceIndependent ... and Void.
```

Marker:

```text
R93_CLASSIFICATION_INDEPENDENCE_DISTINCT_EXPECTED_FAILURE=passed
```

The probe is not retained.

## Countermodel to the authorized separation lemma

Choose any well-formed state containing a fiber at owner `a`. The executable
semantics of O-Retire is:

```idris
applyAction (ORetire a) state = case lookupFiber a (registry state) of
  Nothing => Nothing
  Just fiber => Just (ORetireTag,
    MkSystemState (worldState state)
      (replaceBinding a (retireFiber fiber) (registry state)))
```

and:

```idris
retireFiber (MkFiber component parent retired table lifecycle) =
  MkFiber component parent True table lifecycle
```

Consequently retirement is operationally idempotent:

1. the first checked O-Retire changes the flag to `True`;
2. the fiber remains present;
3. a second checked O-Retire succeeds and leaves the state unchanged.

The existing concrete R45 fixture already supplies a checked first retirement:

```text
r45SourceRetire : Transition r45SourcePairFinal r45SourceFinal
transitionAction r45SourceRetire = ORetire 1
```

A temporary countermodel probe established definitionally:

```text
applyAction @{r45NameEq} @{r45KeyEq} (ORetire 1)
  r45SourceFinal = Just (ORetireTag, r45SourceFinal)
```

(`r93RetireAgainRaw = Refl` was accepted before later declarations in the probe
failed.) Thus the pair is:

```text
r45SourcePairFinal --ORetire 1--> r45SourceFinal
                   --ORetire 1--> r45SourceFinal
```

Use that same checked pair as the moved pair. Then:

- source alignment is `AlignedStep ... (AlignedStep ... AlignedEnd)`;
- moved alignment is identical;
- moved-right action/tag and moved-left action/tag equalities are all `Refl`;
- `CandidateOrchestrationOrchestration` is inhabited by two
  `PaperRetireStep Refl` classifiers;
- both insertion-safety functions are vacuous because an equality between
  `ORetire 1` and `OInsert ...` eliminates by constructor disjointness;
- swapped final effects and controls are reflexive;
- the swapped endpoint is the same well-formed state;
- both actor projections reduce to `1`, so owner equality is `Refl`.

Therefore the authorized statement

```text
AlignedTransitions sourcePair ->
AlignedTransitions movedPair ->
CandidateRegistrationSwapSafety left right ->
Not (actionOwner leftAction = actionOwner rightAction)
```

cannot be inhabited. Adding exact checked transitions, moved action/tag
alignment, endpoint equivalence, or `TraceIndependent` does not repair it.
`TraceIndependent` is universally conditional on a supplied inequality between
selected transformation actors; it does not state that trace occurrences have
distinct actors.

A second temporary proof package attempted to package the full concrete local
diamond. It exhausted its three probe attempts on explicit-boundary issues
(private R45 well-formed evidence, missing `Data.Maybe`, and finally an omitted
explicit `{name,key,world,error,value : Type}` binder in a copied checked-target
helper). Under the permanent budget rule it was removed rather than repaired a
fourth time. This elaboration exhaustion does not weaken the semantic
countermodel: the crucial idempotent second raw retirement was already accepted,
and the frozen CP5 module itself contains the total checked-target-well-formed
theorem at lines 3254–3274 used throughout the checked replay construction.

Temporary probes are not retained.

## Why pair RAR cannot continue under revision-93 plan

The distinct branch remains mechanical:

- source-left foreign lookup transports the right owner from `middle` to
  `first`;
- moved-right foreign lookup transports the left owner from `first` to
  `swappedMiddle`;
- the frozen activation/orchestration singleton RARs then feed cross-cons
  generator/stage localization.

But applying those lookup transports globally requires the false separation
lemma. The same-owner retirement countermodel is not an invalid or malformed
bare transition: it is admitted by executable checked semantics and by the
revision-21 O/O safety constructor.

No ad-hoc same-owner branch was started. That would exceed the accepted #101
ruling and requires a new design review.

## Required design campaign

A viable next design must handle owner equality rather than prove it impossible.
Candidate directions, requiring probes and review:

1. **Distinct/equal split inside the pair RAR.** Keep the accepted foreign-lookup
   and singleton-RAR construction in the `No` branch of `decEq owners`. In the
   `Yes` branch, classify which checked reversible pairs can exist. O-Retire /
   O-Retire must be handled; repeated L-Advance/L-Iter may also be viable.
2. **Same-owner identity/refl pair RAR.** Prove that every viable same-owner
   checked source/moved pair has the required generator-map and exact iterator
   outcome correspondence without foreign lookup transport. This must be
   action/tag-specific; endpoint equivalence alone is insufficient.
3. **Action-specific lookup-free singleton RARs.** O-Retire maps are identity,
   so a same-owner retirement pair should not require source/moved lookup
   equality. Investigate whether repeated L-Advance can use the exact runtime
   package and producer-correlated stage order directly.
4. **Surface revision only if unavoidable.** Retaining original producer
   distinctness would exclude the countermodel, but adding it to
   `LocalRelationalDiamond`, `CandidateRegistrationSwapSafety`, or the frozen
   adjacent signature is currently unauthorized.

The next gate should first enumerate all viable same-owner combinations under
both checked orders. It must include positive O-Retire/O-Retire and repeated
L-Advance probes plus expected failures for impossible mixed action pairs.

## Status

- classification/independence negative pin: **closed as expected failure**;
- proposed checked separation lemma: **refuted by same-owner O-Retire/O-Retire**;
- full temporary diamond package: **removed after three elaboration attempts**;
- runtime package and both singleton RAR families: **unchanged, closed, frozen**;
- pair RAR: **not opened**;
- whole RAR / field 9: **open**;
- fields 1–8: **closed**;
- fields 10–15 foundations: **closed; population pending**;
- occurrence fold/result/body: **unopened**;
- holes: **20**, split **6/4/8/1/1**.

The accepted **2–10 implementation-shift** band is suspended at this semantic
design stop. It should not be narrowed or widened until a same-owner pair-RAR
design is checked.

## Isolation

The 1183-byte adjacent interface and SHA
`e6d0c2d669355e5b7bef9efea1707f5853c708deb888bafe5770ba40dbd15a41`,
revision-20/21 surfaces, all revision-93 capital, production `src/`,
`dgamma.ipkg`, and CP3 remain unchanged. No hole, escape hatch, postulate,
public field, or detached capital was added.
