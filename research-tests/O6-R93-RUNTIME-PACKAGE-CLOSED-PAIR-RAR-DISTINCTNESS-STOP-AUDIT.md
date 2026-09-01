# O6 revision 93: runtime package and singleton RARs closed; pair distinctness stop

## Scope

Grind shift #101 (overall #155) implemented the ratified revision-92 singleton
stage design and continued through both action-family singleton RAR producers.
All retained units passed visible fresh source checking and the R16 assembly
consumer at their commit boundary. Work stopped before opening a cross-cons pair
RAR: the next required activation lookup transport exposes a distinct-owner
premise that is not a field of the frozen `LocalRelationalDiamond` or of
`TraceIndependent`.

## Retained implementation

### Runtime package and LAdvance family

1. `SingletonAdvanceRuntimePackage` and
   `singletonAdvanceRuntimePackage` — `8eecfc7`, fresh attempt 1.
   - the original target stage appears only as an index;
   - every payload/proof field is quantity 0;
   - Here exposes exact component, parent, retired flag, table, remaining
     program, accumulator, view, target lookup, current step/rest/suffix, actor
     equality, and exact runtime outcome;
   - Later is eliminated by `noOccurrenceInEmpty`.
2. `consumeSingletonAdvanceRuntimePackage` — `2d71e0f`, attempt 1.
   It eliminates the package once, reindexes the actor, transports the exact
   target lookup backward with frozen `04fda32`, and constructs the source stage
   plus `MkLocatedSingletonAdvanceStageReplay`, preserving the original
   `selected,targetStage` result indices.
3. `singletonAdvanceStageFamilyFromOwnerLookup` — `5a21dd3`, attempt 1.
   This is the authorized one-clause `SingletonAdvanceStageReplayFamily`
   wrapper.

No stage equality, dictionary equality, reconstructed target-stage index, or
change to the frozen locator was introduced.

### Activation singleton RAR

4. `activationSingletonMapsRelated` — `ba36213`, attempt 2. Attempt 1 supplied
   the relational input where `partialEffectMapForRespects` expects explicit
   left/right states; adding `x y inputs` closed the unit. It uses
   `activationTransitionMapOriginCong` and the frozen map-respect theorem.
5. `lBeginNotAdvance` — `7eba6fb`, attempt 1.
6. `activationSingletonRAR` — `438a892`, attempt 1.
   - LBegin uses `singletonNonAdvanceRAR`;
   - LIter/LFinish use the new stage family and `singletonAdvanceRAR`;
   - every branch obtains map relation from the exact activation classifier and
     owner lookup equality.

### Orchestration singleton RAR

7. `orchestrationSingletonMapsRelated` — `337cfce`, attempt 1, using
   `orchestrationTransitionMapOriginCong` plus map respect.
8. `orchestrationSingletonRAR` — `52cbbde`, attempt 1. OInsert, ORetire, and
   ORemove use `singletonNonAdvanceRAR` with constructor disjointness from
   LAdvance.

These declarations are private research capital. Frozen/public surfaces are
unchanged.

## Mechanical cross-cons construction now available

The checked singleton RARs are exactly the local inputs for a swapped pair:

- source `right` singleton -> target `movedRight` singleton;
- source `left` singleton -> target `movedLeft` singleton.

The existing `JointLocatedConsTargetGenerator` and
`JointLocatedConsTargetStage` locators support an internal cross-cons producer:

- target Here should locate through the right singleton RAR and **prepend** the
  source left head;
- target Later should locate through the left singleton RAR and **widen** it by
  the source right tail.

The generator functions
`prependLocatedReplayGeneratorOrigin`/`widenLocatedReplayGeneratorOrigin` and
the corresponding iterator-stage functions already provide all required map
and exact-outcome lifting. No new semantic map or iterator theorem is needed
for this cross-cons layer.

## Stop: activation lookup needs owner separation

Constructing either activation singleton RAR needs an exact equality of owner
lookups at its source and moved starting states.

For the right action this is:

```text
lookup owner(right) (registry pairMiddle) =
lookup owner(right) (registry pairFirst)
```

and normally follows from `transitionForeignLookup` across source `left` given:

```text
Not (owner(left) = owner(right)).
```

For the left action the analogous equality crosses `movedRight` from
`pairFirst` to `swappedMiddle` and needs the reverse separation.

The currently available frozen capital does not directly provide this fact:

- `TraceIndependent` supplies commutation and iterator stability **conditional
  on** a caller-provided `Not (left = right)`; it does not assert distinctness;
- `CandidateRegistrationSwapSafety` retains classifiers in A/A but no owner
  separation; mixed and O/O fields retain only their specific parent/child and
  inserted-child exclusions;
- `LocalRelationalDiamond` has action/tag projections and checked moved-pair
  alignment, but no distinct-owner field;
- `pairExternalOrder` applies only to external orchestration order and is not a
  universal activation-owner separation theorem.

The genuine four local-diamond producers received a distinct-actor premise and
used it internally, but revision-21 deliberately froze the public diamond
surface without retaining that premise. It is therefore not legitimate to call
`transitionForeignLookup` from the pair-RAR producer until separation is
reconstructed from other checked evidence.

## Required next design/lemma campaign

Do not add a field to `LocalRelationalDiamond` and do not change the frozen
adjacent signature. The next campaign should prove or refute an internal
checked lemma of this shape:

```text
AlignedTransitions sourcePair ->
AlignedTransitions movedPair ->
CandidateRegistrationSwapSafety left right ->
Not (actionOwner leftAction = actionOwner rightAction)
```

The proof must classify all four revision-21 cases and use the exact checked
source/moved transitions:

1. A/A: show that two same-owner paper activation steps cannot both run in the
   source order and the reversed checked order; case-split Begin/Iter/Finish and
   lifecycle applicability.
2. A/O and O/A: combine orchestration action shape with the mixed safety fields
   where necessary; otherwise use checked applicability in both orders.
3. O/O: use inserted-child distinctness for insert/insert and exact checked
   applicability for insert/retire/remove combinations; do not overclaim that
   parent-safety fields alone imply actor inequality.

A small expected-failure probe should confirm that classification or
`TraceIndependent` alone cannot project distinctness. The positive probe must
produce the exact `Not` type from aligned checked source and moved pairs before
implementation resumes.

If that theorem checks, the remaining pair RAR is mechanical:

1. derive source/moved lookup equalities with `transitionForeignLookup`;
2. build the two singleton RARs through the revision-21 classifier;
3. cross-cons generator and stage locators;
4. assemble the pair RAR;
5. compose prefix + pair + sealed suffix.

## Status

- runtime package/producer: **closed**;
- exact consumer: **closed**;
- stage-family wrapper: **closed**;
- activation singleton RAR: **closed**;
- orchestration singleton RAR: **closed**;
- pair RAR: **open at checked owner-separation lemma; cross-cons layer unopened**;
- whole RAR / field 9: **open**;
- fields 1–8: **closed and frozen**;
- fields 10–15 foundations: **closed; population pending**;
- occurrence fold/result/body: **unopened**;
- holes: **20**, split **6/4/8/1/1**.

The accepted **2–10 shift** implementation band is held provisionally rather
than reduced: one implementation shift has closed the ratified representation
and singleton RARs, but the newly explicit separation lemma requires a scoped
design/lemma gate before the cross-cons implementation can be estimated safely.

## Isolation

The 1183-byte adjacent interface, SHA
`e6d0c2d669355e5b7bef9efea1707f5853c708deb888bafe5770ba40dbd15a41`,
revision-20/21 surfaces, production `src/`, `dgamma.ipkg`, and CP3 remain
unchanged. No hole, escape hatch, postulate, public field, or detached output
capital was added.
