# O6 revision 127: restated action-origin design campaign audit

## Scope and coordinate

Design-only shift #125 (overall #179) started from accepted clean HEAD
`5c18e4b624b7594cff89c03fcda2e8ba3d7d6ee1`. It used only the exact renamed
copy `research-tests/DGamma/R48RestatedActionOriginCopyProbePositive.idr`; no
retained proof source or frozen interface was edited.

The final passing disposable source had SHA-256
`932921090be5a852c7d20498bcaf37c8975ee4fe551a837aac09f709ce65501e`
and size 1,550,855 bytes. It and its TTC/TTM artifacts were removed in full.

## Result

The **primary** ladder design passed. The secondary single-input derivation was
therefore not opened.

The successful design does not construct or consume a four-region view. It
turns the canonical `actionOccurrenceOccurs` proof into a positional cursor and
recurses simultaneously over the prefix and that `OccursIn` proof:

- prefix `OccursHere`: retain the identical prefix transition;
- exhausted prefix plus target `OccursHere`: map moved-right to source right;
- exhausted prefix plus `OccursLater OccursHere`: map moved-left to source left;
- two target `OccursLater` constructors: use the sealed suffix origin and
  `adjacentSuffixEmbeddedIndex`/`adjacentSuffixEmbeddedBound`;
- recursive prefix `OccursLater`: prepend one source occurrence and lift the
  ordinal relation with the checked successor lemma.

The `OccursIn` index already contains the exact target trace head. Consequently
there is no independently reconstructed `beforeHead` and no cross-input head
equality to prove. This is precisely the distinction from revisions 124–126.

## Attempt history

### Core positional/action-origin unit

1. **Infrastructure failure:** a local alias for
   `sealedSuffixActionOrigin seal targetLocated` did not retain definitional
   identity with the same opaque call inside
   `sealedSuffixActionOrdinalPreserved`.
2. **Pass:** the suffix branch uses the exact projected expression throughout.
   The positional producer, the located action-origin package, its exact tag and
   ordinal relation, and a one-elimination consumer all checked.

### Exact action-registration payload

1. **Infrastructure failure:** independently pattern matching the per-occurrence
   package in three projection functions reproduced a source proof-token
   mismatch. Conversion of action occurrences back to generated registrations
   also needed explicit eta/ordinal lemmas.
2. **Pass:** producer-owned package projection helpers consume the same package;
   explicit conversion coherence and conversion-ordinal lemmas close generated
   registrations. The final value checks at the exact
   `ActionRegistrationReplayCorrespondence` type, including generation
   bijection, action origin, tag preservation, generated origin, coherence, and
   generation-forward ordinal preservation.

## Ratified retained-unit design

The following private names are proposed (drop only the disposable `Probe`
prefix; preserve the checked argument order and quantities):

1. `adjacentRelationSucc`;
2. `AdjacentPositionalOrigin` and `produceAdjacentPositionalOrigin`;
3. `AdjacentActionOrigin` and `produceAdjacentActionOrigin`;
4. package projections `adjacentPackageSource`, `adjacentPackageTag`, and
   `adjacentPackageOrdinalRelation`;
5. `AdjacentActionOriginProducer`;
6. `adjacentOriginOccurrence`, `adjacentOriginTag`, and
   `adjacentOriginOrdinalRelation`;
7. `actionOccurrenceToGenerated`, its coherence and ordinal lemmas, and the
   generated-origin/coherence/ordinal consumers;
8. `buildAdjacentActionRegistrationCorrespondence`;
9. `adjacentActionRegistrationCorrespondence`.

The exact checked outer signature is:

```idris
private
0 adjacentActionRegistrationCorrespondence :
  (name, key, world, error : Type) -> (value : key -> Type) ->
  (nameEq : DecEq name) -> (keyEq : DecEq key) ->
  (initial, pairFirst, sourceMiddle, sourceSuffixFirst, sourceFinal,
    targetMiddle, targetSuffixFirst, targetFinal :
    SystemState name key value world error) ->
  (prefixTrace : Transitions initial pairFirst) ->
  (sourceFirst : Transition pairFirst sourceMiddle) ->
  (sourceSecond : Transition sourceMiddle sourceSuffixFirst) ->
  (sourceSuffix : Transitions sourceSuffixFirst sourceFinal) ->
  (targetFirst : Transition pairFirst targetMiddle) ->
  (targetSecond : Transition targetMiddle targetSuffixFirst) ->
  (targetSuffix : Transitions targetSuffixFirst targetFinal) ->
  (0 targetFirstAction : (transitionAction targetFirst =
    transitionAction sourceSecond)) ->
  (0 targetFirstTag : (transitionTag targetFirst =
    transitionTag sourceSecond)) ->
  (0 targetSecondAction : (transitionAction targetSecond =
    transitionAction sourceFirst)) ->
  (0 targetSecondTag : (transitionTag targetSecond =
    transitionTag sourceFirst)) ->
  (0 seal : SealedSuffixReplaySpine name key world error value nameEq keyEq
    sourceSuffix targetSuffix) ->
  ActionRegistrationReplayCorrespondence name key world error value
    (appendTransitions prefixTrace
      (MoreTransitions sourceFirst (MoreTransitions sourceSecond sourceSuffix)))
    (appendTransitions prefixTrace
      (MoreTransitions targetFirst (MoreTransitions targetSecond targetSuffix)))
```

`AdjacentActionOrigin` is indexed by the exact target occurrence and contains,
under one constructor elimination:

```idris
sourceOccurrence : LocatedActionOccurrence action sourceTrace
originTagExact : transitionTag (locatedTransition sourceOccurrence) =
  transitionTag (locatedTransition targetOccurrence)
originOrdinalRelation : AdjacentSwapOrdinalRelation
  (transitionCount prefixTrace)
  (locatedActionOrdinal targetOccurrence)
  (locatedActionOrdinal sourceOccurrence)
```

`AdjacentPositionalOrigin` is indexed by the exact `targetSelected` and
`targetOccurs` and contains the source transition, its exact source `OccursIn`,
action/tag equalities, and the ordinal relation between both exact `occursIndex`
values. Neither package accepts a detached source occurrence, source membership,
ordinal relation, or region classifier.

## Construction sites and elimination order

The checked dependency order is:

1. `actionOccurrenceOccurs` converts the caller-owned target occurrence to one
   canonical positional proof.
2. `produceAdjacentPositionalOrigin` eliminates that proof while walking the
   same prefix. The suffix case eliminates exactly one
   `LocatedActionAtOccurrence` and uses the sealed suffix producer.
3. `produceAdjacentActionOrigin` eliminates exactly one positional package and
   one source `LocatedActionAtOccurrence`, producing the correlated action
   package.
4. Each action/tag/ordinal consumer eliminates the same producer-owned package
   through the dedicated projection helpers.
5. Generated-registration conversion is applied only to the source occurrence
   returned by that package; checked eta and ordinal lemmas establish coherence.
6. `buildAdjacentActionRegistrationCorrespondence` fills all six fields of the
   frozen correspondence record.
7. The outer producer supplies `movedRightAction`, `movedRightTag`,
   `movedLeftAction`, `movedLeftTag`, and the sealed suffix spine.

The natural retained declaration site is immediately after
`adjacentSuffixEmbeddedBound`, where every dependency is in scope. There is one
**physical declaration-order risk** for later hole closure: the frozen
`adjacentSwapSuffixSpike` declaration occurs earlier in the file, while the
retained positional foundations currently occur after its hole. Idris does not
permit that earlier RHS to call a later declaration. Landing this design after
the foundations typechecks and preserves every frozen surface, but final body
consumption will need a separately authorized order solution (for example,
moving the unchanged hole declaration below the private foundation block, or an
approved local/inlined wrapper). This campaign did not alter or move the frozen
hole.

## Markers

```text
R127_RESTATED_ACTION_ORIGIN=passed
R127_ONE_ELIM_CONSUMER=passed
R127_ACTION_REGISTRATION_PAYLOAD=passed
R127_SECONDARY_SINGLE_INPUT=not_run_primary_passed
R127_DISPOSABLE_COPY_PROBE_REMOVED=passed
```

## Status

- direct positional action origin: **passed**;
- exact tag and adjacent ordinal relation: **passed**;
- generated registration origin/coherence/renaming: **passed**;
- exact `ActionRegistrationReplayCorrespondence`: **passed**;
- secondary single-input route: **not run**;
- retained proof edits: **none**;
- declaration-order integration: **requires a ruling before final RHS use**;
- holes: **20**, split **6/4/8/1/1**;
- all frozen capital and production surfaces: **unchanged**.
