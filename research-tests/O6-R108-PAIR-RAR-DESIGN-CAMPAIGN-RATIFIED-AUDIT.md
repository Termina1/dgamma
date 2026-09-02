# O6 revision 108: pair-RAR design campaign ratified

## Scope

Design shift #116 (overall grind #170) resumed from accepted HEAD `ebbd2ca`.
It obeyed the revision-107 escalation ruling: all Idris proof work was confined
to disposable `/tmp/dgamma-grind170-*` trees; no retained proof, frozen producer,
revision-19–21 surface, `ReplayInvariantBundle`, `LocalRelationalDiamond`,
`R101FourAlignedHeadViews`, production source, package file, or CP3 file was
edited. Checks ran serially with one `idris2` process and fresh CP5 TTC/TTM
removal before each check.

The required ladder was run in order. There is no semantic gap. The third shape
checks through endpoint handling, both singleton RARs, cons RAR, the final exact
`RelationalReplayCorrespondence`, and `r97Field9ConcreteCapitalConsumer` (the
retained `a44d184` append-composition chain).

## Probe 1 — consistent aligned checks, direct/no-let

The first disposable shape eliminated outer source alignment, used no source
transition let aliases, and used the alignment-owned `leftChecked` /
`rightChecked` consistently in source singleton legs and cons. It still exposed
opaque moved-record projection identity when the moved pair was eliminated
separately:

```text
Can't solve constraint between:
  Fired ... movedRightActionValue movedRightTagValue movedRightChecked
and:
  diamond .movedRight
```

A follow-up ordering variant reached the same projection boundary while
eliminating the action/tag equality. This rejects separate source/moved
alignment eliminations as the retained representation; it does not reject the
pair RAR semantically.

## Probe 2 — preserve original source indices

The no-source-alignment route retained the two original source `Fired` proofs.
It reached the final correspondence but could not recover a common transition
dictionary from independently stored source constructors:

```text
Mismatch between: keyEq and rightKeyEq.
```

This confirms that source alignment must be consumed by one producer-owned
dependent view. No dictionary equality or proof irrelevance is admissible.

## Probe 3 — producer-owned quantity-0 checked identity

The successful disposable design uses two deliberately asymmetric boundaries:

1. A source pair GADT consumes the exact two-step `AlignedTransitions` once and
   returns both source actions/tags and both checked equations as constructor
   indices. Its checked fields are explicitly quantity 0.
2. A low-level moved-pair helper patterns the two exact moved `Fired`
   transitions and their exact two-step alignment in one clause. It then
   eliminates producer-owned action/tag equalities, but **does not identify the
   moved endpoints with source endpoints**. The original source checked proofs
   remain on source singleton legs; the exact moved checked proofs remain on
   target singleton legs.

Keeping endpoints distinct is the decisive cure. The Iter/Iter branch derives
its second activation lookup equality from the producer-owned
`swappedMiddle = middle` equality. The Retire/Retire branch needs no lookup
transport. Both branches then call the frozen activation/orchestration
singleton RAR twice and join with `consRelationalReplayCorrespondence`.

The checked temporary artifact was:

```text
/tmp/dgamma-grind170-probe3m/helper.idr
SHA-256 dcab26c16ab49f9d3ba1b8cbbfc47783cde71d10e2eba30fdd2b19719de73702
```

The final direct check rebuilt the temporary CP5 module visibly and emitted:

```text
1/1: Building DGamma.CP5ConfluenceLocalDiamondSpike
O6_R114_PROBE3_Q0_CHECKED_IDENTITY_PACKAGE=passed
O6_R114_PROBE3_OWNED_MOVED_EXACT_INDICES=passed
O6_R114_PROBE3_FULL_PAIR_RAR=passed
O6_R114_PROBE3_R97_FIELD9_CONSUMER=passed
O6_R114_PROBE3_A44D184_EXACT_TYPE=passed
```

The successful log SHA-256 is
`9fe3442fe4d3786ecf7f4f10d19da50226e5ee051c129ca50f8afc27115ad4d2`.
The final consumer has exactly the frozen field-9 target:

```idris
RelationalReplayCorrespondence name key world error value original
  (appendTransitions tracePrefix
    (MoreTransitions (movedRight diamond)
      (MoreTransitions (movedLeft diamond) replayedSuffix)))
```

No postulate, proof irrelevance, transition equality, dictionary equality,
stage equality, tag-only transport, or escape hatch is used.

## Ratified retained-unit design

The next implementation shift may land one fresh private unit, with these exact
parts and no wider surface change:

1. `PairAlignedIdentity` — private indexed GADT over `left`, `right`, and their
   exact two-step alignment. Constructor checked fields are quantity 0.
2. `pairAlignedIdentity` — one total producer, patterning both source `Fired`
   constructors and both alignment steps in one clause.
3. `lookupStateBackward` — private fully explicit helper deriving owner lookup
   equality from `target = source`; it is used only by the second Iter/Iter
   singleton.
4. `pairRARFromOwnedMovedIdentity` — private low-level helper. Inputs are the
   exact source action/tag/checked values, exact moved transitions, exact moved
   alignment, four producer-owned cross action/tag equations, two endpoint
   equations, and the frozen R102 dispatch. Its clause directly patterns both
   moved `Fired` constructors and both moved alignment steps. It eliminates only
   the four action/tag equations before constructing the singleton/cons RAR;
   endpoint equations remain explicit.
5. `equalOwnerPairRAR` — thin wrapper: eliminate `PairAlignedIdentity` once,
   eliminate R102 once, compose the frozen moved/source cross equations, and
   call the low-level helper.

Implementation invariants:

- use original source checked proofs only on source transitions;
- use moved checked proofs only on target transitions;
- never transport one checked proof into the other's trace index;
- preserve moved endpoint indices in the target trace;
- use endpoint equality only for the Iter/Iter second-owner lookup;
- use no source/moved transition let aliases;
- keep all proof fields/locals quantity 0;
- use explicit state indices and direct `Fired` constructors;
- do not retain the campaign's exploratory wrapper records;
- do not change any frozen/public surface.

After this fresh unit passes visible fresh CP5 and R16, field 9 may be populated
in its own implementation unit by passing `equalOwnerPairRAR` to
`r97Field9ConcreteCapitalConsumer`. Fields 10–15 and body assembly remain the
following unit(s).

## Status and band

- B6 dispatcher: **complete and frozen**;
- mandatory pair-RAR design campaign: **complete and ratified**;
- pair-RAR implementation: **not retained; authorized next in a fresh unit**;
- field 9: **append composition closed; population unopened**;
- fields 10–15: **foundations retained; population unopened**;
- occurrence fold/result/body: **unopened**;
- holes: **20**, split **6/4/8/1/1**;
- nominal implementation band: **1–2 shifts remaining**; this mandatory
  design-only campaign is excluded from that count.

There is no semantic stop. At O6 body closure (`20 -> 19` holes), work must stop
immediately for the already mandated adversarial review.

## Manifest and isolation

```text
NO_FROZEN_SURFACE_CHANGE_REQUIRED
```

The frozen `adjacentSwapSuffixSpike` remains 1183 bytes with SHA-256
`e6d0c2d669355e5b7bef9efea1707f5853c708deb888bafe5770ba40dbd15a41`.
Production `src/`, `dgamma.ipkg`, CP3, revisions 19–21, B6, and all prior
capital remain unchanged. Only this design audit and the plan status are
retained from shift #116.
