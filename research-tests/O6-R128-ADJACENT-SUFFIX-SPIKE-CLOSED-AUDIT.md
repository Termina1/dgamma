# O6 revision 128: adjacent suffix spike closure audit

## Scope and coordinate

Landing shift #126 (overall #180) started from accepted design boundary
`decbb4ad9b284f462a3f0290f09eb780fa11081f`. It landed only the ratified
revision-127 direct-positional occurrence chain, performed the separately
authorized declaration relocation, assembled the existing closed replay
capital into `AdjacentSwapResult`, and filled only
`adjacentSwapSuffixSpike_rhs`.

No production source, package manifest, CP3 source/blob, revision-21 surface,
closed replay-bundle field, or other research hole was changed.

## Retained units and commits

| Unit | Attempts | Commit | Result |
|---|---:|---|---|
| successor relation plus positional package/producer | 1 each | `065c0d0` | passed |
| action package/producer | 1 | `3b8820c` | passed |
| exact producer-owned projections | 1 | `7310c23` | passed |
| generated conversion/coherence/ordinal chain | 2 command attempts | `e151552` | passed; first proof check passed, shell command ended on a quote error before R16/commit |
| generic action-registration payload builder | 1 | `b316c4c` | passed |
| outer adjacent action-registration correspondence | 2 command attempts | `021a215` | passed; first command ended in shell parsing before Idris invocation |
| authorized position-only relocation | 2 infrastructure attempts | `9cb7243` | passed; first extraction included `public export` and measured 1197 rather than the governed 1183-byte subregion, with no edit |
| operational occurrence fold | 2 infrastructure attempts | `01a93b8` | passed; first Python edit used a string as a Path and made no edit |
| complete `AdjacentSwapResult` producer | 1 | `54e0f22` | passed |
| hole RHS | 2 | `c94813e` | passed; first body named implicit endpoint indices unavailable in point-free scope, second inferred them with `_` |

The successor lemma was committed separately at `27c1e52`; the positional
producer followed at `065c0d0`. This tightly coupled 158-line foundation commit was explicitly
accepted by the supervisor; history was not rewritten. Strict one-unit/one-
commit cadence resumed at unit 3.

## Direct positional occurrence construction

The landed chain is exactly the revision-127 design:

1. `actionOccurrenceOccurs` derives canonical positional membership from the
   caller-owned target occurrence.
2. `produceAdjacentPositionalOrigin` recurses over the prefix and that exact
   `OccursIn` proof: prefix identity, moved-right to source right, moved-left to
   source left, and suffix through `sealedSuffixActionOrigin` plus
   `adjacentSuffixEmbeddedIndex`/`adjacentSuffixEmbeddedBound`.
3. `produceAdjacentActionOrigin` reconstructs the exact source located
   occurrence and owns its tag and `AdjacentSwapOrdinalRelation`.
4. Exact package projections retain proof identity.
5. Generated-registration conversion/coherence/ordinal lemmas fill the frozen
   `ActionRegistrationReplayCorrespondence`, using
   `adjacentGenerationBijection`.
6. `produceAdjacentOperationalOccurrenceFold` seals decompositions,
   correspondence, and ordinal semantics.
7. `produceAdjacentSwapResult` eliminates `produceAdjacentInvariantReplay`
   once and combines its already-closed fields with
   `adjacentWholeSameExternal` and the occurrence fold.

No four-region view, caller-selected source occurrence, detached occurrence
proof, or cross-input transition equality remains.

## Authorized relocation transcript

The supervisor authorized a position-only move because Idris rejects references
to the retained positional foundations from the former earlier hole position.
Duplication and RHS-local copies were explicitly rejected.

The governed pre-fill subregion starts at `0 adjacentSwapSuffixSpike :` and ends
at the hole RHS. Before and after relocation:

```text
RELOCATION_BEFORE_BYTES=1183
RELOCATION_BEFORE_SHA256=e6d0c2d669355e5b7bef9efea1707f5853c708deb888bafe5770ba40dbd15a41
RELOCATION_AFTER_BYTES=1183
RELOCATION_AFTER_SHA256=e6d0c2d669355e5b7bef9efea1707f5853c708deb888bafe5770ba40dbd15a41
RELOCATION_BYTE_IDENTITY=passed
RELOCATION_NEW_LINE=27319
RELOCATION_HOLES=20
```

The dedicated commit `9cb7243` contains only that position move. `public export`
was moved with the declaration; the governed 1183-byte region itself was
byte-identical.

## Hole fill and new frozen surface

Immediately before filling:

```text
PREFILL_CURRENT_BYTES=1183
PREFILL_CURRENT_SHA256=e6d0c2d669355e5b7bef9efea1707f5853c708deb888bafe5770ba40dbd15a41
PREFILL_ARCHIVE_MATCH=passed
```

The fill replaced only `?adjacentSwapSuffixSpike_rhs` with a lambda whose body is
a direct call to `produceAdjacentSwapResult`. The statement prefix, from
`0 adjacentSwapSuffixSpike :` through `adjacentSwapSuffixSpike =` inclusive,
remains identical to the archived pre-fill region:

```text
POSTFILL_STATEMENT_PREFIX_BYTES=1154
POSTFILL_STATEMENT_PREFIX_SHA256=3aae5a9fbc5b14e0411b4a91e557a6f3dc68c9a6282b9ec2b3fc658cec337adf
POSTFILL_STATEMENT_PREFIX_IDENTITY=passed
POSTFILL_ONLY_RHS_SUBSTITUTED=passed
```

The new full theorem-definition region is now frozen as:

```text
POSTFILL_FULL_DEFINITION_BYTES=1470
POSTFILL_FULL_DEFINITION_SHA256=2d01486bf953f11191b758ac3cfb5722d1d02b1a192b6e552adc8a3f58199ecf
```

The archived pre-fill region remains at
`/tmp/grind180-relocation-after.region` for provenance during this review.

## Hole status and stop order

The fill changed the research-hole total exactly from 20 to 19, with module
split:

```text
6/4/8/0/1
```

`CP5ConfluenceLocalDiamondSpike.idr` now has zero holes. Per the critical
standing order, no other hole or obligation was opened after this reduction.
The complete full-validation transcript follows at the gate, and work stops for
the commissioned scoped adversarial review.
