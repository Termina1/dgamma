# R198 Unit B: exact ORIGINAL→canonical/replayed control boundary

Source freeze `ae510d70`;16 micro-units,16 first-attempt native PASS,16 guarded
source commits. No D5 retry, C attempt, production edit or extra premise on a
protected statement. All proofs are total/erased; the observation producer and
its two runtime MaybeFiber values are executable. No unsafe/hole was added.

## Produced, not assumed

`CP5O20CanonicalMaybeControlSpike` has13 declarations:

* B1 `o20WithdrawnNameActuallyAbsent` eliminates the existing two withdrawal
  alternatives and returns their actual canonical lookup-Nothing evidence.
* B2 `o20AbsentControlTarget` is a standalone public primitive control absence
  eliminator. Equivalent frozen helpers are private; their visibility and bytes
  are untouched. No deletion-chain or O19/O21 body was copied/called.
* B3 `O20CanonicalControlDisposition` separates actual withdrawn membership
  with canonical Nothing from outside-membership with FULL primitive controls.
  The kept case includes absent/absent; it does NOT claim physical presence.
* B4 `O20CanonicalControlObservation` stores both observed MaybeFiber values,
  erased equations to BOTH actual `lookupFiber`s, and that disposition.
* B5/B6 `o20CanonicalControlsAtDecision` / `o20ObserveCanonicalControls`
  produce that packet for ANY name from one actual canonical endpoint relation.
  Both primitive lookups and the library `isElem` decision carry their own
  equations. The Dec is eliminated BEFORE packet construction. All lookup
  applications explicitly instantiate name/key/value/world/error/nameEq.
* B7/B8/B9 derive actual canonical absence from actual original absence using
  the SAME observation packet, without reconstructing equality between packets.
* B10 `o20CanonicalAbsentFromOriginal` obtains that absence from the actual
  `canonicalEndpoint (canonicalSchedule capital)` of accepted independent
  canonical capital; no membership/support/vestigial premise is required.
* B11 uses the actual replay endpoint's own `replayedControls` field.
* B12 `o20PermutedAbsentFromOriginal` obtains replayed absence from the actual
  original lookup and the supplied `PermutedCanonicalExecution`; canonical
  and replay endpoint relations are projected, not passed as new oracles.
* B13 `o20BothOriginalAbsentReplayedControls` proves the conditional
  removed/removed primitive controls at **exactly** `expectedBridgeBijection
  sameInputs`, from BOTH original absences (including the opposite current
  image). It does NOT derive that second absence from the first.

Thus an ALL-NAME ONE-TRACE observer exists, but an ALL-NAME TWO-ENDPOINT current
map cut does not. These are different claims. B6 is not the requested
all-name actual-current-map endpoint producer, nor does B13 quantify away
its two original absence hypotheses. No application of `o20SupportedBridgeFromOwnedCut` exists.

## Exact name classes and remaining producer obligations

Write `c = expectedBridgeBijection sameInputs`, `x` for the queried left name,
`y = renameForward c x`, `L0/R0` for ORIGINAL endpoints, `LC/RC` for actual
canonical endpoints, and `LP` for the actual operational target. The needed
conclusion is `MaybeFiberRelatedBy c (lookupFiber x LP) (lookupFiber y RC)` for
EVERY x, not just names in either support set.

| ORIGINAL class | Actual observations/facts available | Still needed for final ALL-name controls |
|---|---|---|
| Supported present x | R194 supported-birth original/replay attachment and non-vestigial history/current agreement; B6 owns exact original/canonical lookup equations and conditional complete controls | Assemble the actual attachment, actual history cut and endpoint observations at LC→LP and RC; neither R194 nor B6 alone is the cross-trace control producer |
| Present unsupported, with history/current agreement | B6 still computes the actual membership decision and BOTH MaybeFiber values; if outside withdrawals, full identity-name original→canonical controls, otherwise canonical Nothing | Carry the agreement and actual observations through the supplied canonical/replay transformations; unsupportedness alone is not withdrawal or vestigial evidence |
| Present unsupported, history/current mismatch (vestigial) | R195 `o20DisagreementVestigial` owns the FULL original vestigial packet; B6 produces the real membership branch and lookups | Prove disappearance/withdrawal at the actual canonical endpoint from actual canonical construction, and absence at the opposite CURRENT image (plus the symmetric obligation). No such producer exists |
| Originally removed/absent x | B10 and B12 now produce `lookupFiber x LC = Nothing` and `lookupFiber x LP = Nothing` | Prove `lookupFiber y RC = Nothing` from actual accepted opposite-image classification. Original right absence suffices by B10/B13, but a present vestigial image needs the previous missing canonical-disappearance lemma |

The candidate missing **canonical vestigial disappearance** obligation must
consume the literal original trace, actual independent canonical capital,
actual final generation environment and full original vestigial witness, then
produce the actual canonical lookup-Nothing (or actual withdrawal membership,
which is sufficient). Its strength must be checked against retained-open versus
closing generation dispositions; no unstated axiom asserting it was added.
The separate **current-image canonical absence** obligation must use the actual
current endpoint renaming to classify y and discharge its canonical lookup;
absence on x or equality of supported-name maps is not enough.

For each side, B6's exact alternatives are:

```
Elem x withdrawn
  => lookupFiber x canonicalFinal = Nothing
Not (Elem x withdrawn)
  => FiberControlMaybeRelated (lookupFiber x originalFinal)
                             (lookupFiber x canonicalFinal)
```

Nothing here implies `originalVestigial x => Elem x withdrawn`. The missing
premise cannot be hidden in a callback producing successor controls, a supplied
`O20AllNameCut`, a support-only view, or a repaired weaker convergence statement.
The original→canonical→replayed observation functions do not change any maps.

## Checked fixtures and their precise limits

`R198CanonicalMaybeControlPositive` has three declarations:

* B14 `r198RemovedCanonicalAbsence`: native R192/R195 six-edge removed child
  owns actual original Nothing. The result is canonical Nothing for ANY supplied
  independent canonical capital. Such capital is a visible input; this is not
  an independently packaged accepted canonicalization fixture.
* B15 `r198ClosingRawIdentityEndpoint`: the RAW `CanonicalEndpointRelation`
  permits identity with empty withdrawals at R193's physically present vestigial
  original endpoint. No `IndependentCanonicalSchedule` is constructed. This is
  a compiled boundary of that endpoint predicate, not a countermodel of full
  accepted capital or of the protected convergence theorem.
* B16 `r198ClosingRawControlObservation`: runs the executable B6 observer on
  that actual endpoint/relation and simultaneously retains actual child1
  presence and actual current-image2 absence from R193. The canonical endpoint
  predicate alone therefore does not force vestigial withdrawal. The actual
  canonical construction must supply the missing fact.

Direct imports include the defining calculus/context/state/fixture modules and
`Data.List`, `Data.List.Elem`, `Data.Maybe`, `Data.Nat`, `Decidable.Equality` where
normalization is used. No frozen visibility change or exhausted-statement retry.

## Disposition

B is PARTIAL and capped. New absence producers discharge a concrete tractable
class, not the universal present-vestigial/current-image seam. A has no accepted
synchronization producer. C remains untouched/ineligible; D5 generic consumer
remains exhausted. Final inherited validation and independent reviewer gate
are separate obligations, not mathematical completion claims.
