#!/usr/bin/env bash
set -euo pipefail

ROOT=$(cd "$(dirname "$0")/.." && pwd)
cd "$ROOT"
IDRIS2=${IDRIS2:-idris2}

# Populate production TTCs in a fresh archive, then check every research unit
# with one Idris process at a time. Research tests remain outside dgamma.ipkg.
"$IDRIS2" --build dgamma.ipkg
TTC_ROOT=$(find build/ttc -mindepth 1 -maxdepth 1 -type d | head -n 1)
if [ -z "$TTC_ROOT" ]; then
  echo "No build/ttc version directory found" >&2
  exit 1
fi
export IDRIS2_PATH="$ROOT/$TTC_ROOT${IDRIS2_PATH:+:$IDRIS2_PATH}"

SPIKES=(
  CP5ConfluenceLocalDiamondSpike
  CP5ConfluenceDeletionChainSpike
  CP5ConfluenceCanonicalSortSpike
  CP5ConfluenceRenamingCompositionSpike
  CP5ConfluenceCrossTraceSpike
)
for module in "${SPIKES[@]}"; do
  echo "SPIKE $module"
  "$IDRIS2" --source-dir research --check "research/DGamma/$module.idr"
done

POSITIVE=(
  R10ProvenanceProjectionPositive
  R10ActorBlockDecompositionFixturesPositive
  R11GenericRawPlanRepackagerPositive
  R11AdjacentPrefixMalicePositive
  R11DeletionCertificateProjectionPositive
  R11CoherentBothHalvesAssemblyPositive
  R4OADiamondApplication
  R4ScannerProducerConsumers
  R4VestigialSimultaneous
  R6FourFiberStatic
  R6GeneratedChildSafetyPositive
  R6OccurrenceFoldPositive
  R6OperationalOccurrenceFoldPositive
  R6OuterSchedulesPositive
  R6ScannerRetainedFixturesPositive
  R6ScannerThirdOrdering
  R6TwoIntermediateStatic
  R7DeletionBoundariesPositive
  R7OperationalThreadingPositive
  R8AuthenticationProjectionPositive
  R8BridgeAuthenticatedDirectionPositive
  R8FullPipeline
  R9CoordinateBoundaryPositive
  R9WholeBlockShiftedAliasContradictionPositive
  R9WholeBlockSingletonPositive
  R9WholeBlockTwoByOnePositive
  R9WholeBlockTwoByTwoPositive
)
for module in "${POSITIVE[@]}"; do
  echo "POSITIVE $module"
  "$IDRIS2" --source-dir research-tests --check \
    "research-tests/DGamma/$module.idr"
done

# Each expected failure has its own mandatory diagnostic fragment and source
# declaration. A generic dependent error is no longer enough to pass the suite.
NEGATIVE_SPECS=(
  "R11AdjacentPrefixCollapsedCertificateNegative|targetOrdinal and sourceOrdinal|collapsedPrefixCannotInhabitOrdinalCertificate"
  "R11DeletionFillerMapCertificateNegative|generationSubsequenceSourceOrdinal|fillerMapCannotConstructDeletionCertificate"
  "R11DirectDeletionStepCloneNegative|occurrences and alternate|cloneDeletionStepWithAlternateMap"
  "R11GeneratedOnlyRetargetNegative|alternateGenerated occurrence|retargetOnlyGeneratedHalf"
  "R11TreeOnlyCapitalCloneNegative|capitalCanonicalSchedule and replacement|replaceOnlyCapitalSchedule"
  "R11CoherentBothHalvesAssemblyNegative|alternate and MkActionRegistrationReplayCorrespondence|coherentBothHalvesCannotEnterProducerAssembly"
  "R11BridgeWrongGenerationNegative|generatedGenerationBijection sameInputs|arbitraryRightBirthCannotSatisfyBridgeGeneration"
  "R10AdjacentSwapMapCloneNegative|operationalOccurrenceCorrespondence|replaceActualSwapOccurrenceMap"
  "R10ReductionMapCloneNegative|closingFreeDeletionOccurrenceFold|replaceReductionOccurrenceMap"
  "R10DeletionStepMapCloneNegative|alternate and step .deletionOccurrenceCorrespondence|replaceDeletionStepOccurrenceMap"
  "R10SortedMapCloneNegative|finiteDerivationOccurrenceCorrespondence|replaceSortedOccurrenceMap"
  "R10CoherentBothHalvesCapitalNegative|alternate and canonicalOccurrenceCorrespondence capital|coherentBothHalvesCannotBecomeCapitalOutput"
  "R6MixedScheduleNegative|leftCapital and otherLeft|mixedLeftSchedule"
  "R6OldPollutionNegative|CertifiedActorPermutation|oldPollutionReachesO20"
  "R6OuterPollutionNegative|selectedActorPermutation|wrapPollutedOuter"
  "R6SafetyDetachmentNegative|firstPremises and secondPremises|detachSafetyFromCurrentState"
  "R6ScannerWrongGenerationNegative|12 and 0|conflateSameRawNameBirths"
  "R6StaleQuotientNegative|firstOp and secondOp|staleQuotient"
  "R7DuplicateLabelNegative|not a valid impossible case|duplicateLabelUnique"
  "R8BlockPrefixIdentityNegative|alternateRoot|replaceBlockLabelRootByArbitraryMap"
  "R8BridgeWrongBirthNegative|generationForward|replaceBridgeRightOccurrenceWithoutGenerationEquation"
  "R8PublicScheduleCannotReachBridgeNegative|CanonicalSchedule|publicScheduleCannotEnterAuthenticatedBridge"
  "R8WholeBlockShiftedNodeNegative|0 and 1|relabelExactSameNodeAtNextPosition"
  "R8WrongOccurrenceBridgeNegative|first and second|detachBridgeOccurrenceRelation"
  "R8WrongTraceBridgeNegative|operationalTargetFinal and otherFinal|wrongTraceBridge"
  "R8ZeroDerivationOperationalStepNegative|FiniteAdjacentSwapDerivation|zeroDerivationOperationalStepStillAccepted"
)
for specification in "${NEGATIVE_SPECS[@]}"; do
  IFS='|' read -r module expected symbol <<<"$specification"
  echo "NEGATIVE $module"
  output=$(mktemp)
  set +e
  "$IDRIS2" --source-dir research-tests --check \
    "research-tests/DGamma/$module.idr" >"$output" 2>&1
  status=$?
  set -e
  if [ "$status" -eq 0 ]; then
    cat "$output" >&2
    echo "Expected rejection unexpectedly elaborated: $module" >&2
    rm -f "$output"
    exit 1
  fi
  if ! grep -Fq "$expected" "$output" || ! grep -Fq "$symbol" "$output"; then
    cat "$output" >&2
    echo "Wrong rejection boundary for $module; expected '$expected' at '$symbol'" >&2
    rm -f "$output"
    exit 1
  fi
  rm -f "$output"
done

echo "R11_REPRODUCIBLE_SUITE=passed"
