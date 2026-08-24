#!/usr/bin/env bash
set -euo pipefail

ROOT=$(cd "$(dirname "$0")/.." && pwd)
cd "$ROOT"
IDRIS2=${IDRIS2:-idris2}
FRESH=0
case "${1:-}" in
  "") ;;
  --fresh) FRESH=1 ;;
  *) echo "usage: $0 [--fresh]" >&2; exit 2 ;;
esac

SPIKES=(
  CP5ConfluenceLocalDiamondSpike
  CP5ConfluenceDeletionChainSpike
  CP5ConfluenceCanonicalSortSpike
  CP5ConfluenceRenamingCompositionSpike
  CP5ConfluenceCrossTraceSpike
)

POSITIVE=(
  R15O5AlignedProducerPositive
  R14O4AlignedProducerPositive
  R13O3AlignedProducerPositive
  R10ProvenanceProjectionPositive
  R10ActorBlockDecompositionFixturesPositive
  R9WholeBlockSingletonPositive
  R9WholeBlockTwoByOnePositive
  R9WholeBlockTwoByTwoPositive
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
  R16ConfluenceTheoremAssemblyPositive
  R16EndpointControlsImpossibilityPositive
  R17FullResultImpossibility
  R18ExternalOrderProducerPositive
  R18OccurrenceFoldArbitrarySuffixImpossibilityPositive
  R19SealedReplayCertificateScopingPositive
  R19SuffixFreeFullAdjacentCertificatePositive
  R19CrossStateRetireReplayProbePositive
  R20CorrectedSealedReplayEnvelopeScopingPositive
  R20WholeBundleAlignmentGapPositive
  R21MovedOutputAlignmentScopingPositive
  R9CoordinateBoundaryPositive
  R9WholeBlockShiftedAliasContradictionPositive
)

# Each expected failure has its own mandatory diagnostic fragment and source
# declaration. A generic dependent error is not enough to pass the suite.
NEGATIVE_SPECS=(
  "R19SealedReplayConstructorNegative|ScopedReplayEnd is private|forgedScopedReplaySpine"
  "R20WholeBundleMovedAlignmentNegative|storedRightKeyEq and keyEq|localDiamondCannotSupplyMovedAlignment"
  "R21CandidateIndependentDictionaryNegative|storedRightKeyEq and keyEq|forgeCandidateFromIndependentDictionaries"
  "R21RepeatedIterProducerAlignmentNegative|storedRightKeyEq and storedLeftKeyEq|repeatedIterPremisesCannotSupplyMovedAlignment"
  "R21WholeBundleQuietTransportNegative|source and target|relationalEndpointDoesNotDirectlyTransportQuiet"
  "R17WrongLookupControlNegative|Nothing and with block in lookupEntries|wrongLookupControlPairRejected"
  "R15O5IndependentDictionaryNegative|alternateKeyEq and keyEq|independentEarlyOrchestrationCannotAlign"
  "R14O4IndependentDictionaryNegative|alternateKeyEq and keyEq|independentMixedPairCannotAlign"
  "R13O3IndependentDictionaryNegative|alternateKeyEq and keyEq|independentDictionariesCannotAlign"
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

TEMP_OUTPUTS=()
cleanup_outputs() {
  if [ "${#TEMP_OUTPUTS[@]}" -gt 0 ]; then
    rm -f "${TEMP_OUTPUTS[@]}"
  fi
}
trap cleanup_outputs EXIT

# Idris 2 v0.8.0 can emit declaration errors while returning zero. Every unit
# expected to succeed is therefore accepted only when its exit status is zero,
# its captured diagnostics contain no Error:, and (in fresh mode) it emits its
# own successful build marker.
SUCCESSFUL_BUILD_MARKERS=0
run_successful_unit() {
  local category=$1
  local module=$2
  shift 2
  local output
  output=$(mktemp)
  TEMP_OUTPUTS+=("$output")
  set +e
  "$@" >"$output" 2>&1
  local status=$?
  set -e
  if [ "$status" -ne 0 ] || grep -Fq 'Error:' "$output"; then
    cat "$output" >&2
    echo "$category $module failed: exit=$status or Error: diagnostic present" >&2
    exit 1
  fi
  if [ "$FRESH" -eq 1 ]; then
    if ! grep -Fq "Building DGamma.$module" "$output"; then
      cat "$output" >&2
      echo "$category $module did not emit its required fresh build marker" >&2
      exit 1
    fi
    SUCCESSFUL_BUILD_MARKERS=$((SUCCESSFUL_BUILD_MARKERS + 1))
  fi
  cat "$output"
}

# Package population is hardened against the same status-zero Error: behavior,
# but does not contribute to the 5+41 research-unit marker count.
run_package_build() {
  local output
  output=$(mktemp)
  TEMP_OUTPUTS+=("$output")
  set +e
  "$IDRIS2" --build dgamma.ipkg >"$output" 2>&1
  local status=$?
  set -e
  if [ "$status" -ne 0 ] || grep -Fq 'Error:' "$output"; then
    cat "$output" >&2
    echo "Production package build failed: exit=$status or Error: diagnostic present" >&2
    exit 1
  fi
  cat "$output"
}

run_package_build
TTC_ROOT=$(find build/ttc -mindepth 1 -maxdepth 1 -type d -print -quit)
if [ -z "$TTC_ROOT" ]; then
  echo "No build/ttc version directory found" >&2
  exit 1
fi
export IDRIS2_PATH="$ROOT/$TTC_ROOT${IDRIS2_PATH:+:$IDRIS2_PATH}"

if [ "$FRESH" -eq 1 ]; then
  # Idris writes these direct --check interfaces into the package TTC root, not
  # source-relative research directories. Delete exactly the 5+76 suite units.
  all_modules=("${SPIKES[@]}" "${POSITIVE[@]}")
  for specification in "${NEGATIVE_SPECS[@]}"; do
    IFS='|' read -r module _ _ <<<"$specification"
    all_modules+=("$module")
  done
  for module in "${all_modules[@]}"; do
    rm -f "$TTC_ROOT/DGamma/$module.ttc" "$TTC_ROOT/DGamma/$module.ttm"
  done
fi

for module in "${SPIKES[@]}"; do
  echo "SPIKE $module"
  run_successful_unit SPIKE "$module" \
    "$IDRIS2" --source-dir research --check "research/DGamma/$module.idr"
done

for module in "${POSITIVE[@]}"; do
  echo "POSITIVE $module"
  run_successful_unit POSITIVE "$module" \
    "$IDRIS2" --source-dir research-tests --check \
    "research-tests/DGamma/$module.idr"
done

for specification in "${NEGATIVE_SPECS[@]}"; do
  IFS='|' read -r module expected symbol <<<"$specification"
  echo "NEGATIVE $module"
  output=$(mktemp)
  TEMP_OUTPUTS+=("$output")
  set +e
  "$IDRIS2" --source-dir research-tests --check \
    "research-tests/DGamma/$module.idr" >"$output" 2>&1
  status=$?
  set -e
  if [ "$status" -eq 0 ]; then
    cat "$output" >&2
    echo "Expected rejection unexpectedly elaborated: $module" >&2
    exit 1
  fi
  if ! grep -Fq "$expected" "$output" || ! grep -Fq "$symbol" "$output"; then
    cat "$output" >&2
    echo "Wrong rejection boundary for $module; expected '$expected' at '$symbol'" >&2
    exit 1
  fi
done

if [ "$FRESH" -eq 1 ]; then
  if [ "$SUCCESSFUL_BUILD_MARKERS" -ne 46 ]; then
    echo "Expected 46 fresh successful-unit markers, saw $SUCCESSFUL_BUILD_MARKERS" >&2
    exit 1
  fi
  echo "R11_FRESH_SUCCESSFUL_BUILD_MARKERS=$SUCCESSFUL_BUILD_MARKERS"
fi

echo "R11_REPRODUCIBLE_SUITE=passed"
