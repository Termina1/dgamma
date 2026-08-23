#!/usr/bin/env bash
set -euo pipefail

ROOT=$(cd "$(dirname "$0")/.." && pwd)
cd "$ROOT"
IDRIS2=${IDRIS2:-idris2}

# Populate production TTCs in a fresh archive, then compile every research unit
# one process at a time.  Research tests remain outside dgamma.ipkg.
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
)
for module in "${POSITIVE[@]}"; do
  echo "POSITIVE $module"
  "$IDRIS2" --source-dir research-tests --check \
    "research-tests/DGamma/$module.idr"
done

NEGATIVE=(
  R10AdjacentSwapMapCloneNegative
  R10ReductionMapCloneNegative
  R10SortedMapCloneNegative
  R10CoherentBothHalvesCapitalNegative
  R6MixedScheduleNegative
  R6OldPollutionNegative
  R6OuterPollutionNegative
  R6SafetyDetachmentNegative
  R6ScannerWrongGenerationNegative
  R6StaleQuotientNegative
  R7DuplicateLabelNegative
  R8BlockPrefixIdentityNegative
  R8BridgeWrongBirthNegative
  R8PublicScheduleCannotReachBridgeNegative
  R8WholeBlockShiftedNodeNegative
  R8WrongOccurrenceBridgeNegative
  R8WrongTraceBridgeNegative
  R8ZeroDerivationOperationalStepNegative
)
for module in "${NEGATIVE[@]}"; do
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
  if ! grep -Eq "Mismatch between|Can't solve constraint|not a valid impossible" \
    "$output"; then
    cat "$output" >&2
    echo "Rejection did not reach an intended dependent boundary: $module" >&2
    rm -f "$output"
    exit 1
  fi
  rm -f "$output"
done

echo "R10_REPRODUCIBLE_SUITE=passed"
