#!/usr/bin/env bash
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
cd "$ROOT"

required=(
  research-tests/run-r11-suite.sh
  research-tests/DGamma/R11AdjacentPrefixMalicePositive.idr
  research-tests/DGamma/R11AdjacentPrefixCollapsedCertificateNegative.idr
  research-tests/DGamma/R11DeletionCertificateProjectionPositive.idr
  research-tests/DGamma/R11DeletionFillerMapCertificateNegative.idr
  research-tests/DGamma/R11DirectDeletionStepCloneNegative.idr
  research-tests/DGamma/R11GenericRawPlanRepackagerPositive.idr
  research-tests/DGamma/R11GeneratedOnlyRetargetNegative.idr
  research-tests/DGamma/R11TreeOnlyCapitalCloneNegative.idr
  research-tests/DGamma/R11CoherentBothHalvesAssemblyPositive.idr
  research-tests/DGamma/R11CoherentBothHalvesAssemblyNegative.idr
  research-tests/DGamma/R11BridgeWrongGenerationNegative.idr
)
for path in "${required[@]}"; do
  git ls-files --error-unmatch "$path" >/dev/null
  test -s "$path"
done

test ! -e research-tests/run-r10-suite.sh
test ! -e research-tests/DGamma/R10OperationalOriginPlanFixturesPositive.idr

grep -Fq 'data AdjacentSwapOrdinalRelation' \
  research/DGamma/CP5ConfluenceLocalDiamondSpike.idr
grep -Fq 'operationalOrdinalRelation' \
  research/DGamma/CP5ConfluenceLocalDiamondSpike.idr
grep -Fq 'record DeletionOperationalOccurrenceCertificate' \
  research/DGamma/CP5ConfluenceDeletionChainSpike.idr
grep -Fq 'generationSubsequenceSourceOrdinal' \
  research/DGamma/CP5ConfluenceDeletionChainSpike.idr
grep -Fq 'generic repackager, not a fixture' \
  research-tests/DGamma/R11GenericRawPlanRepackagerPositive.idr

python3 - <<'PY'
from pathlib import Path
suite = Path('research-tests/run-r11-suite.sh').read_text()
files = {p.stem for p in Path('research-tests/DGamma').glob('*.idr')}
listed = set()
for key in ('POSITIVE', 'NEGATIVE_SPECS'):
    body = suite.split(key + '=(', 1)[1].split(')', 1)[0]
    for line in body.splitlines():
        line = line.strip()
        if not line or line.startswith('#'):
            continue
        listed.add(line.strip('"').split('|', 1)[0])
if files != listed:
    raise SystemExit(f'suite mismatch: missing={sorted(files-listed)} extra={sorted(listed-files)}')
if len(files) != 53:
    raise SystemExit(f'expected 53 tracked test modules, found {len(files)}')
PY

holes=$(grep -RhoE '\?[A-Za-z0-9_]+' research/DGamma/CP5Confluence*.idr |
  sort -u | wc -l | tr -d ' ')
test "$holes" = 32

test "$(grep -Ec '^\| \*\*O([1-9]|1[0-9]|2[0-3])\*\*' THM73-PLAN.md)" = 23
test "$(grep -Ec '^\| [1-8] \|' THM73-PLAN.md)" = 8
grep -Fq '148–257' THM73-PLAN.md

echo 'R11_TRACKED_CLAIMS_AUDIT=passed'
