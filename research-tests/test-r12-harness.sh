#!/usr/bin/env bash
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
cd "$ROOT"
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

# Reproduce the Idris 0.8.0 false-success shape: package population succeeds,
# while the first research check prints Error: and exits zero. The hardened
# runner must reject it before continuing to the next unit.
mkdir -p "$TMP/error-zero/research-tests"
cp research-tests/run-r11-suite.sh "$TMP/error-zero/research-tests/"
cat >"$TMP/error-zero/fake-idris2" <<'FAKE'
#!/usr/bin/env bash
set -e
if [ "${1:-}" = "--build" ]; then
  mkdir -p build/ttc/fake/DGamma
  exit 0
fi
echo 'Error: injected status-zero declaration diagnostic'
exit 0
FAKE
chmod +x "$TMP/error-zero/fake-idris2"
set +e
(
  cd "$TMP/error-zero"
  IDRIS2="$TMP/error-zero/fake-idris2" \
    research-tests/run-r11-suite.sh --fresh
) >"$TMP/error-zero.log" 2>&1
status=$?
set -e
if [ "$status" -eq 0 ]; then
  cat "$TMP/error-zero.log" >&2
  echo 'Runner falsely accepted an Error: diagnostic with status zero' >&2
  exit 1
fi
grep -Fq 'Error: injected status-zero declaration diagnostic' "$TMP/error-zero.log"
grep -Fq 'SPIKE CP5ConfluenceLocalDiamondSpike failed' "$TMP/error-zero.log"
if grep -Fq 'SPIKE CP5ConfluenceDeletionChainSpike' "$TMP/error-zero.log"; then
  cat "$TMP/error-zero.log" >&2
  echo 'Runner continued after the injected first-unit error' >&2
  exit 1
fi
echo 'R12_ERROR_ZERO_FALSE_PASS_REJECTED=passed'

# Regression for revision 74's stale-TTC failure mode. R16 assembly checks are
# additional evidence only: every touched CP5 helper must first be checked by a
# direct fresh source build that demonstrably rebuilds its module. A no-op check
# which silently selects an existing TTC through IDRIS2_PATH is not evidence.
# The fresh runner must delete the seeded spike TTC before invoking Idris.
mkdir -p "$TMP/stale-ttc/research-tests"
cp research-tests/run-r11-suite.sh "$TMP/stale-ttc/research-tests/"
cat >"$TMP/stale-ttc/fake-idris2" <<'FAKE'
#!/usr/bin/env bash
set -e
if [ "${1:-}" = "--build" ]; then
  mkdir -p build/ttc/fake/DGamma
  printf 'stale' > build/ttc/fake/DGamma/CP5ConfluenceLocalDiamondSpike.ttc
  exit 0
fi
if printf '%s\n' "$*" | grep -Fq 'CP5ConfluenceLocalDiamondSpike.idr'; then
  if [ -e build/ttc/fake/DGamma/CP5ConfluenceLocalDiamondSpike.ttc ]; then
    echo 'Error: stale CP5 TTC survived --fresh cleanup'
    exit 0
  fi
  printf 'observed' > fresh-cp5-rebuild-observed
  echo 'Error: intentional stop after observing fresh CP5 rebuild boundary'
  exit 0
fi
exit 0
FAKE
chmod +x "$TMP/stale-ttc/fake-idris2"
set +e
(
  cd "$TMP/stale-ttc"
  IDRIS2="$TMP/stale-ttc/fake-idris2" \
    research-tests/run-r11-suite.sh --fresh
) >"$TMP/stale-ttc.log" 2>&1
status=$?
set -e
if [ "$status" -eq 0 ]; then
  cat "$TMP/stale-ttc.log" >&2
  echo 'Runner falsely accepted the intentional fresh-boundary stop' >&2
  exit 1
fi
test -f "$TMP/stale-ttc/fresh-cp5-rebuild-observed"
if grep -Fq 'stale CP5 TTC survived' "$TMP/stale-ttc.log"; then
  cat "$TMP/stale-ttc.log" >&2
  echo 'Runner allowed stale CP5 TTC reuse at a fresh source boundary' >&2
  exit 1
fi
grep -Fq 'intentional stop after observing fresh CP5 rebuild boundary' \
  "$TMP/stale-ttc.log"
echo 'R12_STALE_CP5_TTC_REUSE_REJECTED=passed'

# Reproduce the old auditor's set-laundering bug in a temporary tracked tree.
# The repaired list audit must reject the duplicate before broad validation.
mkdir -p "$TMP/duplicate"
cp -R research "$TMP/duplicate/"
cp -R research-tests "$TMP/duplicate/"
cp THM73-PLAN.md "$TMP/duplicate/"
(
  cd "$TMP/duplicate"
  git init -q
  git add research research-tests THM73-PLAN.md
  python3 - <<'PY'
from pathlib import Path
path = Path('research-tests/run-r11-suite.sh')
text = path.read_text()
needle = '  R10ProvenanceProjectionPositive\n'
if text.count(needle) != 1:
    raise SystemExit('positive mutation target is not unique')
path.write_text(text.replace(needle, needle + needle))
PY
  git add research-tests/run-r11-suite.sh
  set +e
  research-tests/audit-r11-claims.sh --inventory-only \
    >"$TMP/duplicate.log" 2>&1
  audit_status=$?
  set -e
  if [ "$audit_status" -eq 0 ]; then
    cat "$TMP/duplicate.log" >&2
    echo 'Auditor falsely accepted a duplicated runner entry' >&2
    exit 1
  fi
)
grep -Fq 'POSITIVE duplicates' "$TMP/duplicate.log"
echo 'R12_DUPLICATE_FALSE_PASS_REJECTED=passed'

echo 'R12_HARNESS_REGRESSIONS=passed'
