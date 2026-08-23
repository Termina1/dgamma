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
