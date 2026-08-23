#!/usr/bin/env bash
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
cd "$ROOT"
IDRIS2=${IDRIS2:-idris2}
MODE=${1:-}
if [ -n "$MODE" ] && [ "$MODE" != "--inventory-only" ]; then
  echo "usage: $0 [--inventory-only]" >&2
  exit 2
fi

# First validate the entire runner inventory as lists. Sets are used only after
# cardinality and duplicate checks, so a duplicated entry cannot be laundered.
python3 - <<'PY'
from collections import Counter
from pathlib import Path
import subprocess

runner_path = Path('research-tests/run-r11-suite.sh')
runner = runner_path.read_text()

def array_lines(name):
    marker = name + '=('
    if runner.count(marker) != 1:
        raise SystemExit(f'expected one {name} array, found {runner.count(marker)}')
    body = runner.split(marker, 1)[1].split('\n)', 1)[0]
    return [line.strip().strip('"') for line in body.splitlines()
            if line.strip() and not line.lstrip().startswith('#')]

spikes = array_lines('SPIKES')
positives = array_lines('POSITIVE')
negative_specs = array_lines('NEGATIVE_SPECS')
negatives = [spec.split('|', 1)[0] for spec in negative_specs]

for label, values in [('SPIKES', spikes), ('POSITIVE', positives),
                      ('NEGATIVE_SPECS', negatives)]:
    duplicates = sorted(name for name, count in Counter(values).items() if count != 1)
    if duplicates:
        raise SystemExit(f'{label} duplicates: {duplicates}')

all_names = spikes + positives + negatives
cross_duplicates = sorted(name for name, count in Counter(all_names).items() if count != 1)
if cross_duplicates:
    raise SystemExit(f'within/cross-category duplicates: {cross_duplicates}')

expected_lengths = (5, 27, 26)
actual_lengths = (len(spikes), len(positives), len(negatives))
if actual_lengths != expected_lengths:
    raise SystemExit(f'category lengths {actual_lengths}, expected {expected_lengths}')

tracked = subprocess.check_output(
    ['git', 'ls-files', 'research-tests/DGamma/*.idr'], text=True
).splitlines()
expected_tests = sorted(
    [f'research-tests/DGamma/{name}.idr' for name in positives + negatives]
)
if sorted(tracked) != expected_tests:
    raise SystemExit(
        f'tracked test mismatch: missing={sorted(set(expected_tests)-set(tracked))} '
        f'extra={sorted(set(tracked)-set(expected_tests))}'
    )
if len(tracked) != 53:
    raise SystemExit(f'expected 53 tracked tests, found {len(tracked)}')

tracked_spikes = subprocess.check_output(
    ['git', 'ls-files', 'research/DGamma/CP5Confluence*Spike.idr'], text=True
).splitlines()
expected_spikes = sorted(
    [f'research/DGamma/{name}.idr' for name in spikes]
)
if sorted(tracked_spikes) != expected_spikes:
    raise SystemExit(
        f'tracked spike mismatch: missing={sorted(set(expected_spikes)-set(tracked_spikes))} '
        f'extra={sorted(set(tracked_spikes)-set(expected_spikes))}'
    )

for path in tracked + tracked_spikes:
    if not Path(path).is_file():
        raise SystemExit(f'tracked suite path absent from worktree: {path}')
PY

git ls-files --error-unmatch research-tests/run-r11-suite.sh >/dev/null
git ls-files --error-unmatch research-tests/audit-r11-claims.sh >/dev/null
git ls-files --error-unmatch research-tests/test-r12-harness.sh >/dev/null

echo 'R12_RUNNER_INVENTORY=passed'
if [ "$MODE" = "--inventory-only" ]; then
  exit 0
fi

BASELINE=34b21c9
CP3_BLOB=2c697e532e83989de8591fa6a4378747c6a501c0

git cat-file -e "$BASELINE^{commit}"
git diff --exit-code "$BASELINE" -- src dgamma.ipkg
test "$(git hash-object src/DGamma/CP3.idr)" = "$CP3_BLOB"
# Shift 54 is harness-only: no research type or hole may differ from its gate.
git diff --exit-code 6773ffc -- research

assert_no_matches() {
  local description=$1
  shift
  local output
  output=$(mktemp)
  if grep -R -nE "$@" >"$output" 2>&1; then
    cat "$output" >&2
    rm -f "$output"
    echo "$description" >&2
    exit 1
  fi
  rm -f "$output"
}

assert_no_matches 'Production package reaches research CP5 modules' \
  'research/|DGamma\.CP5Confluence' src dgamma.ipkg
assert_no_matches 'Production escape or hole found' \
  '\?[A-Za-z_][A-Za-z0-9_]*|believe_me|assert_total|^[[:space:]]*postulate[[:space:]]|%default partial' \
  src --include='*.idr'
assert_no_matches 'Non-hole research escape found' \
  'believe_me|assert_total|^[[:space:]]*postulate[[:space:]]|%default partial' \
  research research-tests --include='*.idr'
assert_no_matches 'Tracked test contains a hole' \
  '\?[A-Za-z_][A-Za-z0-9_]*' research-tests --include='*.idr'

python3 - <<'PY'
from pathlib import Path
import re

expected = {
    'CP5ConfluenceCanonicalSortSpike.idr': 6,
    'CP5ConfluenceCrossTraceSpike.idr': 4,
    'CP5ConfluenceDeletionChainSpike.idr': 11,
    'CP5ConfluenceLocalDiamondSpike.idr': 9,
    'CP5ConfluenceRenamingCompositionSpike.idr': 2,
}
actual = {}
for filename, count in expected.items():
    text = Path('research/DGamma', filename).read_text()
    holes = set(re.findall(r'\?[A-Za-z0-9_]+', text))
    actual[filename] = len(holes)
if actual != expected:
    raise SystemExit(f'hole split mismatch: {actual}, expected {expected}')
if sum(actual.values()) != 32:
    raise SystemExit(f'hole total mismatch: {sum(actual.values())}')

plan = Path('THM73-PLAN.md').read_text()
rows = []
for line in plan.splitlines():
    match = re.match(r'^\| ([A-H]) — .*?\| .*?\| (\d+)–(\d+) \|$', line)
    if match:
        rows.append((match.group(1), int(match.group(2)), int(match.group(3))))
expected_rows = [
    ('A', 9, 17), ('B', 32, 55), ('C', 15, 26), ('D', 14, 27),
    ('E', 7, 13), ('F', 27, 47), ('G', 39, 64), ('H', 5, 8),
]
if rows != expected_rows:
    raise SystemExit(f'phase rows mismatch: {rows}, expected {expected_rows}')
if (sum(row[1] for row in rows), sum(row[2] for row in rows)) != (148, 257):
    raise SystemExit('phase sum is not 148–257')
PY

# The broad audit ends by executing the hardened, forced-fresh, serial suite.
IDRIS2="$IDRIS2" research-tests/run-r11-suite.sh --fresh

echo 'R12_CLAIMS_AUDIT=passed'
