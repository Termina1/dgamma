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

expected_lengths = (5, 35, 30)
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
if len(tracked) != 65:
    raise SystemExit(f'expected 65 tracked tests, found {len(tracked)}')

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
git ls-files --error-unmatch \
  research-tests/cp5-hole-interface-baseline.json >/dev/null

echo 'R12_RUNNER_INVENTORY=passed'
if [ "$MODE" = "--inventory-only" ]; then
  exit 0
fi

BASELINE=34b21c9
CP3_BLOB=2c697e532e83989de8591fa6a4378747c6a501c0

git cat-file -e "$BASELINE^{commit}"
git diff --exit-code "$BASELINE" -- src dgamma.ipkg
test "$(git hash-object src/DGamma/CP3.idr)" = "$CP3_BLOB"

# Grind-time interface guard. Every baseline hole function keeps its exact
# public declaration, filled or not; surviving hole names must be a unique
# subset of the immutable baseline, and no new hole name may appear.
python3 - <<'PY'
from collections import Counter
from pathlib import Path
import json
import re

manifest_path = Path('research-tests/cp5-hole-interface-baseline.json')
manifest = json.loads(manifest_path.read_text())
if manifest.get('baseline') != '7d467e0556ab8ef62fa0d6c21b049f4346f1245d':
    raise SystemExit('wrong CP5 hole-interface baseline coordinate')
entries = manifest.get('holes', [])
if len(entries) != 27:
    raise SystemExit(f'baseline manifest has {len(entries)} holes, expected 27')
baseline_holes = [entry['hole'] for entry in entries]
if len(set(baseline_holes)) != 27:
    raise SystemExit('baseline manifest contains duplicate hole names')

def current_signature(path, function):
    lines = Path(path).read_text().splitlines()
    declaration_pattern = re.compile(r'^(?:0\s+)?' + re.escape(function) + r'\s*:')
    declaration_lines = [i for i, line in enumerate(lines)
                         if declaration_pattern.match(line)]
    if len(declaration_lines) != 1:
        raise SystemExit(
            f'{path}:{function} has {len(declaration_lines)} declarations, expected 1'
        )
    start = declaration_lines[0]
    definition_pattern = re.compile(r'^' + re.escape(function) + r'\b')
    definitions = [i for i in range(start + 1, len(lines))
                   if definition_pattern.match(lines[i])]
    if not definitions:
        raise SystemExit(f'{path}:{function} has no definition')
    return '\n'.join(lines[start:definitions[0]])

for entry in entries:
    actual = current_signature(entry['module'], entry['function'])
    if actual != entry['signature']:
        raise SystemExit(
            f"immutable or explicitly revised hole declaration changed: "
            f"{entry['module']}:{entry['function']}"
        )

approved_hole_revisions = manifest.get('approvedHoleSignatureRevisions', [])
if len(approved_hole_revisions) != 1:
    raise SystemExit('revision-18 hole-signature manifest is missing or malformed')
revision18 = approved_hole_revisions[0]
if (revision18.get('revision') != 18 or
        revision18.get('audit') != 'research-tests/O6-EXTERNAL-ORDER-AUDIT.md' or
        revision18.get('function') != 'adjacentSwapSuffixSpike'):
    raise SystemExit('revision-18 hole signature lacks its authorized audit')
revision18_text = Path(revision18['module']).read_text()
if revision18_text.count(revision18['premise']) != 1:
    raise SystemExit('revision-18 pair-local external-order premise changed')
for forbidden in [
    'adjacentSwapOperationalOccurrenceFoldSpike :',
    'record LocalRelationalDiamond',
    'record AdjacentSwapResult',
]:
    if forbidden in revision18['premise']:
        raise SystemExit('revision-18 authorization widened beyond suffix signature')

approved_fields = manifest.get('approvedRecordFieldRevisions', [])
if len(approved_fields) != 2 or any(entry.get('revision') != 17 for entry in approved_fields):
    raise SystemExit('revision-17 record-field manifest is missing or malformed')
for entry in approved_fields:
    if entry.get('audit') != 'research-tests/O6-ENDPOINT-CONTROLS-AUDIT.md':
        raise SystemExit('revision-17 record field lacks its authorized audit')
    text = Path(entry['module']).read_text()
    if text.count(entry['signature']) != 1:
        raise SystemExit(
            f"approved record field changed: {entry['record']}.{entry['field']}"
        )

current_occurrences = []
for path in sorted(Path('research/DGamma').glob('CP5Confluence*Spike.idr')):
    for hole in re.findall(r'\?([A-Za-z0-9_]+)', path.read_text()):
        current_occurrences.append((hole, str(path)))
counts = Counter(hole for hole, _ in current_occurrences)
duplicates = sorted(hole for hole, count in counts.items() if count != 1)
if duplicates:
    raise SystemExit(f'remaining hole names are not unique: {duplicates}')
new_holes = sorted(set(counts) - set(baseline_holes))
if new_holes:
    raise SystemExit(f'new hole names outside immutable baseline: {new_holes}')
PY

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
  '\?[A-Za-z_][A-Za-z0-9_]*|believe_me|assert_total|unsafePerformIO|^[[:space:]]*postulate[[:space:]]|%default partial' \
  src --include='*.idr'
assert_no_matches 'Non-hole research escape found' \
  'believe_me|assert_total|unsafePerformIO|^[[:space:]]*postulate[[:space:]]|%default partial' \
  research research-tests --include='*.idr'
assert_no_matches 'Tracked test contains a hole' \
  '\?[A-Za-z_][A-Za-z0-9_]*' research-tests --include='*.idr'

python3 - <<'PY'
from pathlib import Path
import re

expected = {
    'CP5ConfluenceCanonicalSortSpike.idr': 6,
    'CP5ConfluenceCrossTraceSpike.idr': 4,
    'CP5ConfluenceDeletionChainSpike.idr': 8,
    'CP5ConfluenceLocalDiamondSpike.idr': 2,
    'CP5ConfluenceRenamingCompositionSpike.idr': 1,
}
actual = {}
for filename, count in expected.items():
    text = Path('research/DGamma', filename).read_text()
    holes = set(re.findall(r'\?[A-Za-z0-9_]+', text))
    actual[filename] = len(holes)
if actual != expected:
    raise SystemExit(f'hole split mismatch: {actual}, expected {expected}')
if sum(actual.values()) != 21:
    raise SystemExit(f'hole total mismatch: {sum(actual.values())}')

plan = Path('THM73-PLAN.md').read_text()
rows = []
for line in plan.splitlines():
    match = re.match(r'^\| ([A-H]) — .*?\| .*?\| (\d+)–(\d+) \|$', line)
    if match:
        rows.append((match.group(1), int(match.group(2)), int(match.group(3))))
expected_rows = [
    ('A', 9, 9), ('B', 32, 55), ('C', 15, 26), ('D', 14, 27),
    ('E', 7, 13), ('F', 27, 47), ('G', 39, 64), ('H', 5, 8),
]
if rows != expected_rows:
    raise SystemExit(f'phase rows mismatch: {rows}, expected {expected_rows}')
if (sum(row[1] for row in rows), sum(row[2] for row in rows)) != (148, 249):
    raise SystemExit('phase sum is not 148–249')
if (sum(row[1] for row in rows[1:]),
    sum(row[2] for row in rows[1:])) != (139, 240):
    raise SystemExit('remaining phase sum is not 139–240')
PY

# The broad audit ends by executing the hardened, forced-fresh, serial suite.
IDRIS2="$IDRIS2" research-tests/run-r11-suite.sh --fresh

echo 'R12_CLAIMS_AUDIT=passed'
