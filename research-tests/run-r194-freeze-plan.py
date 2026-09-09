#!/usr/bin/env python3
"""Freeze the main-only R194 final plan once; never launch a compiler."""
import datetime, hashlib, json, pathlib, runpy, subprocess
ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = pathlib.Path('/tmp/dgamma-r194')
contract = runpy.run_path(str(ROOT / 'research-tests/r194_evidence_contract.py'))
def git(*args): return subprocess.check_output(['git', *args], cwd=ROOT)
assert not (OUT / 'final-validation-plan.json').exists()
assert not git('diff', '--cached', '--name-only')
assert not git('diff', '--name-only', '--', 'research/', 'src/', 'research-tests/DGamma/', 'dgamma.ipkg')
old = json.loads((ROOT / 'research-tests/O6-R193-FINAL-VALIDATION-PLAN.json').read_text())
excluded = [p['path'] for p in old if not contract['owned_target'](p['path'])]
assert len(excluded) == 3
plan = [dict(p) for p in old if contract['owned_target'](p['path'])]
changed = git('diff', '--name-only', 'b81362d8', '--', 'research/', 'research-tests/DGamma/').decode().splitlines()
for path in changed:
    if path.endswith('.idr') and path not in {p['path'] for p in plan}:
        assert contract['owned_target'](path)
        plan.append(dict(path=path, expectedDiagnostic=None, symbol=None))
for index, item in enumerate(plan, 1):
    item['unit'] = 'V' + str(index)
    source = ROOT / ('dgamma.ipkg' if item['path'] == 'package' else item['path'])
    item['sourceHash'] = hashlib.sha256(source.read_bytes()).hexdigest()
assert len(plan) == 56 and plan[-1]['path'] == 'research/DGamma/CP5O20OwnCutSafetySpike.idr'
data = (json.dumps(plan, indent=2) + '\n').encode()
(ROOT / 'research-tests/O6-R194-FINAL-VALIDATION-PLAN.json').write_bytes(data)
(OUT / 'final-validation-plan.json').write_bytes(data)
(OUT / 'final-validation-plan.sha256').write_text(hashlib.sha256(data).hexdigest() + '\n')
scope = dict(sourceFreezeHead=git('rev-parse', 'HEAD').decode().strip(), timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    finalChecks=len(plan), positiveChecks=sum(not p['expectedDiagnostic'] for p in plan), expectedNegatives=sum(bool(p['expectedDiagnostic']) for p in plan),
    changedIdrisTargets=changed, planSHA256=hashlib.sha256(data).hexdigest(), excludedLaneOwnedTargets=excluded,
    exclusionReason='No main check of lane-owned source or extension-dependent probe. Main frozen fixtures remain; no claim to certify current lane2 variants.',
    defaultRSSGiB=48, pinnedUnchangedLocalDiamondRSSGiB=52, sharedHeavyLock='/tmp/dgamma-heavy.lock', substitutions={})
(ROOT / 'research-tests/O6-R194-FINAL-VALIDATION-SCOPE.json').write_text(json.dumps(scope, indent=2) + '\n')
(OUT / 'final-validation-scope.json').write_text(json.dumps(scope, indent=2) + '\n')
print(json.dumps(scope, indent=2))
