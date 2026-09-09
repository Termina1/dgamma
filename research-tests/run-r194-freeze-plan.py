#!/usr/bin/env python3
"""Freeze R194 main-tree final plan. Owner-approved --restore-main-baseline
preserves/withdraws the unrun56-slot preflight plan, then restores all inherited
main regression targets. No compiler, Idris source edit or proof-budget change.
"""
import datetime, hashlib, json, pathlib, runpy, subprocess, sys
ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = pathlib.Path('/tmp/dgamma-r194')
contract = runpy.run_path(str(ROOT / 'research-tests/r194_evidence_contract.py'))
def git(*args): return subprocess.check_output(['git', *args], cwd=ROOT)
assert sys.argv[1:] in [[], ['--restore-main-baseline']]
assert not git('diff', '--cached', '--name-only')
assert not git('diff', '--name-only', '--', 'research/', 'src/', 'research-tests/DGamma/', 'dgamma.ipkg')
if sys.argv[1:]:
    assert 'RULING: NOT approved' in (ROOT / 'research-tests/O6-R194-PREFLIGHT-RULING.md').read_text()
    assert not any(json.loads(row)['unit'].startswith('V') for row in (OUT / 'ledger.jsonl').read_text().splitlines())
    prior = (OUT / 'final-validation-plan.json').read_bytes()
    assert hashlib.sha256(prior).hexdigest() == '73ddfc58ea6e13473f31a61366fcbad931a18cc69b62b1de6ceb58985fa31bfe'
    assert prior == (ROOT / 'research-tests/O6-R194-FINAL-VALIDATION-PLAN.json').read_bytes()
    assert not (ROOT / 'research-tests/O6-R194-PREFLIGHT-PLAN.json').exists()
    for old, preserved in [('FINAL-VALIDATION-PLAN', 'PREFLIGHT-PLAN'), ('FINAL-VALIDATION-SCOPE', 'PREFLIGHT-SCOPE')]:
        data = (ROOT / ('research-tests/O6-R194-' + old + '.json')).read_bytes()
        (ROOT / ('research-tests/O6-R194-' + preserved + '.json')).write_bytes(data)
        (OUT / (preserved.lower() + '.json')).write_bytes(data)
    (OUT / 'preflight-plan.sha256').write_text(hashlib.sha256(prior).hexdigest() + '\n')
else:
    assert not (OUT / 'final-validation-plan.json').exists()
old = json.loads((ROOT / 'research-tests/O6-R193-FINAL-VALIDATION-PLAN.json').read_text())
plan, excluded = [], []
for item in old:
    source = ROOT / ('dgamma.ipkg' if item['path'] == 'package' else item['path'])
    if not source.exists():
        excluded.append(dict(path=item['path'], reason='file absent from main tree'))
        continue
    assert contract['owned_target'](item['path'])
    assert source.read_bytes() == git('show', 'b81362d8:' + str(source.relative_to(ROOT))), 'Inherited target must stay baseline-pinned'
    plan.append(dict(item))
changed = git('diff', '--name-only', 'b81362d8', '--', 'research/', 'research-tests/DGamma/').decode().splitlines()
for path in changed:
    if path.endswith('.idr') and path not in {p['path'] for p in plan}:
        assert contract['owned_target'](path)
        plan.append(dict(path=path, expectedDiagnostic=None, symbol=None))
for index, item in enumerate(plan, 1):
    item['unit'] = 'V' + str(index)
    source = ROOT / ('dgamma.ipkg' if item['path'] == 'package' else item['path'])
    item['sourceHash'] = hashlib.sha256(source.read_bytes()).hexdigest()
assert len(plan) == 59 and not excluded and plan[-1]['path'] == 'research/DGamma/CP5O20OwnCutSafetySpike.idr'
data = (json.dumps(plan, indent=2) + '\n').encode()
(ROOT / 'research-tests/O6-R194-FINAL-VALIDATION-PLAN.json').write_bytes(data)
(OUT / 'final-validation-plan.json').write_bytes(data)
(OUT / 'final-validation-plan.sha256').write_text(hashlib.sha256(data).hexdigest() + '\n')
scope = dict(sourceFreezeHead='408bd21e832cd231a727dfb8347c9a15d019f4e0', planPreparationHead=git('rev-parse', 'HEAD').decode().strip(),
    timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(), finalChecks=len(plan),
    positiveChecks=sum(not p['expectedDiagnostic'] for p in plan), expectedNegatives=sum(bool(p['expectedDiagnostic']) for p in plan),
    changedIdrisTargets=changed, planSHA256=hashlib.sha256(data).hexdigest(), exclusions=excluded,
    baselineQualification='All52 inherited targets exist and remain byte-pinned to main b81362d8. Checking them certifies main only, never ongoing lane2 results.',
    withdrawnUnrunPreflightPlanSHA256='73ddfc58ea6e13473f31a61366fcbad931a18cc69b62b1de6ceb58985fa31bfe',
    ownerRuling='O6-R194-PREFLIGHT-RULING.md', defaultRSSGiB=48, pinnedUnchangedLocalDiamondRSSGiB=52,
    sharedHeavyLock='/tmp/dgamma-heavy.lock', substitutions={})
(ROOT / 'research-tests/O6-R194-FINAL-VALIDATION-SCOPE.json').write_text(json.dumps(scope, indent=2) + '\n')
(OUT / 'final-validation-scope.json').write_text(json.dumps(scope, indent=2) + '\n')
print(json.dumps(scope, indent=2))
