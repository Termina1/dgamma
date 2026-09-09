#!/usr/bin/env python3
"""Freeze ALL inherited R194 main targets plus every changed R195 Idris target.
Only a path absent from the main checkout may be excluded, with its reason.
No compiler, TTC deletion, source modification or lane-worktree access.
"""
import datetime, hashlib, json, pathlib, runpy, subprocess, sys
ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = pathlib.Path('/tmp/dgamma-r195')
START = '981e6137'
assert not sys.argv[1:]
contract = runpy.run_path(str(ROOT / 'research-tests/r195_evidence_contract.py'))
def git(*args): return subprocess.check_output(['git', *args], cwd=ROOT)
assert not git('diff', '--cached', '--name-only')
assert not git('diff', '--name-only', '--', 'research/', 'src/', 'research-tests/DGamma/', 'dgamma.ipkg')
assert not (OUT / 'final-validation-plan.json').exists(), 'Immutable append-only plan'
assert not any(json.loads(line)['unit'].startswith('V') for line in (OUT / 'ledger.jsonl').read_text().splitlines())
inherited = json.loads((ROOT / 'research-tests/O6-R194-FINAL-VALIDATION-PLAN.json').read_text())
plan, excluded = [], []
for item in inherited:
    path = 'dgamma.ipkg' if item['path'] == 'package' else item['path']
    source = ROOT / path
    if not source.is_file():
        excluded.append(dict(path=item['path'], reason='file absent from main tree'))
        continue
    assert contract['owned_target'](item['path']) and source.stat().st_size > 0
    assert source.read_bytes() == git('show', START + ':' + path), 'Inherited baseline target changed'
    plan.append(dict(item))
changed = [p for p in git('diff', '--name-only', START, '--', 'research/', 'research-tests/DGamma/').decode().splitlines() if p.endswith('.idr')]
for path in changed:
    if path not in {p['path'] for p in plan}:
        assert contract['owned_target'](path)
        plan.append(dict(path=path, expectedDiagnostic=None, symbol=None))
for index, item in enumerate(plan, 1):
    item['unit'] = 'V' + str(index)
    source = ROOT / ('dgamma.ipkg' if item['path'] == 'package' else item['path'])
    item['sourceHash'] = hashlib.sha256(source.read_bytes()).hexdigest()
assert len(plan) == len(inherited) - len(excluded) + len([p for p in changed if p not in {i['path'] for i in inherited}])
data = (json.dumps(plan, indent=2) + '\n').encode()
(ROOT / 'research-tests/O6-R195-FINAL-VALIDATION-PLAN.json').write_bytes(data)
(OUT / 'final-validation-plan.json').write_bytes(data)
(OUT / 'final-validation-plan.sha256').write_text(hashlib.sha256(data).hexdigest() + '\n')
scope = dict(sourceFreezeHead=git('rev-parse', 'HEAD').decode().strip(), baselineCommit=git('rev-parse', START).decode().strip(),
    timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(), finalChecks=len(plan), inheritedChecks=len(inherited),
    positiveChecks=sum(not p['expectedDiagnostic'] for p in plan), expectedNegatives=sum(bool(p['expectedDiagnostic']) for p in plan),
    changedIdrisTargets=changed, planSHA256=hashlib.sha256(data).hexdigest(), exclusions=excluded,
    baselineQualification='All inherited main-tree baseline targets included at981e6137 bytes. This never certifies ongoing lane2-created results.',
    ownerRuling='R195 user scope and R194 preflight inclusion ruling; no preflight exclusion or withdrawn plan this shift.',
    defaultRSSGiB=48, pinnedUnchangedLocalDiamondRSSGiB=52, sharedHeavyLock='/tmp/dgamma-heavy.lock', substitutions={})
(ROOT / 'research-tests/O6-R195-FINAL-VALIDATION-SCOPE.json').write_text(json.dumps(scope, indent=2) + '\n')
(OUT / 'final-validation-scope.json').write_text(json.dumps(scope, indent=2) + '\n')
print(json.dumps(scope, indent=2))
