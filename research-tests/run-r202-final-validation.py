#!/usr/bin/env python3
"""Detached sequential final validation; each native invocation has its own guard."""
import datetime, hashlib, json, pathlib, subprocess, sys
ROOT=pathlib.Path(__file__).resolve().parents[1];OUT=pathlib.Path('/tmp/dgamma-r202')
sha=lambda b:hashlib.sha256(b).hexdigest()
data=(OUT/'final-validation-plan.json').read_bytes(); plan=json.loads(data)
assert sha(data)==(OUT/'final-validation-plan.sha256').read_text().strip()
assert data==(ROOT/'research-tests/O6-R202-FINAL-VALIDATION-PLAN.json').read_bytes()
scope=json.loads((ROOT/'research-tests/O6-R202-VALIDATION-SCOPE.json').read_text())
assert len(plan)==scope['checksIncludingPackage'] and len({x['path'] for x in plan})==len(plan)
assert scope['inheritedSources']==171 and not scope['excludedInheritedApplicablePaths']
assert json.loads((OUT/'contract-tests.json').read_text())['status']=='PASS'
assert not (OUT/'final-validation-launched.json').exists(), 'No silent restart'
policy_bytes=(OUT/'execution-policy.json').read_bytes();policy=json.loads(policy_bytes)
assert policy['authorization']=='SUPERVISOR RULE CHANGE: CROSS-LANE HEAVY LOCK ABOLISHED'
assert sha((ROOT/'research-tests/run-r202-check.py').read_bytes())==policy['runnerSHA256']
launch=dict(startUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),planSHA256=sha(data),runnerSHA256=policy['runnerSHA256'],driverSHA256=sha(pathlib.Path(__file__).read_bytes()),count=len(plan),executionPolicySHA256=sha(policy_bytes))
(OUT/'final-validation-launched.json').write_text(json.dumps(launch,indent=2)+'\n')
records=[json.loads(x) for x in (OUT/'ledger.jsonl').read_text().splitlines()]
assert not any(r['unit'].startswith('V') for r in records), 'No silent replay'
completed=[]
for item in plan[len(completed):]:
    assert sha((ROOT/'research-tests/run-r202-check.py').read_bytes())==launch['runnerSHA256'], 'Runner mutated'
    assert sha((OUT/'final-validation-plan.json').read_bytes())==launch['planSHA256'], 'Plan mutated'
    assert sha((OUT/'execution-policy.json').read_bytes())==launch['executionPolicySHA256'], 'Owner policy mutated'
    for frozen in plan:
        assert sha((ROOT/('dgamma.ipkg' if frozen['path']=='package' else frozen['path'])).read_bytes())==frozen['sourceHash'], 'Frozen source mutated: '+frozen['path']
    command=[sys.executable,'-I',str(ROOT/'research-tests/run-r202-check.py'),item['unit'],item['path']]
    if item['expectedDiagnostic']:command += [item['expectedDiagnostic'],item['symbol']]
    print('FINAL CHECK',item['unit'],item['path'],flush=True)
    with (OUT/(item['unit']+'.launch')).open('w') as log:
        result=subprocess.run(command,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT)
    record_path=OUT/(item['unit']+'.json')
    record=json.loads(record_path.read_text()) if record_path.exists() else None
    if result.returncode!=0 or not record or not record['passed']:
        report=dict(status='STOP; owner gate required; no retry',failedUnit=item['unit'],exit=result.returncode,recordPresent=record is not None,completed=completed,total=len(plan),endUTC=datetime.datetime.now(datetime.timezone.utc).isoformat())
        (OUT/'final-validation-result.json').write_text(json.dumps(report,indent=2)+'\n')
        print(json.dumps(report),flush=True);sys.exit(1)
    assert record['sourceSHA256']==item['sourceHash'] and record['validationContinuationSHA256']==launch['planSHA256']
    completed.append(item['unit']);print('FINAL PASS',item['unit'],record['seconds'],record['maxSampleRSSKiB'],flush=True)
report=dict(status='PASS',completed=completed,total=len(plan),sourceTargets=scope['sourceTargets'],packageBuild='seeded PASS; not cold',endUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),planSHA256=launch['planSHA256'],executionPolicySHA256=launch['executionPolicySHA256'])
(OUT/'final-validation-result.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report),flush=True)
