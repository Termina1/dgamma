"""Authenticate the single supervisor-approved R193 final-validation retry.
No source mutation, compiler launch, plan replacement or implicit retry occurs here.
"""
import hashlib
import json
import subprocess


def authenticate(root, out):
    sha = lambda data: hashlib.sha256(data).hexdigest()
    raw = (out/'final-validation-continuation.json').read_bytes()
    assert raw == (root/'research-tests/O6-R193-FINAL-VALIDATION-CONTINUATION.json').read_bytes()
    assert sha(raw) == (out/'final-validation-continuation.sha256').read_text().strip()
    manifest = json.loads(raw)
    original = (out/'final-validation-plan.json').read_bytes()
    assert original == (root/'research-tests/O6-R193-FINAL-VALIDATION-PLAN.json').read_bytes()
    assert sha(original) == manifest['originalPlanSHA256'] == (out/'final-validation-plan.sha256').read_text().strip()
    plan = json.loads(original)
    assert [item['unit'] for item in plan] == ['V'+str(i) for i in range(1,53)]
    assert manifest['substitutions'] == {'V2':'V2R1'}
    assert manifest['maximumRetryCount'] == 1
    assert manifest['retryRSSLimitKiB'] == 52*1024*1024
    assert manifest['defaultRSSLimitKiB'] == 48*1024*1024
    retry = manifest['retry']
    assert retry == dict(plan[1], unit='V2R1')
    assert retry['path'] == 'research/DGamma/CP5ConfluenceLocalDiamondSpike.idr'
    assert retry['sourceHash'] == 'f77f66a3e3a62f2ff757709f08d1488a25d54d425af74dcec4c2c0f0ed28c6fd'
    assert sha((root/retry['path']).read_bytes()) == retry['sourceHash']
    assert sha(subprocess.check_output(['git','show','77a9efe1:'+retry['path']],cwd=root)) == retry['sourceHash']
    failed_raw = (out/'V2.json').read_bytes()
    assert sha(failed_raw) == manifest['originalV2RecordSHA256']
    failed = json.loads(failed_raw)
    assert failed['unit'] == 'V2' and failed['path'] == retry['path']
    assert failed['sourceSHA256'] == retry['sourceHash']
    assert failed['interrupted'] and not failed['passed'] and not failed['fresh']
    assert failed['maxSampleRSSKiB'] == 50461760 and failed['exit'] == -15
    first = json.loads((out/'V1.json').read_text())
    assert first['passed'] and first['fresh'] and first['sourceSHA256'] == plan[0]['sourceHash']
    assert manifest['continuationUnits'] == [item['unit'] for item in plan[2:]]
    effective = [plan[0], retry] + plan[2:]
    assert manifest['effectiveUnits'] == [item['unit'] for item in effective]
    return manifest, effective
