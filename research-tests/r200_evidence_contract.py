"""Pure R200 source/log/record and immutable validation-plan contracts."""
import hashlib, re

def declarations(source):
    text=source.decode()
    return set(re.findall(r'^(?:[01] )?([A-Za-z_]\w*)\s*:',text,re.M)+re.findall(r'^(?:record|data)\s+([A-Za-z_]\w*)',text,re.M))

def validate_record(record, source, log, root):
    assert source, 'Missing/empty source snapshot'
    assert hashlib.sha256(source).hexdigest()==record['sourceSHA256'], 'Source mismatch'
    assert log==record['transcript'], 'Transcript mismatch'
    path=record['path']
    assert path=='package' or (path.startswith(('research/DGamma/','research-tests/DGamma/')) and '..' not in path.split('/'))
    assert record['maxSampleRSSKiB']==max([s['rssKiB'] for s in record['rssSamples']] or [0])
    building=re.findall(r'^\d+/\d+: Building (.+)$',log,re.M)
    assert building==record['buildingLines']
    own='DGamma.'+path.rsplit('/',1)[-1][:-4]+' ('+str(root/path)+')'
    expected_fresh=path=='package' or own in building
    assert record['fresh']==expected_fresh
    if record['passed']:
        assert expected_fresh and not record['interrupted'] and not record['targetMutationDetected']
        assert not record['resourceStopped'] and not record['unexpectedBuilding']
        assert record['maxSampleRSSKiB']<=record['rssLimitKiB']
        if path!='package':assert building==[own], 'Only one exact own-source Building line'
        if record['expectedDiagnostic']:
            assert record['exit']!=0 and record['expectedDiagnostic'] in log
            assert record['symbol'] and record['symbol'] in log
        else:assert record['exit']==0 and 'Error:' not in log

def validate_plan(plan, read_source, module_paths, invalidation_paths):
    seen=set();planned_paths={item['path'] for item in plan}
    for item in plan:
        path=item['path'];assert path not in seen
        source=read_source(path)
        assert hashlib.sha256(source).hexdigest()==item['sourceHash']
        if path!='package':
            imports=re.findall(r'^import\s+(?:public\s+)?([\w.]+)',source.decode(),re.M)
            expected={module_paths[m] for m in imports if m in module_paths and (module_paths[m] in invalidation_paths or module_paths[m] in planned_paths)}
            assert expected==set(item['dependencies']), 'An invalidated import was omitted'
        assert set(item['dependencies'])<=seen, 'Not topological/import closed'
        seen.add(path)
    return seen

def validate_execution_policy(record, policy_bytes):
    """All R200 records begin under the already-effective no-lock owner rule."""
    import json
    policy=json.loads(policy_bytes)
    assert policy['authorization']=='SUPERVISOR RULE CHANGE: CROSS-LANE HEAVY LOCK ABOLISHED'
    assert policy['shift']=='R200' and policy['oneCompilerPerLane'] is True
    assert record['runnerSHA256']==policy['runnerSHA256']
    assert record['executionPolicySHA256']==hashlib.sha256(policy_bytes).hexdigest()
    assert record['crossLaneHeavyChecksPermitted'] is True
    assert record['heavyLock']==[] and record['lane2Compilers']==[]
    assert all(isinstance(t,str) and record['start']<=t<=record['end'] for t in record['crossLaneOverlapTimestampsUTC'])
