"""Pure R204 source/log/record and immutable validation-plan contracts.
maximum sampled RSS over command-matching idris2 processes (single-process compiler; not an aggregate process-tree total; not OS high-water).
"""
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
    diagnostic_ok=(record['exit']!=0 and record['expectedDiagnostic'] in log and record['symbol'] and record['symbol'] in log) if record['expectedDiagnostic'] else (record['exit']==0 and 'Error:' not in log)
    exact_build=(path=='package' or building==[own])
    derived=bool(expected_fresh and exact_build and diagnostic_ok and not record['interrupted'] and not record['targetMutationDetected'] and not record['resourceStopped'] and not record['unexpectedBuilding'] and record['maxSampleRSSKiB']<=record['rssLimitKiB'])
    assert record['passed']==derived, 'Passed flag does not match independently derived outcome'
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
    """R204 starts with the correct label; no inherited-label relabeling exists."""
    import json
    policy=json.loads(policy_bytes)
    assert policy['authorization']=='SUPERVISOR RULE CHANGE: CROSS-LANE HEAVY LOCK ABOLISHED'
    assert policy['shift']=='R204' and policy['oneCompilerPerLane'] is True
    assert record['runnerSHA256']==policy['runnerSHA256']
    assert record['executionPolicySHA256']==hashlib.sha256(policy_bytes).hexdigest()
    assert record['crossLaneHeavyChecksPermitted'] is True
    assert record['heavyLock']==[] and record['lane2Compilers']==[]
    assert all(isinstance(t,str) and record['start']<=t<=record['end'] for t in record['crossLaneOverlapTimestampsUTC'])

def validate_superseded_pass(first, replacement):
    """Only A3-2 -> A3-3's exact rstrip-only whitespace guard repair is allowed."""
    fixed=('\n'.join(line.rstrip() for line in first.decode().splitlines()).rstrip()+'\n').encode()
    assert first!=replacement and fixed==replacement

def validate_style_repair(before, after):
    """P1 has exactly two inlined former aliases; statement stays byte-identical."""
    assert hashlib.sha256(before).hexdigest()=="b05d2323fbec18160bc212a7ffa3270f0e28e7dc68cfaaa24b1c181f8e410068"
    assert hashlib.sha256(after).hexdigest()=="6946cbd30558b3013a418e0d3cb7ff85ef3698e3e7cd6555545079df6b596618"
    marker=b'r203ActualUnloadIsNotEpsilon ='
    assert before.split(marker)[0]==after.split(marker)[0]
    assert declarations(before)==declarations(after)
    assert not re.search(rb'\blet\b',b'\n'.join(line for line in after.splitlines() if not line.lstrip().startswith((b'--',b'|||'))))
