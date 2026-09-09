"""Pure R196 guarded-check, patch and topological evidence contracts."""
import hashlib
import re

def apply_manifest_diff(before, delta):
    """Apply exact unified context; reject mutation, overlaps and omitted context."""
    lines=before.splitlines(keepends=True); output=[]; cursor=0
    patch=delta.splitlines(keepends=True); i=2
    assert patch[0].startswith('--- a/') and patch[1].startswith('+++ b/')
    while i<len(patch):
        match=re.fullmatch(r'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@.*\n',patch[i])
        assert match, patch[i]
        at=int(match[1])-1; assert at>=cursor
        output.extend(lines[cursor:at]); cursor=at; i+=1
        removed=added=0
        while i<len(patch) and not patch[i].startswith('@@ '):
            line=patch[i]; assert line[0] in ' +-'
            if line[0] in ' -':
                assert cursor<len(lines) and lines[cursor]==line[1:]
                cursor+=1; removed+=1
            if line[0] in ' +': output.append(line[1:]); added+=1
            i+=1
        assert removed==int(match[2] or 1) and added==int(match[4] or 1)
    output.extend(lines[cursor:]); return ''.join(output)

def validate_record(record, source, log, root):
    assert hashlib.sha256(source).hexdigest()==record['sourceSHA256']
    assert log==record['transcript']
    path=record['path']
    assert path=='package' or (path.startswith(('research/DGamma/','research-tests/DGamma/')) and '..' not in path.split('/'))
    assert record['maxSampleRSSKiB']==max([s['rssKiB'] for s in record['rssSamples']] or [0])
    if record['passed']:
        assert record['fresh'] and not record['interrupted'] and not record['targetMutationDetected']
        assert not record.get('resourceStopped') and not record.get('unexpectedBuilding')
        assert record['maxSampleRSSKiB']<=record['rssLimitKiB']
        if path!='package':
            target='(?:'+re.escape(path)+'|'+re.escape(str(root/path))+')'
            assert re.search(r'^\d+/\d+: Building DGamma\.'+re.escape(path.rsplit('/',1)[1][:-4])+r' \('+target+r'\)$',log,re.M)
        if record['expectedDiagnostic']:
            assert record['exit']!=0 and record['expectedDiagnostic'] in log
            assert record.get('symbol') and record['symbol'] in log
        else: assert record['exit']==0 and 'Error:' not in log

def validate_topology(plan, done):
    seen=set(done)
    for item in plan:
        assert set(item['dependencies'])<=seen, (item['unit'],set(item['dependencies'])-seen)
        assert item['path'] not in seen
        seen.add(item['path'])
    return seen
