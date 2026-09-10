"""Compiler-free independent checks on R206 native receipts."""
import hashlib, re

def validate_record(record, source, transcript, root):
    assert hashlib.sha256(source).hexdigest()==record['sourceSHA256'], 'source hash'
    assert transcript==record['transcript'], 'transcript'
    lines=re.findall(r'^\d+/\d+: Building (.+)$',transcript,re.M)
    assert lines==record['buildingLines'], 'Building inventory'
    if record['path']=='package':
        fresh=not lines
        unexpected=lines
    else:
        module=re.search(r'^module\s+([\w.]+)',source.decode(),re.M)[1]
        own=module+' ('+str(root/record['path'])+')'
        fresh=lines==[own]
        unexpected=[line for i,line in enumerate(lines) if line!=own or i>0]
    assert fresh==record['fresh'], 'fresh flag'
    assert unexpected==record['unexpectedBuilding'], 'unexpected Building flag'
    samples=record['rssSamples']
    maximum=max([s['rssKiB'] for s in samples] or [0])
    assert maximum==record['maxSampleRSSKiB'], 'sampled maximum'
    assert record['rssLimitKiB']==(52 if record['path'].endswith('/CP5ConfluenceLocalDiamondSpike.idr') else 48)*1024*1024, 'RSS limit'
    expected=record['expectedDiagnostic']
    diagnostic=(record['exit']==1 and expected in transcript and record['symbol'] and record['symbol'] in transcript) if expected else record['exit']==0 and 'Error:' not in transcript
    passed=bool(fresh and diagnostic and not unexpected and not record['interrupted'] and not record['targetMutationDetected'] and not record['multipleOwnedCompilers'] and maximum<=record['rssLimitKiB'])
    assert passed==record['passed'], 'outcome flag'
    assert record['end']>=record['start'], 'timestamp order'
    assert all(record['start']<=x<=record['end'] for x in record['crossLaneOverlapTimestampsUTC']), 'overlap timestamps'
    assert record['CP3Blob']=='eeaa70aa4414648bb2a1173d58244267997d16d7', 'production blob'
    return passed
