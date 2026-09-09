#!/usr/bin/env python3
"""Detached serialized sealed B-plan runner. Stops at FIRST non-PASS; never retries."""
import datetime, hashlib, json, pathlib, subprocess, sys
ROOT=pathlib.Path(__file__).resolve().parents[1]
OUT=pathlib.Path('/tmp/dgamma-r196')
plan_path=ROOT/'research-tests/O6-R196-DEPENDENT-RECHECK-PLAN.json'
plan_bytes=plan_path.read_bytes()
assert hashlib.sha256(plan_bytes).hexdigest()==(OUT/'dependent-plan.sha256').read_text().strip()
plan=json.loads(plan_bytes)
for stage in ['A1','A2','A4','A3']:
    receipts=[json.loads(s) for s in (OUT/'commit-receipts.jsonl').read_text().splitlines()]
    assert any(r['unit']==stage and r['event']=='GUARDED COMMIT' for r in receipts), stage+' not committed'
for item in plan['items']:
    assert not (OUT/(item['unit']+'.json')).exists(), 'Append-only B; resume needs separate manifest'
    assert plan_path.read_bytes()==plan_bytes
    assert datetime.datetime.now(datetime.timezone.utc)<datetime.datetime(2026,9,9,7,19,35,tzinfo=datetime.timezone.utc)
    command=['python3','-I',str(ROOT/'research-tests/run-r196-check.py'),item['unit'],item['path']]
    if item['expectedDiagnostic']:
        command.append(item['expectedDiagnostic'])
        if item.get('symbol'): command.append(item['symbol'])
    print('LAUNCH',item['unit'],item['path'],flush=True)
    with (OUT/(item['unit']+'.monitor')).open('w') as log:
        result=subprocess.run(command,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT)
    record_path=OUT/(item['unit']+'.json')
    record=json.loads(record_path.read_text()) if record_path.exists() else None
    if result.returncode or not record or not record['passed']:
        print('B STOP',item['unit'],'record',record_path,'runner exit',result.returncode,flush=True)
        sys.exit(1)
    print('PASS',item['unit'],'seconds',record['seconds'],'sampleKiB',record['maxSampleRSSKiB'],flush=True)
(OUT/'B-complete.json').write_text(json.dumps(dict(planSHA256=hashlib.sha256(plan_bytes).hexdigest(),count=len(plan['items']),timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat()),indent=2)+'\n')
print('B COMPLETE',len(plan['items']),flush=True)
