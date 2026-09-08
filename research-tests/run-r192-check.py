#!/usr/bin/env python3
"""One serialized, seeded, fresh R192 check. Launch detached with python3 -I.
No TTC is deleted. JSON/log/source snapshots live under /tmp/dgamma-r192.
Usage: run-r192-check.py UNIT PATH [DIAGNOSTIC [SYMBOL]]; PATH=package for build.
"""
import datetime
import hashlib
import json
import os
import pathlib
import re
import signal
import subprocess
import sys
import time

ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = pathlib.Path('/tmp/dgamma-r192')
OUT.mkdir(exist_ok=True)
unit, path = sys.argv[1:3]
diagnostic = sys.argv[3] if len(sys.argv) > 3 else None
symbol = sys.argv[4] if len(sys.argv) > 4 else None
assert not (OUT/(unit+'.json')).exists(), 'Invocation names are append-only'
# R192: no proof/new attempt in final40min; hash-frozen validation may
# start until final25min. Start18:26:48Z, timeout22:26:48Z.
planned_validation = False
if re.fullmatch(r'V\d+', unit):
    plan_bytes = (OUT/'final-validation-plan.json').read_bytes()
    assert hashlib.sha256(plan_bytes).hexdigest() == (OUT/'final-validation-plan.sha256').read_text().strip(), 'Frozen validation plan changed'
    items = [item for item in json.loads(plan_bytes) if item['unit'] == unit]
    assert len(items) == 1 and items[0]['path'] == path and items[0]['expectedDiagnostic'] == diagnostic and symbol is None, 'Unplanned validation invocation'
    planned_source = ROOT/('dgamma.ipkg' if path == 'package' else path)
    assert hashlib.sha256(planned_source.read_bytes()).hexdigest() == items[0]['sourceHash'], 'Validation source is not frozen bytes'
    planned_validation = True
cutoff = datetime.datetime(2026,9,8,22,1,48,tzinfo=datetime.timezone.utc) if planned_validation else datetime.datetime(2026,9,8,21,46,48,tzinfo=datetime.timezone.utc)
assert datetime.datetime.now(datetime.timezone.utc) < cutoff, 'R192 attempt21:46:48 / frozen-validation22:01:48 start guard'
procs = subprocess.check_output(['ps', '-axo', 'pid,ppid,command'], text=True)
if re.search(r'/idris2_app/idris2(?:\.so)?(?:\s|$)', procs):
    raise SystemExit('Existing compiler: reconcile orphan before fresh attempt')
command = ['idris2', '--source-dir', 'src', '--source-dir', 'research']
if path == 'package':
    command = ['idris2', '--build', 'dgamma.ipkg']
    snapshot = (ROOT/'dgamma.ipkg').read_bytes()
else:
    target = ROOT/path
    if not target.is_file() or target.stat().st_size == 0:
        raise SystemExit('Missing/empty source target: refusing touch or compiler launch')
    snapshot = target.read_bytes()
    if re.fullmatch(r'[A-F]\d+-\d+', unit):
        old = subprocess.run(['git','show','HEAD:'+path],cwd=ROOT,capture_output=True)
        def declarations(data):
            text = data.decode()
            return set(re.findall(r'^(?:[01] )?([A-Za-z_]\w*)\s*:',text,re.M) + re.findall(r'^(?:record|data)\s+([A-Za-z_]\w*)',text,re.M))
        assert len(declarations(snapshot)-declarations(old.stdout if old.returncode == 0 else b'')) == 1, 'Exactly one new declaration per proof invocation'
    # Exactly gated A11 surface/consumer declaration checks (not new declarations).
    if re.fullmatch(r'X[123]-1', unit):
        approved_bytes = (ROOT/'research-tests/O6-R192-A11-SURFACE-MANIFEST.json').read_bytes()
        assert hashlib.sha256(approved_bytes).hexdigest() == 'b391c8bc6d5e4400266af7bff67cd88133da1082b9baa788169e5f6d815e5382'
        approved = [item for item in json.loads(approved_bytes)['items'] if item['unit'] == unit]
        assert len(approved) == 1 and approved[0]['path'] == path
        assert hashlib.sha256(snapshot).hexdigest() == approved[0]['newSourceSHA256']
        assert diagnostic == approved[0]['expectedDiagnostic']
        assert symbol == (approved[0]['symbol'] if diagnostic else None)
    target.touch()
    if path.startswith('research-tests/'):
        command += ['--source-dir', 'research-tests']
    command += ['--check', path]
(OUT/(unit+'.source')).write_bytes(snapshot)
started = datetime.datetime.now(datetime.timezone.utc).isoformat()
clock = time.monotonic()
maximum = 0
interrupted = False
print('START', unit, started, ' '.join(command), flush=True)
with (OUT/(unit+'.log')).open('w') as log:
    process = subprocess.Popen(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
    (OUT/(unit+'.pid')).write_text(str(process.pid))
    def stop(sig, frame):
        global interrupted
        interrupted = True
        os.killpg(process.pid, signal.SIGTERM)
    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)
    while process.poll() is None:
        time.sleep(1)
        for row in subprocess.check_output(['ps', '-axo', 'pid,ppid,rss,command'], text=True).splitlines():
            cells = row.strip().split(None, 3)
            if len(cells) == 4 and cells[0].isdigit() and '/idris2_app/idris2' in cells[3]:
                maximum = max(maximum, int(cells[2]))
        if maximum > 48*1024*1024 and not interrupted:
            stop(signal.SIGTERM, None)
text = (OUT/(unit+'.log')).read_text()
fresh = path == 'package' or bool(re.search(r'^\d+/\d+: Building DGamma\.'+re.escape(pathlib.Path(path).stem)+r' \('+re.escape(path)+r'\)$', text, re.M))
passed = fresh and not interrupted and (process.returncode == 0 and 'Error:' not in text if not diagnostic
          else process.returncode != 0 and diagnostic in text and (not symbol or symbol in text))
record = dict(unit=unit,path=path,command=command,start=started,
              end=datetime.datetime.now(datetime.timezone.utc).isoformat(),seconds=time.monotonic()-clock,
              exit=process.returncode,fresh=fresh,passed=passed,interrupted=interrupted,
              maxSampleRSSKiB=maximum,sourceSHA256=hashlib.sha256(snapshot).hexdigest(),
              expectedDiagnostic=diagnostic,symbol=symbol,transcript=text)
(OUT/(unit+'.json')).write_text(json.dumps(record,indent=2)+'\n')
with (OUT/'ledger.jsonl').open('a') as ledger:
    ledger.write(json.dumps(record)+'\n')
print(text, flush=True)
print('RESULT',json.dumps({k:v for k,v in record.items() if k!='transcript'}),flush=True)
sys.exit(0 if passed else 1)
