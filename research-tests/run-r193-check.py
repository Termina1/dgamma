#!/usr/bin/env python3
"""One serialized, seeded, fresh R193 check. Launch detached with python3 -I.
No TTC is deleted. JSON/log/source snapshots live under /tmp/dgamma-r193.
Usage: run-r193-check.py UNIT PATH [DIAGNOSTIC [SYMBOL]]; PATH=package for build.
"""
import atexit
import datetime
import shutil
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
OUT = pathlib.Path('/tmp/dgamma-r193')
OUT.mkdir(exist_ok=True)
def compiler_scopes():
    owned, lane2, unknown = [], [], []
    for row in subprocess.check_output(['ps','-axo','pid,ppid,command'], text=True).splitlines():
        cells = row.strip().split(None, 2)
        if len(cells) != 3 or not re.search(r'/idris2_app/idris2(?:\.so)?(?:\s|$)', cells[2]):
            continue
        cwd_probe = subprocess.run(['lsof','-a','-p',cells[0],'-d','cwd','-Fn'],capture_output=True,text=True)
        directories = [line[1:] for line in cwd_probe.stdout.splitlines() if line.startswith('n')]
        if str(ROOT)+'/' in cells[2] or str(ROOT) in directories:
            owned.append(row)
        elif '/Users/vyacheslavshebanov/Work/dgamma-lane2/' in cells[2] or '/Users/vyacheslavshebanov/Work/dgamma-lane2' in directories:
            lane2.append(row)
        else:
            unknown.append(row)
    return owned, lane2, unknown

unit, path = sys.argv[1:3]
diagnostic = sys.argv[3] if len(sys.argv) > 3 else None
symbol = sys.argv[4] if len(sys.argv) > 4 else None
assert not (OUT/(unit+'.json')).exists(), 'Invocation names are append-only'
# R193: no proof/new attempt in final40min; hash-frozen validation may
# start until final25min. Start20:25:44Z, timeout00:25:44Z.
planned_validation = False
rss_limit_kib = 48*1024*1024
continuation_sha = None
if unit == 'V2R1':
    import runpy
    authenticate = runpy.run_path(str(ROOT/'research-tests/r193_validation_continuation.py'))['authenticate']
    continuation, effective_plan = authenticate(ROOT, OUT)
    retry = continuation['retry']
    assert path == retry['path'] and diagnostic is None and symbol is None
    rss_limit_kib = continuation['retryRSSLimitKiB']
    continuation_sha = hashlib.sha256((OUT/'final-validation-continuation.json').read_bytes()).hexdigest()
    planned_validation = True
elif re.fullmatch(r'V\d+', unit):
    plan_bytes = (OUT/'final-validation-plan.json').read_bytes()
    assert hashlib.sha256(plan_bytes).hexdigest() == (OUT/'final-validation-plan.sha256').read_text().strip(), 'Frozen validation plan changed'
    items = [item for item in json.loads(plan_bytes) if item['unit'] == unit]
    assert len(items) == 1 and items[0]['path'] == path and items[0]['expectedDiagnostic'] == diagnostic and items[0].get('symbol') == symbol
    planned_source = ROOT/('dgamma.ipkg' if path == 'package' else path)
    assert hashlib.sha256(planned_source.read_bytes()).hexdigest() == items[0]['sourceHash']
    planned_validation = True
cutoff = datetime.datetime(2026,9,9,0,0,44,tzinfo=datetime.timezone.utc) if planned_validation else datetime.datetime(2026,9,8,23,45,44,tzinfo=datetime.timezone.utc)
assert datetime.datetime.now(datetime.timezone.utc) < cutoff, 'R193 attempt23:45:44 / frozen-validation00:00:44 start guard'
owned_compilers, lane2_compilers, unknown_compilers = compiler_scopes()
assert not owned_compilers and not unknown_compilers, 'Own/unknown compiler active; never kill lane2'
if lane2_compilers:
    print('lane-2 compiler (separate worktree)', lane2_compilers, flush=True)
command = ['idris2', '--source-dir', str(ROOT/'src'), '--source-dir', str(ROOT/'research')]
if path == 'package':
    command = ['idris2', '--build', str(ROOT/'dgamma.ipkg')]
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
    target.touch()
    if path.startswith('research-tests/'):
        command += ['--source-dir', str(ROOT/'research-tests')]
    command += ['--check', str(target)]
(OUT/(unit+'.source')).write_bytes(snapshot)
# Supervisor-approved worktree-scoped concurrency and shared heavy lock.
heavy_paths = set(json.loads((ROOT/'research-tests/O6-R193-HEAVY-PATHS.json').read_text()))
heavy = path in heavy_paths or pathlib.Path(path).stem.startswith('R8')
if unit == 'V2R1':
    assert heavy, 'The exceptional52GiB retry must hold the heavy lock'
lock = pathlib.Path('/tmp/dgamma-heavy.lock')
lock_owner = dict(lane='R193-main',pid=os.getpid(),timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),unit=unit,path=path)
lock_acquired = False
lock_events = []
def release_lock():
    if lock_acquired and lock.is_dir():
        observed = (lock/'owner').read_text()
        if observed == json.dumps(lock_owner):
            shutil.rmtree(lock)
            print('HEAVY LOCK RELEASE',unit,flush=True)
atexit.register(release_lock)
if heavy:
    lock_started = time.monotonic()
    while not lock_acquired:
        try:
            lock.mkdir()
            (lock/'owner').write_text(json.dumps(lock_owner))
            lock_acquired = True
            lock_events.append(dict(event='acquired',**lock_owner))
        except FileExistsError:
            age = time.time()-lock.stat().st_mtime
            owner_text = (lock/'owner').read_text() if (lock/'owner').exists() else ''
            owner_pid = None
            try:
                owner_pid = int(json.loads(owner_text)['pid'])
            except (ValueError,KeyError,TypeError):
                match = re.search(r'pid[=: ]+(\d+)',owner_text)
                if match: owner_pid = int(match[1])
            owner_dead = False
            if owner_pid:
                try: os.kill(owner_pid,0)
                except ProcessLookupError: owner_dead = True
            if age > 25*60 and owner_dead:
                event=dict(event='removed-stale-dead-owner-lock',age=age,owner=owner_text)
                lock_events.append(event)
                print(event,flush=True)
                shutil.rmtree(lock)
                continue
            assert time.monotonic()-lock_started < 20*60, 'Heavy-lock wait exceeded20min; no compiler launched'
            print('HEAVY LOCK WAIT',unit,owner_text,flush=True)
            time.sleep(10)
    assert datetime.datetime.now(datetime.timezone.utc) < cutoff, 'Cutoff passed while awaiting heavy lock'
    owned_compilers, lane2_compilers, unknown_compilers = compiler_scopes()
    assert not owned_compilers and not unknown_compilers
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
            if len(cells) == 4 and cells[0].isdigit() and '/idris2_app/idris2' in cells[3] and str(ROOT)+'/' in cells[3]:
                maximum = max(maximum, int(cells[2]))
        if maximum > rss_limit_kib and not interrupted:
            stop(signal.SIGTERM, None)
text = (OUT/(unit+'.log')).read_text()
fresh = path == 'package' or bool(re.search(r'^\d+/\d+: Building DGamma\.'+re.escape(pathlib.Path(path).stem)+r' \('+r'(?:'+re.escape(path)+'|'+re.escape(str(ROOT/path))+r')\)$', text, re.M))
passed = fresh and not interrupted and (process.returncode == 0 and 'Error:' not in text if not diagnostic
          else process.returncode != 0 and diagnostic in text and (not symbol or symbol in text))
record = dict(unit=unit,path=path,command=command,start=started,
              end=datetime.datetime.now(datetime.timezone.utc).isoformat(),seconds=time.monotonic()-clock,
              exit=process.returncode,fresh=fresh,passed=passed,interrupted=interrupted,
              maxSampleRSSKiB=maximum,rssLimitKiB=rss_limit_kib,validationContinuationSHA256=continuation_sha,
              sourceSHA256=hashlib.sha256(snapshot).hexdigest(),
              expectedDiagnostic=diagnostic,symbol=symbol,transcript=text,
              compilerScope='main worktree only', lane2Compilers=lane2_compilers, heavyLock=lock_events)
(OUT/(unit+'.json')).write_text(json.dumps(record,indent=2)+'\n')
with (OUT/'ledger.jsonl').open('a') as ledger:
    ledger.write(json.dumps(record)+'\n')
print(text, flush=True)
print('RESULT',json.dumps({k:v for k,v in record.items() if k!='transcript'}),flush=True)
sys.exit(0 if passed else 1)
