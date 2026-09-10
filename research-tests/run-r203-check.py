#!/usr/bin/env python3
"""One serialized, seeded, fresh R203 check. Launch detached with python3 -I.
No TTC is deleted. JSON/log/source snapshots live under /tmp/dgamma-r203.
Usage: run-r203-check.py UNIT PATH [DIAGNOSTIC [SYMBOL]]; PATH=package for build.
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
OUT = pathlib.Path('/tmp/dgamma-r203')
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
# R203 start18:28Z; timeout22:28Z; no new proofs21:48Z; validation by22:03Z.
planned_validation = False
rss_limit_kib = 48*1024*1024
continuation_sha = None
if re.fullmatch(r'V\d+', unit):
    plan_bytes = (OUT/'final-validation-plan.json').read_bytes()
    assert hashlib.sha256(plan_bytes).hexdigest() == (OUT/'final-validation-plan.sha256').read_text().strip(), 'Frozen validation plan changed'
    items = [item for item in json.loads(plan_bytes) if item['unit'] == unit]
    assert len(items) == 1 and items[0]['path'] == path and items[0]['expectedDiagnostic'] == diagnostic and items[0].get('symbol') == symbol
    planned_source = ROOT/('dgamma.ipkg' if path == 'package' else path)
    assert hashlib.sha256(planned_source.read_bytes()).hexdigest() == items[0]['sourceHash']
    planned_validation = True
    continuation_sha = hashlib.sha256(plan_bytes).hexdigest()
cutoff = datetime.datetime(2026,9,9,22,3,0,tzinfo=datetime.timezone.utc) if planned_validation else datetime.datetime(2026,9,9,21,48,0,tzinfo=datetime.timezone.utc)
assert datetime.datetime.now(datetime.timezone.utc) < cutoff, 'R203 attempt21:48:00 / frozen-validation22:03:00 start guard'
owned_compilers, lane2_compilers, unknown_compilers = compiler_scopes()
assert not owned_compilers and not unknown_compilers, 'Own/unknown compiler active; never kill lane2'
# Owner permits cross-lane overlap; record timestamps only, never foreign commands.
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
    assert not any(word in path for word in ['CP5L2R','L2R']), 'Lane-created target absent from inherited applicable list'
    # Owner's preflight ruling permits inherited MAIN-baseline variant modules,
    # not lane2 results or worktree access. These targets must remain byte-pinned.
    if any(word in path for word in ['ActorLifecycleOnlyExtended','CP5AvailabilityAware']):
        assert planned_validation and snapshot == subprocess.check_output(['git','show','77e94c81:'+path],cwd=ROOT)
    target.touch()
    if path.startswith('research-tests/'):
        command += ['--source-dir', str(ROOT/'research-tests')]
    if os.environ.get('DGAMMA_SHOW_IMPLICITS') == '1':
        command += ['--show-implicits']
    command += ['--check', str(target)]
(OUT/(unit+'.source')).write_bytes(snapshot)
# R203 starts under the already-effective owner no-lock rule.
policy_bytes = (OUT/'execution-policy.json').read_bytes()
policy = json.loads(policy_bytes)
assert policy['authorization'] == 'SUPERVISOR RULE CHANGE: CROSS-LANE HEAVY LOCK ABOLISHED'
assert hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest() == policy['runnerSHA256']
policy_sha = hashlib.sha256(policy_bytes).hexdigest()
lock_events = []
assert not subprocess.check_output(['git','diff','34b21c9','--','src/','dgamma.ipkg'],cwd=ROOT)
for frozen in ['CP5ConfluenceLocalDiamondSpike','CP5ConfluenceDeletionChainSpike','CP5O19SurfaceSpike','CP5ConfluenceCrossTraceSpike','CP5ConfluenceCanonicalSortSpike','CP5ConfluenceRenamingCompositionSpike']:
    fp='research/DGamma/'+frozen+'.idr'
    assert (ROOT/fp).read_bytes()==subprocess.check_output(['git','show','77e94c81:'+fp],cwd=ROOT), 'Frozen source changed: '+fp
if path=='research/DGamma/CP5UniqueRawNameOrdinalCapital.idr':
    assert planned_validation and snapshot==subprocess.check_output(['git','show','77e94c81:'+path],cwd=ROOT)
    assert json.loads((OUT/'shift.json').read_text())['uniqueOrdinalGate'].startswith('APPROVED')
if path == 'research/DGamma/CP5ConfluenceLocalDiamondSpike.idr':
    assert planned_validation
    assert snapshot == subprocess.check_output(['git','show','77e94c81:'+path],cwd=ROOT), 'Changed LocalDiamond requires prior gate'
    rss_limit_kib = 52*1024*1024
if planned_validation:
    assert rss_limit_kib == items[0]['rssLimitKiB']
# Deliberately never acquire, inspect, poll or remove any shared lock path.
started = datetime.datetime.now(datetime.timezone.utc).isoformat()
clock = time.monotonic()
maximum = 0
interrupted = False
mutation_detected = False
resource_stopped = False
samples = []
overlap_timestamps = [started] if lane2_compilers else []
print('START', unit, started, ' '.join(command), flush=True)
with (OUT/(unit+'.log')).open('w') as log:
    process = subprocess.Popen(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
    (OUT/(unit+'.pid')).write_text(str(process.pid))
    def stop(sig, frame):
        global interrupted
        interrupted = True
        if process.poll() is None:
            os.killpg(process.pid, signal.SIGTERM)
    signal.signal(signal.SIGTERM, stop)
    signal.signal(signal.SIGINT, stop)
    while process.poll() is None:
        time.sleep(1)
        current = (ROOT/('dgamma.ipkg' if path == 'package' else path))
        if (not current.exists() or current.read_bytes() != snapshot) and not interrupted:
            mutation_detected = True
            stop(signal.SIGTERM, None)
        sample_max = 0
        foreign_active = False
        for row in subprocess.check_output(['ps', '-axo', 'pid,ppid,rss,command'], text=True).splitlines():
            cells = row.strip().split(None, 3)
            if len(cells) == 4 and cells[0].isdigit() and '/idris2_app/idris2' in cells[3] and str(ROOT)+'/' in cells[3]:
                sample_max = max(sample_max, int(cells[2]))
            if len(cells) == 4 and cells[0].isdigit() and re.search(r'/idris2_app/idris2(?:\.so)?(?:\s|$)', cells[3]) and '/Users/vyacheslavshebanov/Work/dgamma-lane2/' in cells[3]:
                foreign_active = True
        if foreign_active:
            overlap_timestamps.append(datetime.datetime.now(datetime.timezone.utc).isoformat())
        maximum = max(maximum, sample_max)
        samples.append(dict(timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),rssKiB=sample_max))
        if maximum > rss_limit_kib and not interrupted:
            resource_stopped = True
            stop(signal.SIGTERM, None)
text = (OUT/(unit+'.log')).read_text()
building_lines=re.findall(r'^\d+/\d+: Building (.+)$',text,re.M)
expected_building='DGamma.'+pathlib.Path(path).stem+' ('+str(ROOT/path)+')'
unexpected_builds=[] if path=='package' else [b for i,b in enumerate(building_lines) if b != expected_building or i > 0]

fresh = path == 'package' or bool(re.search(r'^\d+/\d+: Building DGamma\.'+re.escape(pathlib.Path(path).stem)+r' \('+r'(?:'+re.escape(path)+'|'+re.escape(str(ROOT/path))+r')\)$', text, re.M))
passed = fresh and not interrupted and not unexpected_builds and (process.returncode == 0 and 'Error:' not in text if not diagnostic
          else process.returncode != 0 and diagnostic in text and (not symbol or symbol in text))
record = dict(unit=unit,path=path,command=command,start=started,
              end=datetime.datetime.now(datetime.timezone.utc).isoformat(),seconds=time.monotonic()-clock,
              exit=process.returncode,fresh=fresh,passed=passed,interrupted=interrupted,
              targetMutationDetected=mutation_detected, resourceStopped=resource_stopped, unexpectedBuilding=unexpected_builds, buildingLines=building_lines, rssSamples=samples, maxSampleRSSKiB=maximum,rssLimitKiB=rss_limit_kib,validationContinuationSHA256=continuation_sha,
              sourceSHA256=hashlib.sha256(snapshot).hexdigest(),runnerSHA256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
              expectedDiagnostic=diagnostic,symbol=symbol,transcript=text,
              compilerScope='main worktree only', lane2Compilers=[], heavyLock=lock_events,
              executionPolicySHA256=policy_sha, crossLaneHeavyChecksPermitted=True,
              crossLaneOverlapTimestampsUTC=overlap_timestamps)
(OUT/(unit+'.json')).write_text(json.dumps(record,indent=2)+'\n')
with (OUT/'ledger.jsonl').open('a') as ledger:
    ledger.write(json.dumps(record)+'\n')
print(text, flush=True)
print('RESULT',json.dumps({k:v for k,v in record.items() if k!='transcript'}),flush=True)
sys.exit(0 if passed else 1)
