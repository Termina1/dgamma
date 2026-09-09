#!/usr/bin/env python3
"""One serialized, seeded, fresh R196 check. Launch detached with python3 -I.
No TTC is deleted. JSON/log/source snapshots live under /tmp/dgamma-r196.
Usage: run-r196-check.py UNIT PATH [DIAGNOSTIC [SYMBOL]]; PATH=package for build.
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
OUT = pathlib.Path('/tmp/dgamma-r196')
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
# A stages are exact hash-pinned approved edits; B is a sealed topological plan.
manifest_path=ROOT/'research-tests/O6-R196-ROOT-CONTRACT-EXECUTION.json'
manifest_bytes=manifest_path.read_bytes()
assert hashlib.sha256(manifest_bytes).hexdigest()==(OUT/'execution-manifest.sha256').read_text().strip()
manifest=json.loads(manifest_bytes)
planned_validation=False
rss_limit_kib=48*1024*1024
continuation_sha=None
stage=unit.rsplit('-',1)[0]
approved_edit=next((x for x in manifest['items'] if x['unit']==stage),None)
if unit=='A4-2':
    amendment_bytes=(ROOT/'research-tests/O6-R196-A4-SYNTAX-AMENDMENT.json').read_bytes()
    assert hashlib.sha256(amendment_bytes).hexdigest()==(pathlib.Path('/tmp/dgamma-r196')/'A4-syntax-amendment.sha256').read_text().strip()
    approved_edit=json.loads(amendment_bytes)

if re.fullmatch(r'B\d+',unit):
    plan_bytes=(ROOT/'research-tests/O6-R196-DEPENDENT-RECHECK-PLAN.json').read_bytes()
    assert hashlib.sha256(plan_bytes).hexdigest()==(OUT/'dependent-plan.sha256').read_text().strip()
    items=[x for x in json.loads(plan_bytes)['items'] if x['unit']==unit]
    assert len(items)==1 and items[0]['path']==path and items[0]['expectedDiagnostic']==diagnostic and items[0].get('symbol')==symbol
    assert hashlib.sha256((ROOT/('dgamma.ipkg' if path=='package' else path)).read_bytes()).hexdigest()==items[0]['sourceHash']
    for dep in items[0]['dependencies']:
        done=[json.loads(s) for s in (OUT/'ledger.jsonl').read_text().splitlines()]
        assert any(x['path']==dep and x['passed'] and x['sourceSHA256']==hashlib.sha256((ROOT/dep).read_bytes()).hexdigest() for x in done), 'Dependency not directly rechecked: '+dep
    planned_validation=True
cutoff=datetime.datetime(2026,9,9,7,19,35,tzinfo=datetime.timezone.utc) if planned_validation else datetime.datetime(2026,9,9,7,4,35,tzinfo=datetime.timezone.utc)
assert datetime.datetime.now(datetime.timezone.utc)<cutoff, 'R196 proof07:04:35 / validation07:19:35 start cutoff'
assert not subprocess.check_output(['git','diff','34b21c9','--','src/','dgamma.ipkg'],cwd=ROOT)
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
    if approved_edit:
        assert approved_edit['path']==path
        assert hashlib.sha256(snapshot).hexdigest()==approved_edit['afterSHA256'], 'Unapproved A bytes'
        assert hashlib.sha256(subprocess.check_output(['git','show','HEAD:'+path],cwd=ROOT)).hexdigest()==approved_edit['beforeSHA256'], 'A preimage mismatch'
    elif re.fullmatch(r'C\d+-\d+',unit):
        old=subprocess.run(['git','show','HEAD:'+path],cwd=ROOT,capture_output=True)
        def declarations(data):
            return set(re.findall(r'^(?:[01] )?([A-Za-z_]\w*)\s*:',data.decode(),re.M)+re.findall(r'^(?:record|data)\s+([A-Za-z_]\w*)',data.decode(),re.M))
        assert len(declarations(snapshot)-declarations(old.stdout if old.returncode==0 else b''))==1
    else:
        assert planned_validation or unit.startswith('S'), 'Unclassified invocation'
    assert not any(word in path for word in ['CP5L2R','L2R']), 'Lane-created result target prohibited'
    # Owner's preflight ruling permits inherited MAIN-baseline variant modules,
    # not lane2 results or worktree access. These targets must remain byte-pinned.
    if any(word in path for word in ['ActorLifecycleOnlyExtended','CP5AvailabilityAware']):
        assert planned_validation and snapshot == subprocess.check_output(['git','show','58f88c63:'+path],cwd=ROOT)
    target.touch()
    if path.startswith('research-tests/'):
        command += ['--source-dir', str(ROOT/'research-tests')]
    command += ['--check', str(target)]
(OUT/(unit+'.source')).write_bytes(snapshot)
# One dedicated detached owner holds the shared lock continuously through A/B.
heavy_paths=set(json.loads((ROOT/'research-tests/O6-R195-HEAVY-PATHS.json').read_text()))
heavy=True
lock=pathlib.Path('/tmp/dgamma-heavy.lock')
lock_owner=json.loads((OUT/'window-owner.json').read_text())
assert lock_owner['lane']=='R196-main' and (lock/'owner').read_text()==json.dumps(lock_owner)
os.kill(lock_owner['pid'],0)
window=json.loads(pathlib.Path('/tmp/dgamma-rebuild-window.json').read_text())
assert window['pid']==lock_owner['pid'] and window['lane']=='R196-main'
lock_events=[dict(event='continuous-window-owned',**lock_owner)]
if path=='research/DGamma/CP5ConfluenceLocalDiamondSpike.idr':
    assert approved_edit and stage in ['A1','A2'], 'LocalDiamond only exact owner-gated stages'
    rss_limit_kib=52*1024*1024
else:
    inventory=json.loads((ROOT/'research-tests/O6-R195-ROOT-CONTRACT-COSTS.json').read_text())
    cost=next((x for x in inventory['entries'] if x['path']==path),None)
    assert not cost or (cost['estimatedSampleRSSKiB'] or 0)<=40*1024*1024, 'Per-module measured>40GiB requires new owner gate'
started = datetime.datetime.now(datetime.timezone.utc).isoformat()
clock = time.monotonic()
maximum = 0
interrupted = False
mutation_detected = False
resource_stopped = False
samples = []
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
        for row in subprocess.check_output(['ps', '-axo', 'pid,ppid,rss,command'], text=True).splitlines():
            cells = row.strip().split(None, 3)
            if len(cells) == 4 and cells[0].isdigit() and '/idris2_app/idris2' in cells[3] and str(ROOT)+'/' in cells[3]:
                sample_max = max(sample_max, int(cells[2]))
        maximum = max(maximum, sample_max)
        samples.append(dict(timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),rssKiB=sample_max))
        if maximum > rss_limit_kib and not interrupted:
            resource_stopped = True
            stop(signal.SIGTERM, None)
text = (OUT/(unit+'.log')).read_text()
building_lines=re.findall(r'^\d+/\d+: Building (.+)$',text,re.M)
unexpected_builds=[] if path=='package' else [b for b in building_lines if not b.startswith('DGamma.'+pathlib.Path(path).stem+' (')]

fresh = path == 'package' or bool(re.search(r'^\d+/\d+: Building DGamma\.'+re.escape(pathlib.Path(path).stem)+r' \('+r'(?:'+re.escape(path)+'|'+re.escape(str(ROOT/path))+r')\)$', text, re.M))
passed = fresh and not interrupted and not unexpected_builds and (process.returncode == 0 and 'Error:' not in text if not diagnostic
          else process.returncode != 0 and diagnostic in text and (not symbol or symbol in text))
record = dict(unit=unit,path=path,command=command,start=started,
              end=datetime.datetime.now(datetime.timezone.utc).isoformat(),seconds=time.monotonic()-clock,
              exit=process.returncode,fresh=fresh,passed=passed,interrupted=interrupted,
              targetMutationDetected=mutation_detected, resourceStopped=resource_stopped, unexpectedBuilding=unexpected_builds, buildingLines=building_lines, rssSamples=samples, maxSampleRSSKiB=maximum,rssLimitKiB=rss_limit_kib,validationContinuationSHA256=continuation_sha,
              sourceSHA256=hashlib.sha256(snapshot).hexdigest(),
              expectedDiagnostic=diagnostic,symbol=symbol,transcript=text,
              compilerScope='main worktree only', lane2Compilers=lane2_compilers, heavyLock=lock_events)
(OUT/(unit+'.json')).write_text(json.dumps(record,indent=2)+'\n')
with (OUT/'ledger.jsonl').open('a') as ledger:
    ledger.write(json.dumps(record)+'\n')
print(text, flush=True)
print('RESULT',json.dumps({k:v for k,v in record.items() if k!='transcript'}),flush=True)
sys.exit(0 if passed else 1)
