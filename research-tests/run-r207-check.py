#!/usr/bin/env python3
"""Detached R207 exact-source check; one owned compiler, no shared locks.
Usage: python3 -I research-tests/run-r207-check.py INVOCATION PATH
Fresh own Building only; package is seeded and must produce no Building.
LocalDiamond52GiB, all other permitted targets48GiB. Production is never a
fresh target; in particular SupportSolution/TTC is not touched. Only the
spawned own process group can be terminated. RSS is maximum sampled
command-matching compiler RSS, not OS high-water or aggregate tree memory.
"""
import sys, pathlib, os, signal, time, subprocess, json, re
sys.dont_write_bytecode=True
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from r207_common import *

unit,path=sys.argv[1:3]; OUT.mkdir(exist_ok=True)
assert re.fullmatch(r'[A-Za-z0-9_-]+',unit)
assert not (OUT/(unit+'.json')).exists() and not (OUT/(unit+'.log')).exists(), 'Append-only invocation'
own,foreign,unknown=compiler_scopes(); assert not own and not unknown, 'Own/unknown compiler already active'
assert_frozen()
assert not git('diff','--cached','--name-only').strip()
assert not git('diff', START, '--', 'src/', 'dgamma.ipkg'), 'Production frozen at seal'
assert not path.startswith('src/'), 'Production validation is seeded package only; never touch SupportSolution TTC'
production_paths=[p for p in source_paths() if p.startswith('src/')]+['dgamma.ipkg']
production={p:sha((ROOT/p).read_bytes()) for p in production_paths}
current_paths=source_paths()
source_manifest={p:sha((ROOT/p).read_bytes()) for p in current_paths}
source=ROOT/('dgamma.ipkg' if path=='package' else path)
assert source.is_file() and source.stat().st_size>0
snapshot=source.read_bytes()
source_manifest[str(source.relative_to(ROOT))]=sha(snapshot)
source_dirs=['src'] if path.startswith('src/') else ['src','research'] if path.startswith('research/') else ['src','research','research-tests']
command=['idris2','--build',str(source)] if path=='package' else ['idris2']+[arg for directory in source_dirs for arg in ['--source-dir',str(ROOT/directory)]]+['--check',str(source)]
expected=None; symbol=None
contracts=json.loads((ROOT/'research-tests/O6-R205-NEGATIVE-PREFLIGHT.json').read_text())['contracts']
if path in contracts:
    contract=contracts[path]
    assert contract['sourceSHA256']==sha(snapshot), 'Changed negative contract requires new gate'
    expected=contract['expectedDiagnostic'];symbol=contract['symbol']
assert utc() < ('2026-09-10T08:18:00' if unit.startswith(('V','P')) else '2026-09-10T08:03:00'), 'R207 proof/validation cutoff'
assert not unit.startswith('C'), 'Unit C ineligible: A/B not closed'
if path!='package':
    if path in PROTECTED_PATHS or any(w in path for w in ['CP5L2R','L2R','ActorLifecycleOnlyExtended','CP5AvailabilityAware']):
        assert snapshot == subprocess.check_output(['git','show',START+':'+path],cwd=ROOT) or path=='research/DGamma/CP5ActorLifecycleOnlyExtended.idr'
    if re.fullmatch(r'(?:U0|E|VREST|A|B)\d+-\d+',unit):
        old=subprocess.run(['git','show','HEAD:'+path],cwd=ROOT,capture_output=True)
        def declarations(data):
            return set(re.findall(r'^(?:[01] )?([A-Za-z_]\w*)\s*:',data.decode(),re.M)+re.findall(r'^(?:record|data)\s+([A-Za-z_]\w*)',data.decode(),re.M))
        added=declarations(snapshot)-declarations(old.stdout if old.returncode==0 else b'')
        assert len(added)<=1, 'One new top-level declaration per invocation'
        cap_unit=re.fullmatch(r'(U0|E|VREST|A|B)(\d+)-\d+',unit)
        assert 1<=int(cap_unit[2])<=dict(U0=10,E=26,VREST=1,A=16,B=16)[cap_unit[1]], 'Micro-unit cap'
        assert int(unit.rsplit('-',1)[1])<=3
        previous=[r for r in records() if r['unit'].rsplit('-',1)[0]==unit.rsplit('-',1)[0]]
        assert len(previous)<3, 'Three invocations per micro-unit'
    source.touch()
limit=(52 if path.endswith('/CP5ConfluenceLocalDiamondSpike.idr') else 48)*1024*1024
seeded_package=path=='package'
(OUT/(unit+'.source')).write_bytes(snapshot)
(OUT/(unit+'.runner.py')).write_bytes(pathlib.Path(__file__).read_bytes())
(OUT/(unit+'.common.py')).write_bytes((ROOT/'research-tests/r207_common.py').read_bytes())
write_json(OUT/(unit+'.sources.json'),source_manifest)
start=utc(); clock=time.monotonic(); samples=[]; overlaps=[start] if foreign else []
mutation=[]; interrupted=False; resource=False; multiple=False; maximum=0
print('START',unit,start,' '.join(command),'guardKiB',limit,flush=True)
with (OUT/(unit+'.log')).open('w') as log:
    process=subprocess.Popen(command,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
    (OUT/(unit+'.pid')).write_text(str(process.pid))
    def stop(sig=None, frame=None):
        global interrupted
        interrupted=True
        if process.poll() is None: os.killpg(process.pid,signal.SIGTERM)
    signal.signal(signal.SIGTERM,stop); signal.signal(signal.SIGINT,stop)
    while process.poll() is None:
        time.sleep(1)
        rows=subprocess.check_output(['ps','-axo','pid,ppid,rss,command'],text=True).splitlines()
        ours=[]; foreign_active=False
        for row in rows:
            cells=row.strip().split(None,3)
            if len(cells)!=4 or not cells[0].isdigit() or not re.search(r'/idris2_app/idris2(?:\.so)?(?:\s|$)',cells[3]): continue
            if str(ROOT)+'/' in cells[3]: ours.append((int(cells[0]),int(cells[2])))
            elif '/Users/vyacheslavshebanov/Work/dgamma-lane2/' in cells[3]: foreign_active=True
        sample=max([r[1] for r in ours] or [0]); maximum=max(maximum,sample)
        stamp=utc(); samples.append(dict(timestampUTC=stamp,rssKiB=sample,ownedPids=[r[0] for r in ours]))
        if foreign_active: overlaps.append(stamp)
        if len(ours)>1: multiple=True; stop()
        if maximum>limit: resource=True; stop()
        if len(samples)%5==0 or interrupted:
            mutation=[p for p,h in source_manifest.items() if not (ROOT/p).exists() or sha((ROOT/p).read_bytes())!=h]
            if sha((ROOT/'dgamma.ipkg').read_bytes())!=production['dgamma.ipkg']: mutation.append('dgamma.ipkg')
            if mutation: stop()
        if len(samples)%15==0:
            write_json(OUT/'active.json',dict(unit=unit,path=path,start=start,pid=process.pid,elapsed=time.monotonic()-clock,peakRSSKiB=maximum,guardKiB=limit,lastSampleUTC=stamp))
        if interrupted and process.poll() is None:
            try: process.wait(timeout=10)
            except subprocess.TimeoutExpired: os.killpg(process.pid,signal.SIGKILL)
text=(OUT/(unit+'.log')).read_text(); building=re.findall(r'^\d+/\d+: Building (.+)$',text,re.M)
module=None if path=='package' else re.search(r'^module\s+([\w.]+)',snapshot.decode(),re.M)[1]
expected_build=module+' ('+str(source)+')' if module else None
unexpected=(building if seeded_package else []) if path=='package' else [b for i,b in enumerate(building) if b!=expected_build or i>0]
fresh=(not building if seeded_package else bool(building)) if path=='package' else building==[expected_build]
post_mutation=[p for p,h in source_manifest.items() if not (ROOT/p).exists() or sha((ROOT/p).read_bytes())!=h]
mutation=sorted(set(mutation+post_mutation))
diagnostic_ok=(process.returncode==1 and expected in text and symbol and symbol in text) if expected else (process.returncode==0 and 'Error:' not in text)
passed=bool(fresh and diagnostic_ok and not interrupted and not mutation and not unexpected and not multiple and maximum<=limit)
record=dict(unit=unit,path=path,command=command,start=start,end=utc(),seconds=time.monotonic()-clock,exit=process.returncode,passed=passed,fresh=fresh,seededPackageNoBuilding=seeded_package,expectedDiagnostic=expected,symbol=symbol,buildingLines=building,unexpectedBuilding=unexpected,targetMutationDetected=bool(mutation),mutatedPaths=mutation,interrupted=interrupted,resourceStopped=resource,multipleOwnedCompilers=multiple,maxSampleRSSKiB=maximum,rssLimitKiB=limit,rssSamples=samples,sourceSHA256=sha(snapshot),sourceManifestSHA256=sha((OUT/(unit+'.sources.json')).read_bytes()),headAtEnd=git('rev-parse','HEAD').strip(),CP3Blob=git('hash-object','src/DGamma/CP3.idr').strip(),runnerSHA256=sha((OUT/(unit+'.runner.py')).read_bytes()),commonSHA256=sha((OUT/(unit+'.common.py')).read_bytes()),crossLaneOverlapTimestampsUTC=overlaps,transcript=text)
write_json(OUT/(unit+'.json'),record)
with (OUT/'ledger.jsonl').open('a') as f: f.write(json.dumps(record)+'\n')
write_json(OUT/'active.json',dict(status='IDLE',lastInvocation=unit,end=record['end']))
print('RESULT',json.dumps({k:v for k,v in record.items() if k not in ['rssSamples','transcript']}),flush=True)
sys.exit(0 if passed else 1)
