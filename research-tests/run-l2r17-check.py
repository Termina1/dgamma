#!/usr/bin/env python3
"""Copied from L2R16; L2R17 bounded new-source/validation runner.
One new declaration per U/X/N/P invocation, <=3 attempts; caps 6/14/14/6.
TYPE checks are not inhabitants; status is recorded in the declaration ledger.
RSS = maximum sampled RSS over command-matching idris2 processes.
18 GiB light; 48 GiB only if predeclared. Target-only touch, mutation monitor,
one own Building line, support TTC untouched, no locks/windows/foreign signals.
Usage: python3 -I research-tests/run-l2r17-check.py UNIT PATH.
"""
import datetime, hashlib, json, os, pathlib, re, signal, subprocess, sys, time
ROOT = pathlib.Path('/Users/vyacheslavshebanov/Work/dgamma-lane2')
OUT = pathlib.Path('/tmp/dgamma-l2r17')
unit, path = sys.argv[1:3]
assert re.fullmatch(r'(?:[UXNPD][1-9]\d*-[1-3]|V\d+)', unit), 'Bounded attempt or validation ID required'
diagnostic = sys.argv[3] if len(sys.argv)>3 else None
symbol = sys.argv[4] if len(sys.argv)>4 else None
assert pathlib.Path.cwd() == ROOT
assert subprocess.check_output(['git','branch','--show-current'],cwd=ROOT,text=True).strip() == 'cp5-thm73-lane-a8a10'
assert not (OUT/(unit+'.json')).exists(), 'Append-only invocation IDs'
assert path != 'package', 'Whole package and cold rebuild forbidden in this lane'
target = ROOT/path
assert target.is_file() and target.stat().st_size > 0 and target.resolve().is_relative_to(ROOT)
assert path in (OUT/'TARGETS.txt').read_text().splitlines() or path.startswith('research-tests/O6-L2R17-Sources/'), 'Lane-owned inventory or L2R17 sources only'
assert not path.startswith('src/')
assert not any(x in target.name for x in ['CP5O20', 'LocalDiamond']), 'Frozen target forbidden'
plan = json.loads((OUT/'shift.json').read_text())
cutoff = plan['validationCutoff'] if re.fullmatch(r'V\d+',unit) else plan['attemptCutoff']
assert datetime.datetime.now(datetime.timezone.utc).isoformat() < cutoff
support=ROOT/'build/ttc/2025081600/DGamma/CP4SupportSolution.ttc'
support_before=(hashlib.sha256(support.read_bytes()).hexdigest(),support.stat().st_mtime_ns)
assert support_before[0]=='0572d487cd7d341c091a94b5fa1d6d6685eade50c2b618f38ffc19fca7dce340'
snapshot = target.read_bytes()
assert all(line.rstrip() == line for line in snapshot.decode().splitlines()), 'Trailing whitespace: rstrip-only and fresh retry required'
assert snapshot == snapshot.rstrip()+b'\n', 'EOF whitespace: rstrip-only and fresh validation required'
assert '%default total' in snapshot.decode()
assert not re.search(r'\b(?:believe_me|assert_total|postulate|partial)\b|\?[A-Za-z_]', '\n'.join(line.split('--')[0] for line in snapshot.decode().splitlines() if not line.lstrip().startswith('|||'))), 'Forbidden source shape or hole'
bundle=[]


def declarations(data):
 text=data.decode();return set(re.findall(r'^(?:[01] )?([^\W\d]\w*)\s*:',text,re.M)+re.findall(r'^(?:record|data)\s+([A-Za-z_]\w*)',text,re.M))
if re.fullmatch(r'[UXNPD]\d+-\d+',unit):
 assert not (OUT/'source-closed.json').exists()
 assert int(unit.split('-')[0][1:]) <= {'U':6,'X':14,'N':14,'P':6,'D':3}[unit[0]]
 old=subprocess.run(['git','show','HEAD:'+path],cwd=ROOT,capture_output=True)
 assert len(declarations(snapshot)-declarations(old.stdout if old.returncode==0 else b''))==1, 'ONE new declaration'
 assert not re.search(r'\b(?:with|let)\b','\n'.join(l.split('--')[0] for l in snapshot.decode().splitlines() if not l.lstrip().startswith('|||')))
 previous=[json.loads(s) for s in (OUT/'ledger.jsonl').read_text().splitlines()] if (OUT/'ledger.jsonl').exists() else []
 assert sum(r['unit'].rsplit('-',1)[0]==unit.rsplit('-',1)[0] for r in previous)<3
 assert not any(r['passed'] and r['unit'].rsplit('-',1)[0]==unit.rsplit('-',1)[0] for r in previous)
def sources_unchanged(target, snapshot, bundle):
 try:
  return target.read_bytes()==snapshot and all(p.read_bytes()==data for p,data in bundle)
 except OSError:
  return False
def compiler_processes():
 result=[]
 for row in subprocess.check_output(['ps','-axo','pid=,ppid=,rss=,command='],text=True).splitlines():
  cells=row.strip().split(None,3)
  if len(cells)!=4 or pathlib.Path(cells[3].split()[0]).name not in {'chez','scheme','chezscheme','idris2','idris2.so'}:continue
  if '/idris2_app/idris2' not in cells[3]:continue
  lane='lane2' if str(ROOT)+'/' in cells[3] else ('main-lane compiler (separate worktree)' if '/Users/vyacheslavshebanov/Work/dgamma/' in cells[3] else 'unclassified compiler (not owned; never killed)')
  result.append(dict(pid=int(cells[0]),ppid=int(cells[1]),rssKiB=int(cells[2]),command=cells[3],classification=lane))
 return result
initial_procs=compiler_processes()
assert not any(p['classification']=='lane2' for p in initial_procs),'Own compiler already running'
heavy_plan=json.loads((OUT/'HEAVY-TARGETS.json').read_text())
heavy=path in heavy_plan['declared48GiB']
rss_limit=(48 if heavy else 18)*1024*1024
finish_plan=json.loads((OUT/'FINISH-TIMING-PLAN.json').read_text())
deadline_stop=finish_plan['longChecksStopUTC'] if heavy else finish_plan['allChecksStopUTC']
assert datetime.datetime.now(datetime.timezone.utc).isoformat()<deadline_stop, 'Lane finish guard: validation reserve'
deadline_interrupted=False
command=['idris2','--source-dir',str(ROOT/'src'),'--source-dir',str(ROOT/'research')]
if path.startswith('research-tests/'):command+=['--source-dir',str(ROOT/'research-tests')]
source_root = target.parent.parent
command+=['--source-dir',str(source_root),'--check',str(target)]
old_mtime=target.stat().st_mtime_ns
target.touch()  # Supervisor-approved TARGET-only fresh validation exception.
touch_record=dict(path=str(target),oldMtimeNs=old_mtime,newMtimeNs=target.stat().st_mtime_ns,authority='L2R17 task BUILD SEED; target only, unchanged own dependency rebuilds REJECTED')
(OUT/(unit+'.source')).write_bytes(snapshot)
bundle_records=[]
for i,(extra,data) in enumerate(bundle):
 old=extra.stat().st_mtime_ns;extra.touch()
 sourcefile=unit+'.bundle-'+str(i)+'.source';(OUT/sourcefile).write_bytes(data)
 bundle_records.append(dict(path=str(extra.relative_to(ROOT)),sourceSHA256=hashlib.sha256(data).hexdigest(),sourceFile=sourcefile,targetMtimeTouch=dict(path=str(extra),oldMtimeNs=old,newMtimeNs=extra.stat().st_mtime_ns,authority='No companion bundle is authorized in L2R17')))

started=datetime.datetime.now(datetime.timezone.utc).isoformat();clock=time.monotonic()
maximum=0;interrupted=False;source_mutation=False
# L2R17 persists ONLY overlap timestamps from its first invocation.
# No foreign PID, RSS or command metadata is ever written to evidence.
foreign={p['pid']:dict(firstObservedUTC=started,lastObservedUTC=started) for p in initial_procs if p['classification']!='lane2'}
print('START',unit,started,' '.join(command),flush=True)
try:
 with (OUT/(unit+'.log')).open('w') as log:
  process=subprocess.Popen(command,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
  (OUT/(unit+'.pid')).write_text(str(process.pid))
  def stop(sig,frame):
   global interrupted
   interrupted=True
   # Only this exact wrapper-owned process group is ever signalled.
   try:os.killpg(process.pid,signal.SIGTERM)
   except ProcessLookupError:pass  # It finished during the preceding sample.
  signal.signal(signal.SIGTERM,stop);signal.signal(signal.SIGINT,stop)
  while process.poll() is None:
   time.sleep(0.25)
   if datetime.datetime.now(datetime.timezone.utc).isoformat()>=deadline_stop and not interrupted:
    deadline_interrupted=True
    stop(signal.SIGTERM,None)
   if not sources_unchanged(target,snapshot,bundle) and not interrupted:
    source_mutation=True
    stop(signal.SIGTERM,None)
   for p in compiler_processes():
    if p['classification']=='lane2':maximum=max(maximum,p['rssKiB'])
    else:
     stamp=datetime.datetime.now(datetime.timezone.utc).isoformat()
     foreign[p['pid']]=dict(firstObservedUTC=foreign.get(p['pid'],{}).get('firstObservedUTC',stamp),lastObservedUTC=stamp)
   if maximum>rss_limit and not interrupted:stop(signal.SIGTERM,None)
   active_log=(OUT/(unit+'.log')).read_text()
   active_builds=re.findall(r'^\d+/\d+: Building (\S+)',active_log,re.M)
   if any(m!='DGamma.'+target.stem for m in active_builds) and not interrupted:stop(signal.SIGTERM,None)
 if not sources_unchanged(target,snapshot,bundle):
  source_mutation=True;interrupted=True
 assert support_before==(hashlib.sha256(support.read_bytes()).hexdigest(),support.stat().st_mtime_ns), 'SupportSolution TTC must be untouched'
 text=(OUT/(unit+'.log')).read_text()
 fresh=bool(re.search(r'^\d+/\d+: Building DGamma\.'+re.escape(target.stem)+r' \((?:'+re.escape(str(ROOT))+r'/)?'+re.escape(path)+r'\)$',text,re.M))
 bundle_fresh=all(bool(re.search(r'^\d+/\d+: Building DGamma\.'+re.escape(p.stem)+r' \('+re.escape(str(p))+r'\)$',text,re.M)) for p,data in bundle)
 buildingLines=re.findall(r'^\d+/\d+: Building .+$',text,re.M)
 passed=fresh and len(buildingLines)==1 and bundle_fresh and not interrupted and (process.returncode==0 and 'Error:' not in text if not diagnostic else process.returncode!=0 and diagnostic in text and bool(symbol) and symbol in text)
 record=dict(buildingLines=buildingLines,buildingCount=len(buildingLines),bundleSources=bundle_records,bundleFresh=bundle_fresh,unit=unit,path=path,command=command,start=started,end=datetime.datetime.now(datetime.timezone.utc).isoformat(),seconds=time.monotonic()-clock,exit=process.returncode,fresh=fresh,passed=passed,interrupted=interrupted,maxSampleRSSKiB=maximum,sourceSHA256=hashlib.sha256(snapshot).hexdigest(),expectedDiagnostic=diagnostic,symbol=symbol,transcript=text,overlapTimestampsOnly=True,separateCompilerObservations=list(foreign.values()),declaredHeavy=heavy,rssLimitKiB=rss_limit,targetMtimeTouch=touch_record,sourceMutationObserved=source_mutation,deadlineStopUTC=deadline_stop,deadlineInterrupted=deadline_interrupted)
 (OUT/(unit+'.json')).write_text(json.dumps(record,indent=2)+'\n')
 with (OUT/'ledger.jsonl').open('a') as ledger:ledger.write(json.dumps(record)+'\n')
 print(text,flush=True);print('RESULT',json.dumps({k:v for k,v in record.items() if k!='transcript'}),flush=True)
finally:
 pass  # No shared lock/window operations.
sys.exit(0 if passed else 1)
