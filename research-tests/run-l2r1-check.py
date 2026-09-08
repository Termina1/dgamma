#!/usr/bin/env python3
"""Adapted from run-r192-check.py: detached lane2-only seeded single check.
Uses absolute compiler arguments, never touches sources or deletes build data.
Usage: python3 -I run-l2r1-check.py UNIT PATH [DIAGNOSTIC [SYMBOL]].
"""
import datetime, hashlib, json, os, pathlib, re, signal, subprocess, sys, time
ROOT = pathlib.Path('/Users/vyacheslavshebanov/Work/dgamma-lane2')
OUT = pathlib.Path('/tmp/dgamma-l2r1')
LOCK = pathlib.Path('/tmp/dgamma-heavy.lock')
unit, path = sys.argv[1:3]
diagnostic = sys.argv[3] if len(sys.argv)>3 else None
symbol = sys.argv[4] if len(sys.argv)>4 else None
assert pathlib.Path.cwd() == ROOT
assert subprocess.check_output(['git','branch','--show-current'],cwd=ROOT,text=True).strip() == 'cp5-thm73-lane-a8a10'
assert not (OUT/(unit+'.json')).exists(), 'Append-only invocation IDs'
assert path != 'package', 'Whole package and cold rebuild forbidden in this lane'
target = ROOT/path
assert target.is_file() and target.stat().st_size > 0 and target.resolve().is_relative_to(ROOT)
assert not path.startswith('src/')
plan = json.loads((OUT/'shift.json').read_text())
cutoff = plan['validationCutoff'] if re.fullmatch(r'V\d+',unit) else plan['attemptCutoff']
assert datetime.datetime.now(datetime.timezone.utc).isoformat() < cutoff
snapshot = target.read_bytes()
def declarations(data):
 text=data.decode();return set(re.findall(r'^(?:[01] )?([A-Za-z_]\w*)\s*:',text,re.M)+re.findall(r'^(?:record|data)\s+([A-Za-z_]\w*)',text,re.M))
if re.fullmatch(r'[BC]\d+-\d+',unit):
 old=subprocess.run(['git','show','HEAD:'+path],cwd=ROOT,capture_output=True)
 assert len(declarations(snapshot)-declarations(old.stdout if old.returncode==0 else b''))==1
 previous=[json.loads(s) for s in (OUT/'ledger.jsonl').read_text().splitlines()] if (OUT/'ledger.jsonl').exists() else []
 assert sum(r['unit'].rsplit('-',1)[0]==unit.rsplit('-',1)[0] for r in previous)<3
 assert not any(r['passed'] and r['unit'].rsplit('-',1)[0]==unit.rsplit('-',1)[0] for r in previous)
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
heavy=any(k in path for k in ['CanonicalSort','R8FullPipeline','ReachedBlocks','AllFour','LocalDiamond'])
assert 'LocalDiamond' not in path,'LocalDiamond needs prior supervisor gate'
lock_events=[];locked=False
if heavy:
 wait_start=time.monotonic()
 while True:
  try:
   LOCK.mkdir();locked=True
   (LOCK/'owner').write_text(json.dumps(dict(lane='lane2',pid=os.getpid(),timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),unit=unit,path=str(target)))+'\n')
   break
  except FileExistsError:
   owner=json.loads((LOCK/'owner').read_text()) if (LOCK/'owner').exists() else {}
   age=time.time()-LOCK.stat().st_mtime
   alive=True
   try:os.kill(owner.get('pid',-1),0)
   except ProcessLookupError:alive=False
   if age>25*60 and owner.get('pid',0)>0 and not alive:
    lock_events.append(dict(event='removed stale dead-owner lock',owner=owner,ageSeconds=age))
    (LOCK/'owner').unlink(missing_ok=True);LOCK.rmdir();continue
   assert time.monotonic()-wait_start<20*60,'Heavy lock timeout; gate'
   time.sleep(5)
command=['idris2','--source-dir',str(ROOT/'src'),'--source-dir',str(ROOT/'research')]
if path.startswith('research-tests/'):command+=['--source-dir',str(ROOT/'research-tests')]
command+=['--check',str(target)]
old_mtime=target.stat().st_mtime_ns
target.touch()  # Supervisor-approved TARGET-only fresh validation exception.
touch_record=dict(path=str(target),oldMtimeNs=old_mtime,newMtimeNs=target.stat().st_mtime_ns,authority='L2R1 supervisor protocol gate; target only, dependency rebuilds acknowledged')
(OUT/(unit+'.source')).write_bytes(snapshot)
started=datetime.datetime.now(datetime.timezone.utc).isoformat();clock=time.monotonic()
maximum=0;interrupted=False;foreign={p['pid']:p for p in initial_procs if p['classification']!='lane2'}
print('START',unit,started,' '.join(command),flush=True)
try:
 with (OUT/(unit+'.log')).open('w') as log:
  process=subprocess.Popen(command,cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
  (OUT/(unit+'.pid')).write_text(str(process.pid))
  def stop(sig,frame):
   global interrupted
   interrupted=True
   # Only this exact wrapper-owned process group is ever signalled.
   os.killpg(process.pid,signal.SIGTERM)
  signal.signal(signal.SIGTERM,stop);signal.signal(signal.SIGINT,stop)
  while process.poll() is None:
   time.sleep(0.25)
   for p in compiler_processes():
    if p['classification']=='lane2':maximum=max(maximum,p['rssKiB'])
    else:foreign[p['pid']]=p
   if maximum>48*1024*1024 and not interrupted:stop(signal.SIGTERM,None)
 text=(OUT/(unit+'.log')).read_text()
 fresh=bool(re.search(r'^\d+/\d+: Building DGamma\.'+re.escape(target.stem)+r' \((?:'+re.escape(str(ROOT))+r'/)?'+re.escape(path)+r'\)$',text,re.M))
 passed=fresh and not interrupted and (process.returncode==0 and 'Error:' not in text if not diagnostic else process.returncode!=0 and diagnostic in text and bool(symbol) and symbol in text)
 record=dict(unit=unit,path=path,command=command,start=started,end=datetime.datetime.now(datetime.timezone.utc).isoformat(),seconds=time.monotonic()-clock,exit=process.returncode,fresh=fresh,passed=passed,interrupted=interrupted,maxSampleRSSKiB=maximum,sourceSHA256=hashlib.sha256(snapshot).hexdigest(),expectedDiagnostic=diagnostic,symbol=symbol,transcript=text,separateCompilerObservations=list(foreign.values()),heavyLockAcquired=heavy,heavyLockEvents=lock_events,targetMtimeTouch=touch_record)
 (OUT/(unit+'.json')).write_text(json.dumps(record,indent=2)+'\n')
 with (OUT/'ledger.jsonl').open('a') as ledger:ledger.write(json.dumps(record)+'\n')
 print(text,flush=True);print('RESULT',json.dumps({k:v for k,v in record.items() if k!='transcript'}),flush=True)
finally:
 if locked:
  assert json.loads((LOCK/'owner').read_text())['pid']==os.getpid()
  (LOCK/'owner').unlink();LOCK.rmdir()
sys.exit(0 if passed else 1)
