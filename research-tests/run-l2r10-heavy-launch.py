#!/usr/bin/env python3
"""C3-3-only detached shared-lock launcher, derived from L2R10 launch protocol.
Supervisor-authorized exception, exact manifest/source SHA; poll at most20min.
No window-file access. Cleanup requires our exact JSON identity, never another
lane's lock. The child checker alone owns/monitors its compiler process group.
"""
import datetime, hashlib, json, os, pathlib, shutil, signal, subprocess, sys, time
ROOT=pathlib.Path('/Users/vyacheslavshebanov/Work/dgamma-lane2')
OUT=pathlib.Path('/tmp/dgamma-l2r10')
AUTHORITY_SHA256='629bf4a5f404a089d47413dc147fb1f7c49b234341f29cd57590687d8e80d8e2'
assert pathlib.Path.cwd()==ROOT
raw=(ROOT/'research-tests/O6-L2R10-HEAVY-EXCEPTION.json').read_bytes()
assert hashlib.sha256(raw).hexdigest()==AUTHORITY_SHA256
a=json.loads(raw);unit=a['unit'];assert unit=='C3-3'
assert hashlib.sha256((ROOT/a['path']).read_bytes()).hexdigest()==a['sourceSHA256']
assert not (OUT/(unit+'.json')).exists(), 'One UNUSED third attempt only'
if sys.argv[1:]!=['--worker']:
 assert not sys.argv[1:]
 assert not (OUT/(unit+'.wrapper.log')).exists()
 with (OUT/(unit+'.wrapper.log')).open('w') as log:
  p=subprocess.Popen([sys.executable,'-I',str(ROOT/'research-tests/run-l2r10-heavy-launch.py'),'--worker'],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
 (OUT/(unit+'.wrapper.pid')).write_text(str(p.pid)+'\n')
 print('DETACHED HEAVY EXCEPTION',unit,'wrapper PID',p.pid,flush=True)
 raise SystemExit(0)
lock=pathlib.Path(a['lock']);assert str(lock)=='/tmp/dgamma-heavy.lock'
owner=dict(lane='lane2',pid=os.getpid(),timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),unit=unit,path=str(ROOT/a['path']),authoritySHA256=AUTHORITY_SHA256)
events=[];owned=False;child=None;start=time.monotonic();released=False
try:
 while not owned:
  try:
   lock.mkdir();owned=True
  except FileExistsError:
   if time.monotonic()-start>=a['pollSeconds']:
    raise TimeoutError('Shared lock held for20min; no compiler launched')
   time.sleep(2)
 (lock/'owner.json').write_text(json.dumps(owner,indent=2)+'\n')
 events.append(dict(event='acquired atomic mkdir',owner=owner,pollSeconds=time.monotonic()-start))
 print('LOCK ACQUIRED',json.dumps(owner),flush=True)
 def stop(signum,frame):
  if child is not None and child.poll() is None:
   child.send_signal(signal.SIGTERM)
   child.wait()
  raise KeyboardInterrupt('Heavy launcher stopped')
 signal.signal(signal.SIGTERM,stop);signal.signal(signal.SIGINT,stop)
 env=os.environ.copy();env['L2R10_HEAVY_OWNER_PID']=str(os.getpid())
 child=subprocess.Popen([sys.executable,'-I',str(ROOT/'research-tests/run-l2r10-heavy-check.py'),unit,a['path']],cwd=ROOT,env=env)
 code=child.wait()
 events.append(dict(event='checker exited',code=code))
finally:
 if owned:
  if child is not None and child.poll() is None:
   child.send_signal(signal.SIGTERM);child.wait()
  assert (lock/'owner.json').exists() and json.loads((lock/'owner.json').read_text())==owner, 'Foreign lock identity; NEVER remove'
  shutil.rmtree(lock)
  released=True
  events.append(dict(event='released own identity-checked lock',timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat()))
 (OUT/(unit+'.lock.json')).write_text(json.dumps(dict(unit=unit,owner=owner,events=events,released=released,windowInteraction=False),indent=2)+'\n')
 print('LOCK RELEASED',released,flush=True)
sys.exit(code)
