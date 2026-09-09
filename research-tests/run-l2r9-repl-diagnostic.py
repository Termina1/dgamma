#!/usr/bin/env python3
"""Supervisor-authorized ONE A14 REPL normalization diagnostic, NOT a proof
attempt or validation. Derived from the L2R8 monitored check protocol: detached
launcher, absolute lane-owned target, sampled18GiB stop, source mutation guard.
No scratch source/TTC, target touch, compiler --check, commit or shared lock IO.
"""
import datetime,hashlib,json,os,pathlib,signal,subprocess,sys,time
ROOT=pathlib.Path('/Users/vyacheslavshebanov/Work/dgamma-lane2')
OUT=pathlib.Path('/tmp/dgamma-l2r9')
TARGET=ROOT/'research-tests/O6-L2R9-Sources/DGamma/L2R9OrdinalTrails.idr'
assert pathlib.Path.cwd()==ROOT
if len(sys.argv)==1:
 assert not (OUT/'A14-diagnostic.wrapper.log').exists()
 with (OUT/'A14-diagnostic.wrapper.log').open('w') as f:
  p=subprocess.Popen([sys.executable,'-I',str(ROOT/'research-tests/run-l2r9-repl-diagnostic.py'),'worker'],cwd=ROOT,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
 (OUT/'A14-diagnostic.wrapper.pid').write_text(str(p.pid)+'\n');print('DETACHED diagnostic',p.pid);sys.exit()
assert sys.argv[1:] == ['worker']
assert not (OUT/'A14-diagnostic.json').exists()
assert subprocess.check_output(['git','branch','--show-current'],text=True).strip()=='cp5-thm73-lane-a8a10'
def owned():
 ps=[]
 for row in subprocess.check_output(['ps','-axo','pid=,ppid=,rss=,command='],text=True).splitlines():
  c=row.strip().split(None,3)
  if len(c)==4 and pathlib.Path(c[3].split()[0]).name in {'chez','scheme','chezscheme','idris2','idris2.so'} and '/idris2_app/idris2' in c[3] and str(ROOT)+'/' in c[3]:ps.append(dict(pid=int(c[0]),rssKiB=int(c[2]),command=c[3]))
 return ps
assert not owned()
sources={p:p.read_bytes() for p in (ROOT/'research-tests/O6-L2R9-Sources/DGamma').glob('*.idr')}
command=['idris2','--source-dir',str(ROOT/'src'),'--source-dir',str(ROOT/'research'),'--source-dir',str(ROOT/'research-tests'),'--source-dir',str(TARGET.parent.parent),str(TARGET)]
inputText='releaseOrdinalScan %search %search (smallComponent True) (fst ordinalFixtureTrails)\nreleaseOrdinalScan %search %search (smallComponent True) (snd ordinalFixtureTrails)\n:q\n'
(OUT/'A14-diagnostic.input').write_text(inputText)
start=datetime.datetime.now(datetime.timezone.utc).isoformat();maximum=0;mutation=False;interrupted=False
with (OUT/'A14-diagnostic.log').open('w') as log:
 p=subprocess.Popen(command,cwd=ROOT,stdin=subprocess.PIPE,stdout=log,stderr=subprocess.STDOUT,start_new_session=True,text=True)
 p.stdin.write(inputText);p.stdin.close()
 (OUT/'A14-diagnostic.pid').write_text(str(p.pid)+'\n')
 def stop(sig,frame):
  global interrupted
  interrupted=True;os.killpg(p.pid,signal.SIGTERM)
 signal.signal(signal.SIGTERM,stop);signal.signal(signal.SIGINT,stop)
 while p.poll() is None:
  time.sleep(.25)
  mutation=not all(q.read_bytes()==b for q,b in sources.items())
  maximum=max([maximum]+[r['rssKiB'] for r in owned()])
  if (mutation or maximum>18*1024*1024) and not interrupted:stop(signal.SIGTERM,None)
record=dict(kind='SUPERVISOR AUTHORIZED REPL DIAGNOSTIC; not proof/validation',command=command,input=inputText,start=start,end=datetime.datetime.now(datetime.timezone.utc).isoformat(),exit=p.returncode,maxSampleRSSKiB=maximum,interrupted=interrupted,sourceMutationObserved=mutation,sourceHashes={str(q.relative_to(ROOT)):hashlib.sha256(b).hexdigest() for q,b in sources.items()},targetTouch=False,scratchFiles=[],heavyLockInteraction=False,transcript=(OUT/'A14-diagnostic.log').read_text())
(OUT/'A14-diagnostic.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record,indent=2))
