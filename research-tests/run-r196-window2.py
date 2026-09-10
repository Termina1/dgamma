#!/usr/bin/env python3
"""Detached second continuous R196 rebuild lock owner; no compiler or worktree writes."""
import atexit, datetime, json, os, pathlib, shutil, signal, time
OUT=pathlib.Path('/tmp/dgamma-r196'); OUT.mkdir(exist_ok=True)
lock=pathlib.Path('/tmp/dgamma-heavy.lock')
window=pathlib.Path('/tmp/dgamma-rebuild-window.json')
owner=dict(lane='R196-main',pid=os.getpid(),timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),unit='C3-through-W-package',path='/Users/vyacheslavshebanov/Work/dgamma/')
owner_text=json.dumps(owner)
acquired=False
stopping=False
def event(kind,**kwargs):
    entry=dict(event=kind,timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),**kwargs)
    with (OUT/'window2-events.jsonl').open('a') as f: f.write(json.dumps(entry)+'\n')
    print(json.dumps(entry),flush=True)
def stop(sig,frame):
    global stopping
    stopping=True
signal.signal(signal.SIGTERM,stop); signal.signal(signal.SIGINT,stop)
def release():
    if acquired and lock.is_dir() and (lock/'owner').read_text()==owner_text:
        if window.exists() and json.loads(window.read_text()).get('pid')==os.getpid(): window.unlink()
        shutil.rmtree(lock); event('released',owner=owner)
atexit.register(release)
clock=time.monotonic()
while not acquired and not stopping:
    try:
        lock.mkdir(); (lock/'owner').write_text(owner_text); acquired=True
    except FileExistsError:
        age=time.time()-lock.stat().st_mtime
        observed=(lock/'owner').read_text() if (lock/'owner').exists() else ''
        dead=False
        try:
            other_pid=int(json.loads(observed)['pid'])
            try: os.kill(other_pid,0)
            except ProcessLookupError: dead=True
        except (ValueError,KeyError,TypeError): pass
        if age>25*60 and dead:
            event('removed-stale-dead-owner-lock',age=age,owner=observed); shutil.rmtree(lock); continue
        if time.monotonic()-clock>=20*60: raise SystemExit('Heavy lock wait20min exceeded; no compiler launched')
        event('waiting',owner=observed); time.sleep(10)
assert acquired and not stopping
assert not window.exists(), 'Unexpected rebuild window: stop and gate'
window_data=dict(lane='R196-main',pid=os.getpid(),start=owner['timestampUTC'],expectedEnd='2026-09-09T07:19:35Z',note='DeletionChain helper rebuild; lane 2 light only')
window.write_text(json.dumps(window_data,indent=2)+'\n')
(OUT/'window2-owner.json').write_text(owner_text)
event('acquired',owner=owner,window=window_data)
(OUT/'window2-ready').write_text(str(os.getpid()))
while not stopping and not (OUT/'window2-stop').exists():
    assert (lock/'owner').read_text()==owner_text
    assert datetime.datetime.now(datetime.timezone.utc)<datetime.datetime(2026,9,9,7,29,35,tzinfo=datetime.timezone.utc), 'Final gate deadline reached'
    time.sleep(2)
