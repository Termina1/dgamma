#!/usr/bin/env python3
"""Detached Python -I launch only; never commits or writes Idris source.
Usage: python3 -I research-tests/run-l2r17-launch.py UNIT TARGET
"""
import pathlib, subprocess, sys, json, datetime
ROOT=pathlib.Path('/Users/vyacheslavshebanov/Work/dgamma-lane2')
OUT=pathlib.Path('/tmp/dgamma-l2r17')
unit,target=sys.argv[1:3]
assert pathlib.Path.cwd()==ROOT
assert not (OUT/(unit+'.wrapper.log')).exists()
(OUT/(unit+'.request.json')).write_text(json.dumps(dict(unit=unit,path=target,timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat()))+'\n')
with (OUT/(unit+'.wrapper.log')).open('w') as log:
    child=subprocess.Popen([sys.executable,'-I',str(ROOT/'research-tests/run-l2r17-check.py'),unit,target],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
(OUT/(unit+'.wrapper.pid')).write_text(str(child.pid)+'\n')
print('DETACHED',unit,'wrapper PID',child.pid,flush=True)
