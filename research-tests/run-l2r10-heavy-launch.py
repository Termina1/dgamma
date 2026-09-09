#!/usr/bin/env python3
"""C3-3 declared-heavy launcher: cross-lane lock ABOLISHED; no lock/window access.
Detached Python -I launch only; never commits or writes Idris source.
Usage: python3 -I research-tests/run-l2r10-heavy-launch.py C3-3 TARGET
"""
import pathlib, subprocess, sys
ROOT=pathlib.Path('/Users/vyacheslavshebanov/Work/dgamma-lane2')
OUT=pathlib.Path('/tmp/dgamma-l2r10')
unit,target=sys.argv[1:3]
assert unit=='C3-3' and target=='research-tests/O6-L2R10-Sources/DGamma/L2R10SplitEdges.idr'
assert pathlib.Path.cwd()==ROOT
assert not (OUT/(unit+'.wrapper.log')).exists()
with (OUT/(unit+'.wrapper.log')).open('w') as log:
    child=subprocess.Popen([sys.executable,'-I',str(ROOT/'research-tests/run-l2r10-heavy-check.py'),unit,target],cwd=ROOT,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
(OUT/(unit+'.wrapper.pid')).write_text(str(child.pid)+'\n')
print('DETACHED',unit,'wrapper PID',child.pid,flush=True)
