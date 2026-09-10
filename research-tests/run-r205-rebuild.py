#!/usr/bin/env python3
"""Serialized production or research validation driver; no repair/re-proof.
Usage: python3 -I research-tests/run-r205-rebuild.py production|research
Every native invocation has its own immutable receipt; failed deps are skipped,
not silently loaded from stale TTCs. Resource/monitor stops pause this driver.
Resume skips all completed invocations (failures need explicit repair gates).
"""
import sys,pathlib,json,subprocess,datetime
sys.dont_write_bytecode=True
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from r205_common import *
mode=sys.argv[1];assert mode in ['production','research']
policy=json.loads((ROOT/'research-tests/O6-R205-REBUILD-POLICY.json').read_text())
plan=json.loads((ROOT/'research-tests/O6-R205-VALIDATION-PLAN.json').read_text())
targets=policy['productionTargets'] if mode=='production' else plan['targets']
def records():
    p=OUT/'ledger.jsonl';return [json.loads(s) for s in p.read_text().splitlines()] if p.exists() else []
def current_status():
    status={p:'unchanged production prerequisite; seeded' for p in policy['unaffectedSeededProduction']}
    for r in records():
        if r['path']!='package':status[r['path']]='passed' if r['passed'] and r['exit']==0 else 'expected rejection' if r['passed'] else 'failed'
    return status
blocked={}
for item in targets:
    path=item['path'];unit=item.get('unit',item.get('plannedUnit'))
    previous=[r for r in records() if r['path']==path]
    if previous:
        if len(previous)==1 and previous[0]['unit']=='S1' and 'is not in the source directory' in previous[0]['transcript'] and not previous[0]['fresh']:
            unit='S1-2' # authenticated CLI-root correction, unchanged source; not a proof retry
        elif len(previous)==1 and previous[0]['unit']=='S31' and previous[0]['resourceStopped'] and path=='src/DGamma/CP4SupportSolution.idr' and 'S31-2' in policy.get('resourceOverrides',{}):
            unit='S31-2' # supervisor-authorized ONE isolated 128GiB attempt
        elif len(previous)==2 and previous[-1]['unit']=='S31-2' and previous[-1]['resourceStopped'] and path=='src/DGamma/CP4SupportSolution.idr' and 'S31-3' in policy.get('resourceOverrides',{}):
            unit='S31-3' # FINAL gated200GiB/45min/pressure-monitored attempt
        elif len(previous)==3 and previous[-1]['unit']=='S31-3' and previous[-1].get('memoryPressureStopped') and path=='src/DGamma/CP4SupportSolution.idr' and 'S31-4' in policy.get('resourceOverrides',{}):
            unit='S31-4' # NEW supervisor-owned gate: acknowledged pressure-rule miscalibration
        else:continue
    if item.get('validationMode')=='gate-historical-R11-restriction':
        blocked[path]='legacy, not re-checked (standing classification)';continue
    status=current_status()
    bad=[p for p in item['dependencies'] if status.get(p) not in ['passed','unchanged production prerequisite; seeded']]
    if bad:
        blocked[path]={'reason':'blocked by unchecked/failed import; stale TTC not consumed','dependencies':bad};continue
    if datetime.datetime.now(datetime.timezone.utc)>=datetime.datetime(2026,9,10,2,15,tzinfo=datetime.timezone.utc):
        print('CUTOFF reached; explicit unchecked state retained',flush=True);break
    if (OUT/'pause-request.json').exists():
        print('PAUSE requested between invocations',flush=True);break
    print('DRIVER',mode,unit,path,utc(),flush=True)
    with (OUT/(unit+'.launch.log')).open('w') as launch_log:
        result=subprocess.run(['python3','-I',str(ROOT/'research-tests/run-r205-check.py'),unit,path],cwd=ROOT,stdout=launch_log,stderr=subprocess.STDOUT)
    record_path=OUT/(unit+'.json')
    if not record_path.exists():
        print('RUNNER failed before receipt',unit,result.returncode,flush=True);break
    r=json.loads(record_path.read_text())
    print('DONE',unit,'PASS' if r['passed'] else 'FAIL',r['seconds'],r['maxSampleRSSKiB'],flush=True)
    write_json(OUT/(mode+'-progress.json'),dict(timestampUTC=utc(),lastInvocation=unit,status=current_status(),blocked=blocked))
    subprocess.run(['python3','-I',str(ROOT/'research-tests/run-r205-state.py')],cwd=ROOT,check=True,stdout=subprocess.DEVNULL)
    if r['resourceStopped'] or r.get('memoryPressureStopped') or r.get('wallTimeStopped') or r['targetMutationDetected'] or r['multipleOwnedCompilers'] or r['unexpectedBuilding']:
        print('GATE REQUIRED: resource/mutation/multiple/unexpected-building stop',unit,flush=True);break
write_json(OUT/(mode+'-progress.json'),dict(timestampUTC=utc(),status=current_status(),blocked=blocked,driverIdle=True))
subprocess.run(['python3','-I',str(ROOT/'research-tests/run-r205-state.py')],cwd=ROOT,check=True)
print('DRIVER IDLE',mode,utc(),flush=True)
