#!/usr/bin/env python3
"""Persist an honest resumable R205 state, including EVERY unchecked main path."""
import sys,pathlib,json,collections
sys.dont_write_bytecode=True
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from r205_common import *
plan=json.loads((ROOT/'research-tests/O6-R205-VALIDATION-PLAN.json').read_text())
policy=json.loads((ROOT/'research-tests/O6-R205-REBUILD-POLICY.json').read_text())
records=[json.loads(s) for s in (OUT/'ledger.jsonl').read_text().splitlines()] if (OUT/'ledger.jsonl').exists() else []
current_hashes={i['path']:sha((ROOT/i['path']).read_bytes()) for i in plan['allModulesTopological']}
last={r['path']:r for r in records if r['path']!='package' and r['sourceSHA256']==current_hashes.get(r['path'])}
blocked={}
for mode in ['production','research']:
    p=OUT/(mode+'-progress.json')
    if p.exists():blocked.update(json.loads(p.read_text()).get('blocked',{}))
items=[]
for item in plan['allModulesTopological']:
    path=item['path'];r=last.get(path)
    status='unchecked'
    reason=blocked.get(path)
    if path in policy['unaffectedSeededProduction']:status='unchanged production prerequisite; seeded (not freshly checked)'
    if item['validationMode']=='gate-historical-R11-restriction':status='legacy, not re-checked (standing classification)'
    if r:
        if r['passed']:status='passed' if r['exit']==0 else 'passed expected-negative contract'
        elif r['resourceStopped']:status='RESOURCE STOP — gate required'
        elif r.get('memoryPressureStopped'):status='RESOURCE STOP — memory pressure'
        elif r.get('wallTimeStopped'):status='RESOURCE STOP — wall-time limit'
        elif r['unexpectedBuilding']:status='MONITOR STOP — unexpected dependency Building'
        elif r['targetMutationDetected']:status='MONITOR STOP — source mutation'
        else:status='FAILED — lexical/semantic classification required'
        if not r['passed'] and path=='src/DGamma/CP3StatementChecks.idr' and (ROOT/'research-tests/O6-R205-STATEMENT-MIGRATION-STOP.json').exists():status='BROKEN BY UNFREEZE — production migration STOP3/3, restored old API'
    elif reason and status=='unchecked':status='unchecked — blocked dependency'
    items.append(dict(path=path,module=item['module'],sourceSHA256=sha((ROOT/path).read_bytes()),plannedSHA256=item['sourceSHA256'],status=status,reason=reason,invocation=r['unit'] if r else None,peakRSSKiB=r['maxSampleRSSKiB'] if r else None,exactErrors='\n'.join(r['transcript'].splitlines()) if r and not r['passed'] else None,protected=path in PROTECTED_PATHS))
applicable=[i for i in items if not i['status'].startswith(('unchanged production','legacy,'))]
complete=all(i['status'].startswith('passed') for i in applicable) and any(r['path']=='package' and r['passed'] and r.get('seededPackageNoBuilding') for r in records)
counts=dict(collections.Counter(i['status'] for i in items))
state=dict(timestampUTC=utc(),status='COMPLETE' if complete else 'INCOMPLETE',head=git('rev-parse','HEAD').strip(),CP3Blob=git('hash-object','src/DGamma/CP3.idr').strip(),patchSHA256=PATCH_SHA,lane2CompilerRelease='NOT RELEASED: remain idle until supervisor confirms COMPLETE' if not complete else 'COMPLETE; supervisor may release lane2/re-seed',counts=counts,checked=sum(i['invocation'] is not None for i in items),passed=sum(i['status'].startswith('passed') for i in items),lexicallyRepaired=0,broken=sum(i['invocation'] is not None and not i['status'].startswith('passed') for i in items),unchecked=sum(i['status'].startswith('unchecked') for i in items),legacyNotApplicable=11,unaffectedProductionSeeds=44,packageInvocations=[{k:r[k] for k in ['unit','passed','exit','seconds','maxSampleRSSKiB','rssLimitKiB','buildingLines','resourceStopped']} for r in records if r['path']=='package'],frozen=frozen(),modules=items,supersededCandidateInvocations=[r['unit'] for r in records if r['path']!='package' and r['sourceSHA256']!=current_hashes.get(r['path'])],qualification='TTCs emitted by stopped P1 are not evidence. Source hashes and every checked/unchecked/broken path retained. Resource or semantic breakage is not a repaired proof; no stale cache PASS claims.')
write_json(ROOT/'research-tests/O6-R205-REBUILD-STATE.json',state)
write_json(ROOT/'research-tests/O6-R205-COMPILER-LEDGER.json',dict(records=records))
print(json.dumps({k:state[k] for k in ['status','checked','passed','broken','unchecked','counts']},indent=2))
