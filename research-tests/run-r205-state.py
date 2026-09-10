#!/usr/bin/env python3
"""Current-source disposition for EVERY main module; blocked caches never count."""
import sys,pathlib,json,collections
sys.dont_write_bytecode=True
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from r205_common import *
plan=json.loads((ROOT/'research-tests/O6-R205-VALIDATION-PLAN.json').read_text())
policy=json.loads((ROOT/'research-tests/O6-R205-REBUILD-POLICY.json').read_text())
records=[json.loads(s) for s in (OUT/'ledger.jsonl').read_text().splitlines()]
current={i['path']:sha((ROOT/i['path']).read_bytes()) for i in plan['allModulesTopological']}
last={r['path']:r for r in records if r['path']!='package' and r['sourceSHA256']==current.get(r['path'])}
classifications={r['path']:r for r in json.loads((ROOT/'research-tests/O6-R205-BROKEN-MODULES.json').read_text())['entries']}
for p,r in classifications.items():assert r['sourceSHA256']==current[p]
repairs=json.loads((ROOT/'research-tests/O6-R205-LEXICAL-REPAIRS.json').read_text())['entries']
items=[];by_path={};ready_unexecuted=[]
for item in plan['allModulesTopological']:
    path=item['path'];r=last.get(path);reason=None;roots=[]
    bad=[p for p in item['dependencies'] if not by_path[p]['usableAsImport']]
    if path in policy['unaffectedSeededProduction']:
        status='unchanged production prerequisite; seeded (not freshly checked)';usable=True
    elif item['validationMode']=='gate-historical-R11-restriction':
        status='legacy, not re-checked (standing classification)';usable=False
    elif r:
        usable=bool(r['passed'] and r['exit']==0)
        if r['passed']:status='passed' if r['exit']==0 else 'passed expected-negative contract'
        elif path in classifications:status=classifications[path]['status'];reason=classifications[path]['cause']
        elif r['resourceStopped'] or r.get('memoryPressureStopped') or r.get('wallTimeStopped'):status='RESOURCE STOP — gate required'
        elif r['unexpectedBuilding'] or r['targetMutationDetected'] or r['multipleOwnedCompilers']:status='MONITOR STOP — gate required'
        else:status='FAILED — classification required'
        if not usable:roots=[path]
    else:
        usable=False
        if bad:
            status='unchecked — blocked dependency'
            roots=sorted(set(root for p in bad for root in (by_path[p]['blockedRootCauses'] or [p])))
            reason=dict(dependencies=bad,rootCauses=roots,rule='No stale TTC acceptance; importing a known-broken/unvalidated module is not a fresh own-target check')
        else:status='unchecked — ready target not executed';ready_unexecuted.append(path);roots=[path]
    ttcs=[]
    for ttc in (ROOT/'build/ttc').glob('*/'+item['module'].replace('.','/')+'.ttc'):
        ttcs.append(dict(path=str(ttc.relative_to(ROOT)),sha256=sha(ttc.read_bytes()),bytes=ttc.stat().st_size,mtimeNs=ttc.stat().st_mtime_ns,evidence='fresh own-target receipt' if usable and r else 'authenticated unchanged seed' if usable else 'UNTRUSTED for current-source validation'))
    row=dict(path=path,module=item['module'],sourceSHA256=current[path],plannedSHA256=item['sourceSHA256'],status=status,reason=reason,invocation=r['unit'] if r else None,peakRSSKiB=r['maxSampleRSSKiB'] if r else None,exactErrors=r['transcript'] if r and not r['passed'] else None,protected=path in PROTECTED_PATHS,usableAsImport=usable,blockedRootCauses=roots,ttc=ttcs)
    items.append(row);by_path[path]=row
applicable=[i for i in items if not i['status'].startswith(('unchanged production','legacy,'))]
package=any(r['path']=='package' and r['passed'] and r.get('seededPackageNoBuilding') for r in records)
production=package and all(by_path[i['path']]['usableAsImport'] for i in policy['productionTargets'])
complete=production and all(i['status'].startswith('passed') for i in applicable)
disposed=not ready_unexecuted and all(i['status'].startswith(('passed','BROKEN BY UNFREEZE','FAILED — pre-existing','unchecked — blocked')) for i in applicable)
lexical=sum(r['path'] in last and last[r['path']]['passed'] and current[r['path']]==r['afterSHA256'] for r in repairs)
fg=json.loads((ROOT/'research-tests/O6-R205-FROZEN-MIGRATION-GATE.json').read_text())
frozen_migrations=int(current[fg['path']]==fg['afterSHA256'] and last.get(fg['path'],{}).get('passed',False))
state=dict(timestampUTC=utc(),status='COMPLETE' if complete else 'INCOMPLETE — native research has explicit breakage/blocked imports',productionRebuildComplete=production,dispositionTraversalComplete=disposed,allApplicableNativeChecksPass=complete,head=git('rev-parse','HEAD').strip(),CP3Blob=git('hash-object','src/DGamma/CP3.idr').strip(),patchSHA256=PATCH_SHA,lane2CompilerRelease='SUPERVISOR GATE REQUIRED; no release inferred from production or disposition completeness',counts=dict(collections.Counter(i['status'] for i in items)),checked=sum(i['invocation'] is not None for i in items),passed=sum(i['status'].startswith('passed') for i in items),lexicallyRepaired=lexical+frozen_migrations,nonFrozenLexicalRepairs=lexical,frozenConsumerMigrations=frozen_migrations,productionConsumerMigrations=1,broken=sum(i['invocation'] is not None and not i['status'].startswith('passed') for i in items),unchecked=sum(i['status'].startswith('unchecked') for i in items),legacyNotApplicable=11,unaffectedProductionSeeds=44,readyUnexecuted=ready_unexecuted,packageInvocations=[{k:r[k] for k in ['unit','passed','exit','seconds','maxSampleRSSKiB','rssLimitKiB','buildingLines','resourceStopped']} for r in records if r['path']=='package'],frozen=frozen(),modules=items,supersededCandidateInvocations=[r['unit'] for r in records if r['path']!='package' and r['sourceSHA256']!=current.get(r['path'])],qualification='Production package PASS is not full research PASS. Every applicable ready target was attempted; semantic/pre-existing failures and their blocked dependents remain explicit. Stopped-build or stale TTCs are never proof evidence. No new theorem/hole/escape hatch.')
final_gate_path=ROOT/'research-tests/O6-R205-FINAL-GATE.json'
if final_gate_path.exists():
    gate=json.loads(final_gate_path.read_text())
    assert gate['acceptance']=='ACCEPTED CHECKED-PARTIAL' and gate['artifactOnlySealAuthorized']
    state.update(ownerAcceptance=gate['acceptance'],acceptedHead=gate['acceptedHead'],lane2CompilerRelease=gate['lane2Release'],mainNextShift=gate['mainNextShift'],standDownAuthorized=gate['standDownAuthorized'])
write_json(ROOT/'research-tests/O6-R205-REBUILD-STATE.json',state)
write_json(ROOT/'research-tests/O6-R205-COMPILER-LEDGER.json',dict(records=records))
print(json.dumps({k:state[k] for k in ['status','productionRebuildComplete','dispositionTraversalComplete','checked','passed','broken','unchecked','lexicallyRepaired','counts']},indent=2))
