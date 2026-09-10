#!/usr/bin/env python3
"""Independent compiler-free receipt/closure/source audit; never asserts unchecked proof PASS."""
import sys,pathlib,json,re,subprocess,collections
sys.dont_write_bytecode=True
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from r205_common import *
from r205_evidence_contract import validate_record,validate_plan
plan=json.loads((ROOT/'research-tests/O6-R205-VALIDATION-PLAN.json').read_text())
policy=json.loads((ROOT/'research-tests/O6-R205-REBUILD-POLICY.json').read_text())
pre=json.loads((ROOT/'research-tests/O6-R205-PRE-STATE.json').read_text())
records=[json.loads(s) for s in (OUT/'ledger.jsonl').read_text().splitlines()]
overrides={}
gate=json.loads((ROOT/'research-tests/O6-R205-PRODUCTION-MIGRATION-GATE.json').read_text())
if sha((ROOT/gate['path']).read_bytes())==gate['afterSHA256']:overrides[gate['path']]=gate
repairs_path=ROOT/'research-tests/O6-R205-LEXICAL-REPAIRS.json'
if repairs_path.exists():
    for row in json.loads(repairs_path.read_text())['entries']:
        if sha((ROOT/row['path']).read_bytes())==row['afterSHA256']:overrides[row['path']]=row
frozen_gate=ROOT/'research-tests/O6-R205-FROZEN-MIGRATION-GATE.json'
if frozen_gate.exists():
    row=json.loads(frozen_gate.read_text())
    if sha((ROOT/row['path']).read_bytes())==row['afterSHA256']:overrides[row['path']]=row
paths=validate_plan(plan,lambda p:(ROOT/p).read_bytes(),overrides)
assert set(source_paths())==paths
assert_frozen()
assert frozen()['census']==[1,2,0,0,1]
assert sha((ROOT/'research-tests/O6-R205-CP3-TIER1-SIGNED-DIFF.patch').read_bytes())==PATCH_SHA
assert git('hash-object','src/DGamma/CP3.idr').strip()=='eeaa70aa4414648bb2a1173d58244267997d16d7'
production_delta=set(git('diff','--name-only',START,'--','src/','dgamma.ipkg').splitlines())
assert production_delta=={'src/DGamma/CP3.idr','src/DGamma/CP3StatementChecks.idr'}
assert git('show',START+':dgamma.ipkg')==(ROOT/'dgamma.ipkg').read_text()
seen_units=set();previous_end='';accepted={p:'seed' for p in policy['unaffectedSeededProduction']};native_counts=collections.Counter();missing_snapshots=[]
for r in records:
    assert r['unit'] not in seen_units;seen_units.add(r['unit'])
    assert not previous_end or r['start']>=previous_end,'Native invocations overlapped'
    previous_end=r['end']
    receipt=json.loads((OUT/(r['unit']+'.json')).read_text());assert receipt==r
    source=(OUT/(r['unit']+'.source')).read_bytes();log=(OUT/(r['unit']+'.log')).read_text()
    validate_record(r,source,log,ROOT)
    for key,suffix in [('runnerSHA256','.runner.py'),('commonSHA256','.common.py'),('pressureSamplerSHA256','.pressure.py'),('policySHA256','.policy.json'),('sourceManifestSHA256','.sources.json')]:
        snapshot=OUT/(r['unit']+suffix)
        if key in r:
            if snapshot.exists():assert sha(snapshot.read_bytes())==r[key],(r['unit'],key)
            else:missing_snapshots.append(r['unit']+suffix)
    assert r['CP3Blob']=='eeaa70aa4414648bb2a1173d58244267997d16d7'
    assert not r['targetMutationDetected'] and not r['multipleOwnedCompilers']
    assert not r['crossLaneOverlapTimestampsUTC'],'Lane2 was required idle'
    if r['path']!='package':
        item=next(i for i in plan['allModulesTopological'] if i['path']==r['path'])
        assert all(accepted.get(p) in ['pass','seed'] for p in item['dependencies']),('Unvalidated dependency',r['unit'])
        expected=item.get('expectedDiagnostic');symbol=item.get('symbol')
        snap=OUT/(r['unit']+'.negative-preflight.json')
        if not expected and snap.exists():
            negative=json.loads(snap.read_text())['contracts'].get(r['path'])
            if negative:
                assert negative['sourceSHA256']==r['sourceSHA256'];expected=negative['expectedDiagnostic'];symbol=negative['symbol']
        assert (r['expectedDiagnostic'],r['symbol'])==(expected,symbol),(r['unit'],'diagnostic contract changed')
        assert not (item.get('validationMode')=='gate-historical-R11-restriction')
        accepted[r['path']]='pass' if r['passed'] and r['exit']==0 else 'expected-negative' if r['passed'] else 'failed'
    elif r.get('seededPackageNoBuilding'):
        assert all(accepted.get(p['path'])=='pass' for p in policy['productionTargets'])
    native_counts['pass' if r['passed'] else 'failed/stopped']+=1
current={p:sha((ROOT/p).read_bytes()) for p in paths}
latest={r['path']:r for r in records if r['path'] in current and r['sourceSHA256']==current[r['path']]}
assert all(latest[p['path']]['passed'] and latest[p['path']]['exit']==0 for p in policy['productionTargets'])
p2=next(r for r in records if r['unit']=='P2');assert p2['passed'] and not p2['buildingLines']
state=json.loads((ROOT/'research-tests/O6-R205-REBUILD-STATE.json').read_text())
assert {r['path'] for r in state['modules']}==paths
assert state['productionRebuildComplete'] and state['dispositionTraversalComplete']
assert not state['readyUnexecuted']
for row in state['modules']:
    assert row['sourceSHA256']==current[row['path']]
    for ttc in row['ttc']:assert sha((ROOT/ttc['path']).read_bytes())==ttc['sha256']
    if row['status'].startswith('unchecked'):
        assert row['blockedRootCauses'] and not row['usableAsImport']
    if row['status'].startswith('passed'):
        assert latest[row['path']]['passed']
    if row['status']=='legacy, not re-checked (standing classification)':assert row['path'] not in latest
assert len([r for r in state['modules'] if r['status']=='legacy, not re-checked (standing classification)'])==11
assert not git('diff','--cached','--name-only').strip()
report=dict(timestampUTC=utc(),status='VERIFIED evidence and explicit dispositions; not a claim that broken/unchecked research typechecks',modules=len(paths),productionFreshPasses=len(policy['productionTargets']),productionAuthenticatedSeeds=len(policy['unaffectedSeededProduction']),nativeInvocations=len(records),nativeCounts=dict(native_counts),census=frozen()['census'],packageInvocation='P2',packageNoBuilding=True,sourceOverrides=sorted(overrides),missingHistoricalAuxiliarySnapshots=missing_snapshots,protected=frozen(),sourceManifestSHA256=sha(json.dumps(current,sort_keys=True).encode()),noStagedFiles=True)
write_json(ROOT/'research-tests/O6-R205-INDEPENDENT-VERIFICATION.json',report)
print(json.dumps({k:v for k,v in report.items() if k!='protected'},indent=2))
