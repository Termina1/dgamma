#!/usr/bin/env python3
"""Freeze the refreshed MAIN tree's full import-closed validation inventory.
No lane-only source copied. Historical negative contracts retained byte-exact.
Unclassified diagnostics are NOT accepted negative tests. Historical R11
restrictions are visible and require parent disposition before those targets.
"""
import sys,pathlib,json,re
sys.dont_write_bytecode=True
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from r205_common import *
pre=json.loads((ROOT/'research-tests/O6-R205-PRE-STATE.json').read_text())
old=json.loads((ROOT/'research-tests/O6-R204-FINAL-VALIDATION-PLAN.json').read_text())
costs=json.loads((ROOT/'research-tests/O6-R204-ROOT-CONTRACT-COSTS.json').read_text())['entries']
contracts={i['path']:i for i in costs}
contracts.update({i['path']:i for i in old})
all_items={i['path']:dict(i) for i in pre['inventory']}
modules={i['module']:p for p,i in all_items.items()}; assert len(modules)==len(all_items)
for p,i in all_items.items():
    i['sourceSHA256']=sha((ROOT/p).read_bytes())
    i['dependencies']=sorted({modules[m] for m in i['imports'] if m in modules})
    i['libraryImports']=[m for m in i['imports'] if m not in modules]
    i['rssLimitKiB']=(52 if p.endswith('/CP5ConfluenceLocalDiamondSpike.idr') else 48)*1024*1024
    c=contracts.get(p,{})
    i['expectedDiagnostic']=c.get('expectedDiagnostic');i['symbol']=c.get('symbol')
    i['historicalDisposition']=c.get('checkDisposition',c.get('origin','not previously classified'))
    if p.startswith('src/'): i['validationMode']='production-package'
    elif 'R11' in pathlib.Path(p).name: i['validationMode']='gate-historical-R11-restriction'
    elif i['expectedDiagnostic']: i['validationMode']='authenticated-expected-negative'
    elif 'Negative' in p or 'Probe' in p: i['validationMode']='diagnostic-preflight-not-assumed-pass'
    else: i['validationMode']='positive-check'
    i['protected']=p in PROTECTED_PATHS
seen=set(); ordered=[]
while len(seen)<len(all_items):
    ready=sorted(p for p,i in all_items.items() if p not in seen and set(i['dependencies'])<=seen)
    assert ready,'Import cycle/missing dependency'
    for p in ready: ordered.append(all_items[p]);seen.add(p)
research=[i for i in ordered if not i['path'].startswith('src/')]
for n,i in enumerate(research,1):i['plannedUnit']='V'+str(n)
report=dict(timestampUTC=utc(),productionCommit=git('rev-parse','HEAD').strip(),CP3Blob=git('hash-object','src/DGamma/CP3.idr').strip(),patchSHA256=PATCH_SHA,fullValidation=True,productionCount=sum(i['path'].startswith('src/') for i in ordered),researchFixtureCount=len(research),productionPackageOrder=[i['path'] for i in ordered if i['path'].startswith('src/')],allModulesTopological=ordered,targets=research,qualification='All extant MAIN Idris sources. No claim to validate absent lane sources. Unclassified expected-rejection files need diagnostic/symbol preflight; existing R11 restriction gated, not silently overridden. Blocked dependencies prevent stale-TTC acceptance.')
output=ROOT/'research-tests/O6-R205-VALIDATION-PLAN.json';assert not output.exists()
write_json(output,report)
print('full plan',report['productionCount'],'production',len(research),'research/fixture')
print('R11 gated',sum(i['validationMode']=='gate-historical-R11-restriction' for i in research))
print('diagnostic preflight',sum(i['validationMode']=='diagnostic-preflight-not-assumed-pass' for i in research))
