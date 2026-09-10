#!/usr/bin/env python3
"""Per-module post-unfreeze dispositions; blocked != checked. Compiler-free."""
import sys,pathlib,json,re,collections
sys.dont_write_bytecode=True
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from r207_common import *
from r207_disposition_contract import classify_module
old=json.loads((ROOT/'research-tests/O6-R206-DISPOSITION.json').read_text())['modules']
base={m['path']:m for m in old}
current=source_paths()
active=[p for p in current if '/retired/' not in p]
nodes={p:dict(module=re.search(r'^module\s+([\w.]+)',(ROOT/p).read_text(),re.M)[1],imports=re.findall(r'^import\s+(?:public\s+)?([\w.]+)',(ROOT/p).read_text(),re.M),sourceSHA256=sha((ROOT/p).read_bytes())) for p in active}
byname={m['module']:m['path'] for m in old}
byname.update({v['module']:p for p,v in nodes.items()})
for p in nodes:
    nodes[p]['dependencies']=[byname[m] for m in nodes[p]['imports'] if m in byname]
    nodes[p]['missingProjectImports']=[m for m in nodes[p]['imports'] if m.startswith('DGamma.') and m not in byname]
changed={p for p,v in nodes.items() if base.get(p,{}).get('sourceSHA256')!=v['sourceSHA256']}
retired={p for p in base if p not in nodes}
closure=changed|retired
while True:
    more={p for p,v in nodes.items() if any(d in closure for d in v['dependencies'])}
    if more<=closure: break
    closure|=more
rs=records()
latest={r['path']:r for r in rs}
first_current={p:min([r['end'] for r in rs if r['path']==p and r['passed'] and r['exit']==0 and r['sourceSHA256']==v['sourceSHA256']] or ['']) for p,v in nodes.items()}
remaining=set(nodes);order=[]
while remaining:
    ready=sorted(p for p in remaining if not (set(nodes[p]['dependencies'])&remaining))
    assert ready,'Import cycle'
    order+=ready;remaining-=set(ready)
result={p:dict(path=p,module=base[p]['module'],status='retired by A8/A12 (owner-signed unfreeze)',usableAsImport=False,requiredEpoch='',sourceSHA256=base[p]['sourceSHA256'],retiredTo='research-tests/DGamma/retired/'+pathlib.Path(p).name,blockedRootCauses=[p]) for p in retired}
for p in order:
    v=nodes[p];r=latest.get(p)
    exact=bool(r and r['sourceSHA256']==v['sourceSHA256'])
    dependencies=v['dependencies']
    bad=[d for d in dependencies if not result[d]['usableAsImport']]
    epoch=max([result[d]['requiredEpoch'] for d in dependencies]+([first_current[p]] if p in changed else ['']))
    checked=bool(exact and r['fresh'] and not r['unexpectedBuilding'])
    status,usable=classify_module(exact=exact,record=r,epoch=epoch,
      blocked=bool(bad or v['missingProjectImports']),in_closure=p in closure,
      baseline_status=base.get(p,{}).get('status',''),
      seed_authenticated=bool(base.get(p,{}).get('usableAsImport') and base[p]['sourceSHA256']==v['sourceSHA256']))
    roots=sorted({root for d in bad for root in result[d]['blockedRootCauses']})
    if not usable and not roots: roots=[p]
    result[p]=dict(path=p,module=v['module'],sourceSHA256=v['sourceSHA256'],status=status,usableAsImport=usable,requiredEpoch=epoch,dependencies=dependencies,blockedDependencies=bad,blockedRootCauses=roots,missingProjectImports=v['missingProjectImports'],invalidationClosure=p in closure,nativeInvoked=bool(exact),freshOwnDiagnostic=checked,invocation=r['unit'] if exact else None,exactErrors=r['transcript'] if checked and not r['passed'] else None)
blocked205={m['path'] for m in old if m['status']=='blocked by untrusted/retired import'}
assert len(blocked205)==117
counts=collections.Counter(result[p]['status'] for p in blocked205)
checked205=[p for p in blocked205 if result[p].get('freshOwnDiagnostic')]
report=dict(timestampUTC=utc(),startBaseline=START,productionByteIdentity=not git('diff',START,'--','src/','dgamma.ipkg'),frozen=frozen(),changedActiveSources=sorted(changed),retiredSources=sorted(retired),invalidationClosure=sorted(closure),R206Blocked117=dict(total=len(blocked205),nativeOwnRechecked=len(checked205),freshPassed=sum(result[p]['status']=='fresh PASS' for p in blocked205),freshExpectedNegativePassed=sum(result[p]['status']=='fresh expected-negative PASS' for p in blocked205),freshFailed=sum(result[p]['status']=='fresh own-target FAILED' for p in blocked205),stillBlocked=sum(result[p]['status']=='blocked by untrusted/retired import' for p in blocked205),statusCounts=dict(counts),entries=[result[p] for p in sorted(blocked205)]),allModuleStatusCounts=dict(collections.Counter(x['status'] for x in result.values())),modules=[result[p] for p in sorted(result)],qualification='Fresh own diagnostics, inherited authentic seeds and blocked dispositions are distinct. No stale TTC supplies a missing proof.')
write_json(ROOT/'research-tests/O6-R207-DISPOSITION.json',report)
write_json(ROOT/'research-tests/O6-R207-COMPILER-LEDGER.json',dict(timestampUTC=utc(),records=rs))
receipts=OUT/'commit-receipts.jsonl'
write_json(ROOT/'research-tests/O6-R207-COMMIT-RECEIPTS.json',[json.loads(x) for x in receipts.read_text().splitlines()] if receipts.exists() else [])
print(json.dumps({k:v for k,v in report.items() if k not in ['modules','frozen','R206Blocked117','invalidationClosure']},indent=2))
print('R206 blocked117', {k:v for k,v in report['R206Blocked117'].items() if k!='entries'})
