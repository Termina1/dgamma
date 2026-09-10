#!/usr/bin/env python3
"""Topological changed-target/dependent validation; stale TTCs never bypass failures.
Usage: LABEL ROOTPATH... . Root sources themselves must already have fresh PASS.
Every dependency is either post-seal authentic usable seed or a fresh current PASS.
Blocked entries are NOT native re-checks or passes. Never visits another worktree.
"""
import sys,pathlib,json,re,subprocess
sys.dont_write_bytecode=True
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from r207_common import *
from r207_disposition_contract import needs_dependency_refresh
label,*roots=sys.argv[1:]
assert roots
old=json.loads((ROOT/'research-tests/O6-R206-DISPOSITION.json').read_text())['modules']
base={x['path']:x for x in old}
files=[p for p in source_paths() if '/retired/' not in p]
nodes={p:dict(module=re.search(r'^module\s+([\w.]+)',(ROOT/p).read_text(),re.M)[1],imports=re.findall(r'^import\s+(?:public\s+)?([\w.]+)',(ROOT/p).read_text(),re.M)) for p in files}
byname={v['module']:v['path'] for v in old}
byname.update({v['module']:p for p,v in nodes.items()})
for p in nodes: nodes[p]['dependencies']=[byname[m] for m in nodes[p]['imports'] if m in byname]
closure=set(roots)
while True:
    more={p for p,v in nodes.items() if any(d in closure for d in v['dependencies'])}
    if more<=closure: break
    closure|=more
status={p:('seed' if base.get(p,{}).get('usableAsImport') and base[p]['sourceSHA256']==sha((ROOT/p).read_bytes()) else 'untrusted baseline') for p in nodes}
for p in base:
    if p not in nodes: status[p]='retired/missing source; TTC untrusted'
for p in closure:
    if p in nodes: status[p]='invalidated dependent'
for r in records():
    p=r['path']
    if p in nodes and r['sourceSHA256']==sha((ROOT/p).read_bytes()):
        status[p]='passed' if r['passed'] and r['exit']==0 else 'failed'
# Roots are not exempt from dependency invalidation: a fixture may have been
# checked before its imported new module's final declaration was added.
rs=records()
latest={r['path']:r for r in rs}
changed={p for p in nodes if base.get(p,{}).get('sourceSHA256')!=sha((ROOT/p).read_bytes())}
first_current={p:min([r['end'] for r in rs if r['path']==p and r['passed'] and r['exit']==0
    and r['sourceSHA256']==sha((ROOT/p).read_bytes())] or ['']) for p in nodes}
epochs={p:'' for p in base if p not in nodes}
def required_epoch(p):
    if p not in epochs:
        epochs[p]=max([required_epoch(d) for d in nodes[p]['dependencies']]+
                      [first_current[p] if p in changed else ''])
    return epochs[p]
for p in closure:
    if p in nodes and p in latest:
        r=latest[p]
        snapshot=json.loads((OUT/(r['unit']+'.sources.json')).read_text())
        hashes={d:sha((ROOT/d).read_bytes()) for d in nodes[p]['dependencies'] if d in nodes}
        if needs_dependency_refresh(r, required_epoch(p), snapshot, hashes): status[p]='invalidated dependent'
remaining=set(closure)&set(nodes);ordered=[]
while remaining:
    ready=sorted(p for p in remaining if not (set(nodes[p]['dependencies'])&remaining))
    assert ready, 'Import cycle'
    ordered+=ready;remaining-=set(ready)
manifest=[]
for index,p in enumerate(ordered):
    bad=[d for d in nodes[p]['dependencies'] if status[d] not in ['seed','passed']]
    if bad: outcome='blocked';status[p]='blocked'
    elif p in roots and status[p]=='passed': outcome='fresh root already checked'
    else:
        unit='V'+label+'-'+str(index+1)
        log=OUT/(unit+'.launch.log')
        assert not log.exists()
        print('CHECK',unit,p,utc(),flush=True)
        with log.open('w') as f:
            subprocess.run(['python3','-I',str(ROOT/'research-tests/run-r207-check.py'),unit,p],cwd=ROOT,stdout=f,stderr=subprocess.STDOUT)
        rp=OUT/(unit+'.json')
        assert rp.exists(), 'Runner failed before receipt: '+unit
        r=json.loads(rp.read_text());outcome='passed' if r['passed'] else 'failed'
        status[p]='passed' if r['passed'] and r['exit']==0 else 'failed'
        if r['resourceStopped'] or r['targetMutationDetected'] or r['multipleOwnedCompilers'] or r['unexpectedBuilding']:
            write_json(OUT/(label+'-closure-stop.json'),r)
            raise SystemExit('Cache/resource gate; no dependent is accepted')
    entry=dict(path=p,sourceSHA256=sha((ROOT/p).read_bytes()),outcome=outcome,blockedDependencies=bad,dependencies=nodes[p]['dependencies'])
    manifest.append(entry)
    write_json(OUT/(label+'-closure.json'),dict(label=label,roots=roots,startBaseline=START,entries=manifest,complete=False))
write_json(OUT/(label+'-closure.json'),dict(label=label,roots=roots,startBaseline=START,entries=manifest,complete=True))
print('COMPLETE',label,{s:sum(x['outcome']==s for x in manifest) for s in sorted({x['outcome'] for x in manifest})},utc(),flush=True)
