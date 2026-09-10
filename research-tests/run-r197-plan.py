#!/usr/bin/env python3
"""Compiler-free, append-only freeze of the COMPLETE R197 final check plan."""
import datetime, hashlib, json, pathlib, re, subprocess
ROOT=pathlib.Path(__file__).resolve().parents[1]
OUT=pathlib.Path('/tmp/dgamma-r197'); ART=ROOT/'research-tests'
sha=lambda b:hashlib.sha256(b).hexdigest()
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT,text=True)
assert not (OUT/'final-validation-plan.json').exists(), 'Plan is immutable; gate any replacement'
assert not git('diff','--name-only','--','src/','research/','research-tests/DGamma/','dgamma.ipkg').strip()
assert not git('diff','--cached','--name-only').strip()
assert not git('ls-files','--others','--exclude-standard','--','research/','research-tests/DGamma/','src/').strip()
old=json.loads((ART/'O6-R196-COMPILER-LEDGER.json').read_text())['records']
items={}
for r in old:
    if r['passed'] and r['path']!='package':
        items[r['path']]=dict(path=r['path'],expectedDiagnostic=r['expectedDiagnostic'],symbol=r['symbol'],origin='inherited R196 applicable current source')
assert len(items)==136, 'R196135 baseline sources plus the late checked root consumer'
inherited=sorted(items)
changed=[p for p in git('diff','--name-only','e2ebe3b5','HEAD','--','research/','research-tests/DGamma/').splitlines() if p.endswith('.idr')]
assert len(changed)==7
for p in changed:items[p]=dict(path=p,expectedDiagnostic=None,symbol=None,origin='R197 changed/new source')
inventory=json.loads((ART/'O6-R196-ROOT-CONTRACT-COSTS.json').read_text())['entries']
invalidated_domain={x['path'] for x in inventory}|set(changed)
assert len(inventory)==245
module_paths={}
for parent in ['research/DGamma','research-tests/DGamma']:
    for p in (ROOT/parent).glob('*.idr'):
        m=re.search(r'^module\s+([\w.]+)',p.read_text(),re.M)
        if m:
            assert m[1] not in module_paths, 'Duplicate main module name'
            module_paths[m[1]]=str(p.relative_to(ROOT))
for p,item in items.items():
    assert (ROOT/p).is_file() and (ROOT/p).stat().st_size>0
    text=(ROOT/p).read_text()
    imports=re.findall(r'^import\s+(?:public\s+)?([\w.]+)',text,re.M)
    imported={module_paths[m] for m in imports if m in module_paths}
    deps=sorted(imported&invalidated_domain)
    assert set(deps)<=items.keys(), ('Missing inherited/new INVALIDATED import closure',p,set(deps)-items.keys())
    seeded=sorted(imported-invalidated_domain)
    for dependency in seeded:
        assert (ROOT/dependency).read_bytes()==subprocess.check_output(['git','show','e2ebe3b5:'+dependency],cwd=ROOT), 'Changed out-of-domain dependency'
    item.update(sourceHash=sha((ROOT/p).read_bytes()),dependencies=deps,unchangedSeededResearchImports={d:sha((ROOT/d).read_bytes()) for d in seeded},module=re.search(r'^module\s+([\w.]+)',text,re.M)[1],heavyLock=True,rssLimitKiB=(52 if p.endswith('CP5ConfluenceLocalDiamondSpike.idr') else 48)*1024*1024)
plan=[]; seen=set()
while len(seen)<len(items):
    ready=sorted(p for p,x in items.items() if p not in seen and set(x['dependencies'])<=seen)
    assert ready, 'Import cycle or missing dependency'
    for p in ready:
        plan.append(dict(unit='V'+str(len(plan)+1),**items[p]));seen.add(p)
plan.append(dict(unit='V'+str(len(plan)+1),path='package',sourceHash=sha((ROOT/'dgamma.ipkg').read_bytes()),expectedDiagnostic=None,symbol=None,dependencies=sorted(seen),origin='seeded production package build; NOT cold build',heavyLock=True,rssLimitKiB=48*1024*1024))
data=(json.dumps(plan,indent=2)+'\n').encode()
(OUT/'final-validation-plan.json').write_bytes(data)
(OUT/'final-validation-plan.sha256').write_text(sha(data)+'\n')
(ART/'O6-R197-FINAL-VALIDATION-PLAN.json').write_bytes(data)
report=dict(status='FROZEN; execution pending',preparedUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),sourceFreezeHead=git('rev-parse','HEAD').strip(),baseline='e2ebe3b5',planSHA256=sha(data),inheritedApplicableBaselineSources=135,inheritedLateRootConsumerSources=1,inheritedSources=len(inherited),newChangedSources=len(changed),sourceTargets=len(items),checksIncludingPackage=len(plan),inheritedPaths=inherited,newPaths=changed,importClosedWithinInheritedInvalidationInventory=True,invalidationInventoryCount=245,topologicallySorted=True,excludedInheritedApplicablePaths=[],seededDependencyQualification='Unchanged prerequisites OUTSIDE the inherited245-source invalidation inventory are source-pinned and reused from seed, not falsely called freshly rechecked.',qualification='R196135 applicable baseline sources PLUS its late root consumer =136 inherited, all present. Seven R197 sources added =143 distinct source checks +1 seeded package build. No old expected-negative target is silently converted to a positive check. No lane2 worktree/source additions or cold build claimed.')
(ART/'O6-R197-VALIDATION-SCOPE.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ['inheritedPaths','newPaths']},indent=2))
