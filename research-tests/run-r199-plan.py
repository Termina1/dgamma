#!/usr/bin/env python3
"""Compiler-free append-only freeze of all 150 inherited main sources + changes + package."""
import datetime, hashlib, json, pathlib, re, subprocess
ROOT=pathlib.Path(__file__).resolve().parents[1];OUT=pathlib.Path('/tmp/dgamma-r199');ART=ROOT/'research-tests';START='fdf96f9a'
sha=lambda b:hashlib.sha256(b).hexdigest()
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT,text=True)
assert not (OUT/'final-validation-plan.json').exists(), 'Immutable plan; gate any replacement'
assert not git('diff','--name-only','--','src/','research/','research-tests/DGamma/','dgamma.ipkg').strip()
assert not git('diff','--cached','--name-only').strip()
assert not git('ls-files','--others','--exclude-standard','--','research/','research-tests/DGamma/','src/').strip()
old=json.loads((ART/'O6-R198-COMPILER-LEDGER.json').read_text())['records'];items={}
for r in old:
    if r['passed'] and r['path']!='package':items[r['path']]=dict(path=r['path'],expectedDiagnostic=r['expectedDiagnostic'],symbol=r['symbol'],origin='inherited R198 import-closed main target')
assert len(items)==150, '143 pre-R198 + 7 R198 sources'
excluded=[]
for path in list(items):
    if not (ROOT/path).is_file():
        excluded.append(dict(path=path,reason='absent from main tree'));del items[path]
inherited=sorted(items)
changed=[p for p in git('diff','--name-only',START,'HEAD','--','research/','research-tests/DGamma/').splitlines() if p.endswith('.idr')]
for path in changed:items[path]=dict(path=path,expectedDiagnostic=None,symbol=None,origin='R199 changed/new source')
inventory=json.loads((ART/'O6-R198-ROOT-CONTRACT-COSTS.json').read_text())['entries'];assert len(inventory)==259
invalidated={x['path'] for x in inventory}|set(changed)
module_paths={}
for parent in ['research/DGamma','research-tests/DGamma']:
    for p in (ROOT/parent).glob('*.idr'):
        m=re.search(r'^module\s+([\w.]+)',p.read_text(),re.M)
        if m:
            assert m[1] not in module_paths, 'Duplicate main module name';module_paths[m[1]]=str(p.relative_to(ROOT))
for path,item in items.items():
    assert (ROOT/path).stat().st_size>0
    text=(ROOT/path).read_text();imports=re.findall(r'^import\s+(?:public\s+)?([\w.]+)',text,re.M)
    imported={module_paths[m] for m in imports if m in module_paths}
    assert imported&invalidated<=items.keys(), ('Missing invalidated import closure',path,(imported&invalidated)-items.keys())
    # Include EVERY planned dependency, including the two inherited variants outside inventory.
    deps=sorted(imported&items.keys());seeded=sorted(imported-items.keys())
    for dep in seeded:assert (ROOT/dep).read_bytes()==subprocess.check_output(['git','show',START+':'+dep],cwd=ROOT), 'Changed out-of-plan dependency'
    item.update(sourceHash=sha((ROOT/path).read_bytes()),dependencies=deps,unchangedSeededResearchImports={d:sha((ROOT/d).read_bytes()) for d in seeded},module=re.search(r'^module\s+([\w.]+)',text,re.M)[1],heavyLock=True,rssLimitKiB=(52 if path.endswith('CP5ConfluenceLocalDiamondSpike.idr') else 48)*1024*1024)
plan=[];seen=set()
while len(seen)<len(items):
    ready=sorted(p for p,x in items.items() if p not in seen and set(x['dependencies'])<=seen)
    assert ready, 'Import cycle or missing dependency'
    for path in ready:plan.append(dict(unit='V'+str(len(plan)+1),**items[path]));seen.add(path)
plan.append(dict(unit='V'+str(len(plan)+1),path='package',sourceHash=sha((ROOT/'dgamma.ipkg').read_bytes()),expectedDiagnostic=None,symbol=None,dependencies=sorted(seen),origin='seeded production package build; NOT cold',heavyLock=True,rssLimitKiB=48*1024*1024))
data=(json.dumps(plan,indent=2)+'\n').encode();(OUT/'final-validation-plan.json').write_bytes(data);(OUT/'final-validation-plan.sha256').write_text(sha(data)+'\n');(ART/'O6-R199-FINAL-VALIDATION-PLAN.json').write_bytes(data)
report=dict(status='FROZEN; execution pending',preparedUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),sourceFreezeHead=git('rev-parse','HEAD').strip(),baseline=START,planSHA256=sha(data),inheritedSources=len(inherited),newChangedSources=len(changed),sourceTargets=len(items),checksIncludingPackage=len(plan),inheritedPaths=inherited,newPaths=changed,importClosedWithinInheritedInvalidationInventory=True,invalidationInventoryCount=259,allPlannedImportsTopologicallySorted=True,excludedInheritedApplicablePaths=excluded,seededDependencyQualification='Unchanged prerequisites outside the inherited259-source invalidation inventory/source plan are source-pinned reused seeds, not fresh-PASS claims.',qualification='ALL150 inherited R198 main sources (143 +7), except only explicitly absent paths, plus every R199 source and seeded package. Expected negatives retain exact diagnostic AND symbol. No lane2 worktree or cold build.')
(ART/'O6-R199-VALIDATION-SCOPE.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k not in ['inheritedPaths','newPaths']},indent=2))
