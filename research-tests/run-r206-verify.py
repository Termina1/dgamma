#!/usr/bin/env python3
"""Independent compiler-free evidence cross-check; not an external reviewer.
Checks immutable native snapshots, commit chain, frozen baseline, closure epochs,
original133 accounting and the untouched SupportSolution TTC. No compiler/locks.
"""
import sys, pathlib, json, re, collections, subprocess, io, tarfile
sys.dont_write_bytecode=True
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from r206_common import ROOT, OUT, START, sha, git, frozen, compiler_scopes, write_json, utc
from r206_evidence_contract import validate_record

report=json.loads((ROOT/'research-tests/O6-R206-DISPOSITION.json').read_text())
rs=[json.loads(x) for x in (OUT/'ledger.jsonl').read_text().splitlines()]
assert len({r['unit'] for r in rs})==len(rs)
assert json.loads((ROOT/'research-tests/O6-R206-COMPILER-LEDGER.json').read_text())['records']==rs
archive_bytes=subprocess.check_output(['git','archive',START,'src/','dgamma.ipkg'],cwd=ROOT)
with tarfile.open(fileobj=io.BytesIO(archive_bytes)) as tf:
    production={m.name:sha(tf.extractfile(m).read()) for m in tf.getmembers() if m.isfile()}
assert not git('diff',START,'--','src/','dgamma.ipkg')
assert not git('diff',START,'--','research-tests/r205_common.py')
assert frozen()==json.loads((ROOT/'research-tests/O6-R205-POST-FROZEN-BASELINE.json').read_text())['frozen']
assert report['frozen']==frozen() and report['productionByteIdentity']
assert not git('diff','--cached','--name-only').strip()
subprocess.run(['git','diff','--check'],cwd=ROOT,check=True)
own,foreign,unknown=compiler_scopes();assert not own and not unknown
for p,h in production.items():assert sha((ROOT/p).read_bytes())==h,p

budgets=collections.defaultdict(list)
for r in rs:
    unit=r['unit']
    assert json.loads((OUT/(unit+'.json')).read_text())==r
    validate_record(r,(OUT/(unit+'.source')).read_bytes(),(OUT/(unit+'.log')).read_text(),ROOT)
    for suffix,key in [('.runner.py','runnerSHA256'),('.common.py','commonSHA256'),('.sources.json','sourceManifestSHA256')]:
        assert sha((OUT/(unit+suffix)).read_bytes())==r[key],(unit,key)
    manifest=json.loads((OUT/(unit+'.sources.json')).read_text())
    target='dgamma.ipkg' if r['path']=='package' else r['path']
    assert manifest[target]==r['sourceSHA256']
    for p,h in production.items():
        if p.endswith('.idr') or p in manifest:assert manifest[p]==h,(unit,p)
    assert not r['path'].startswith('src/')
    assert 'CP4SupportSolution' not in r['path']
    assert not r['targetMutationDetected'] and not r['mutatedPaths']
    assert not r['multipleOwnedCompilers'] and not r['resourceStopped'] and not r['interrupted']
    assert not r['unexpectedBuilding']
    m=re.fullmatch(r'(U0|A|B)(\d+)-(\d+)',unit)
    if m:
        assert 1<=int(m[2])<=26 and 1<=int(m[3])<=3
        budgets[m[1]+m[2]].append(r)
    cutoff='2026-09-10T05:45:00' if unit.startswith(('V','P')) else '2026-09-10T05:30:00'
    assert r['start']<cutoff
assert all(len(v)<=3 for v in budgets.values())
assert not any(len(v)==3 and not v[-1]['passed'] for v in budgets.values()),'Exhausted seam requires explicit review'
assert not any(p for p in OUT.glob('*.pid') if not p.with_suffix('.json').exists())
packages=[r for r in rs if r['path']=='package']
assert packages and packages[-1]['passed'] and not packages[-1]['buildingLines']

mods={m['path']:m for m in report['modules']}
base={m['path']:m for m in json.loads((ROOT/'research-tests/O6-R205-REBUILD-STATE.json').read_text())['modules']}
latest={r['path']:r for r in rs}
changed=set(report['changedActiveSources']);retired=set(report['retiredSources'])
for p in changed:
    added='\n'.join(line[1:] for line in git('diff',START,'--',p).splitlines()
      if line.startswith('+') and not line.startswith('+++') and not line[1:].lstrip().startswith(('--','|||')))
    assert not re.search(r'\b(?:with|let|believe_me|assert_total|assert_smaller|partial|postulate|deletionTheoremProof)\b|\?\w+',added),p
    assert '%default total' in (ROOT/p).read_text(),p
closure=changed|retired
while True:
    add={p for p,m in mods.items() if any(d in closure for d in m.get('dependencies',[]))}
    if add<=closure:break
    closure|=add
assert closure==set(report['invalidationClosure'])
epochs={p:'' for p in retired}
def required_epoch(p):
    if p not in epochs:
        own_epochs=[r['end'] for r in rs if r['path']==p and r['passed'] and r['exit']==0 and r['sourceSHA256']==mods[p]['sourceSHA256']]
        epochs[p]=max([required_epoch(d) for d in mods[p]['dependencies']]+[min(own_epochs or ['']) if p in changed else ''])
    return epochs[p]
for p,m in mods.items():
    if p in retired:continue
    assert m['sourceSHA256']==sha((ROOT/p).read_bytes()),p
    assert m['requiredEpoch']==required_epoch(p),p
    assert (p in changed)==(base.get(p,{}).get('sourceSHA256')!=m['sourceSHA256']),p
    bad=[d for d in m['dependencies'] if not mods[d]['usableAsImport']]
    assert bad==m['blockedDependencies'],p
    if m['usableAsImport']:
        assert not bad and not m['missingProjectImports'],p
    status=m['status'];r=latest.get(p)
    if status.startswith('fresh '):
        assert r and r['sourceSHA256']==m['sourceSHA256'] and r['fresh'] and not r['unexpectedBuilding'],p
        assert r['end']>=m['requiredEpoch'],p
        assert not bad,p
        if status=='fresh PASS':
            assert r['passed'] and r['exit']==0 and m['usableAsImport'],p
            source_manifest=json.loads((OUT/(r['unit']+'.sources.json')).read_text())
            assert all(source_manifest[d]==mods[d]['sourceSHA256'] for d in m['dependencies']),p
        elif status=='fresh expected-negative PASS':assert r['passed'] and r['exit']==1 and not m['usableAsImport'],p
        else:assert status=='fresh own-target FAILED' and not r['passed'] and not m['usableAsImport'],p
    elif status.startswith('R205 authenticated seed'):
        assert p not in closure and base[p]['usableAsImport'] and base[p]['sourceSHA256']==m['sourceSHA256'],p
        assert not (r and r['sourceSHA256']==m['sourceSHA256'] and not r['passed']),p
    elif status=='blocked by untrusted/retired import':assert bad or m['missingProjectImports'],p
    if p in closure:assert status not in ['unchecked / invalidated','rejected native invocation / cache-resource gate'],p
    if p in changed:assert status=='fresh PASS',p
blocked133={p for p,b in base.items() if b['status']=='unchecked — blocked dependency'}
assert len(blocked133)==133
counts=collections.Counter(mods[p]['status'] for p in blocked133)
assert dict(counts)==report['R205Blocked133']['statusCounts']
assert sum(counts.values())==133
old='research-tests/DGamma/R172O17OpenParentRootReuseCandidate.idr'
new='research-tests/DGamma/retired/R172O17OpenParentRootReuseCandidate.idr'
assert retired=={old} and not (ROOT/old).exists()
assert (ROOT/new).read_bytes()==subprocess.check_output(['git','show',START+':'+old],cwd=ROOT)

commits=[json.loads(x) for x in (OUT/'commit-receipts.jsonl').read_text().splitlines()]
last=START
native_by_id={r['unit']:r for r in rs}
for c in commits:
    assert c['beforeCommit']==last and git('rev-parse',c['afterCommit']+'^').strip()==last
    assert c['noStagedFiles'] and c['productionUnchanged'] and c['frozenUnchanged'] and c['whitespaceGuard']
    for p,h in c['hashes'].items():
        for ref,key in [(last,'before'),(c['afterCommit'],'after')]:
            f=subprocess.run(['git','show',ref+':'+p],cwd=ROOT,capture_output=True)
            assert (sha(f.stdout) if f.returncode==0 else None)==h[key],(c['afterCommit'],p,key)
    if c['unit'] not in ['ARTIFACT','RETIRE']:
        r=native_by_id[c['unit']]
        assert r['passed'] and r['exit']==0 and c['hashes'][r['path']]['after']==r['sourceSHA256']
    last=c['afterCommit']
assert last==git('rev-parse','HEAD').strip()
support=json.loads((OUT/'support-before-package.json').read_text())
p=ROOT/support['path']
assert sha(p.read_bytes())==support['sha256'] and p.stat().st_mtime_ns==support['mtimeNS']
assert support['sha256']=='0572d487cd7d341c091a94b5fa1d6d6685eade50c2b618f38ffc19fca7dce340'

archive=ROOT/'research-tests/O6-R206-EVIDENCE.tar.gz'
manifest=json.loads((ROOT/'research-tests/O6-R206-ARCHIVE-MANIFEST.json').read_text())
assert sha(archive.read_bytes())==manifest['archiveSHA256']
with tarfile.open(archive) as tf:
    members=tf.getmembers();assert all(m.isfile() and not pathlib.PurePosixPath(m.name).is_absolute() and '..' not in pathlib.PurePosixPath(m.name).parts for m in members)
    assert len({m.name for m in members})==len(members)
    actual={m.name:sha(tf.extractfile(m).read()) for m in members}
    assert actual==manifest['members']
    assert [json.loads(x) for x in tf.extractfile('meta/ledger.jsonl').read().decode().splitlines()]==rs
    for r in rs:
        for suffix in ['.json','.log','.source','.runner.py','.common.py','.sources.json']:
            assert actual['native/'+r['unit']+suffix]==sha((OUT/(r['unit']+suffix)).read_bytes())
result=dict(timestampUTC=utc(),head=last,kind='compiler-free independent evidence cross-check; not an external reviewer',passed=True,
    nativeReceipts=len(rs),nativeAcceptedOutcomes=sum(r['passed'] for r in rs),nativeRejectedOutcomes=sum(not r['passed'] for r in rs),
    nativePackage=dict(unit=packages[-1]['unit'],passed=True,buildingLines=[],seconds=packages[-1]['seconds']),
    proofBudgetMax=3,microUnits={k:len(v) for k,v in budgets.items()},invalidationClosure=len(closure),
    invalidatedUnknown=0,original133StatusCounts=dict(counts),productionByteIdentity=True,frozenUnchanged=True,
    census=frozen()['census'],supportSolutionTTC=support,sourceCommitReceipts=len(commits),noStagedFiles=True,noOwnedCompiler=True,
    crossLaneOverlapTimestampsUTC=sorted({t for r in rs for t in r['crossLaneOverlapTimestampsUTC']}),
    archiveSHA256=manifest['archiveSHA256'],archiveMembers=len(actual),
    reviewGate=('Supervisor ACCEPTED CHECKED-PARTIAL at2d21f6ea; see O6-R206-OWNER-FINAL-GATE.md; no external reviewer claimed'
      if (ROOT/'research-tests/O6-R206-OWNER-FINAL-GATE.md').exists() and
         'R206 FINAL GATE RULING: ACCEPTED as CHECKED-PARTIAL' in (ROOT/'research-tests/O6-R206-OWNER-FINAL-GATE.md').read_text()
      else 'Supervisor spot-check still required; no external reviewer claimed'))
if '--read-only' not in sys.argv:
    write_json(ROOT/'research-tests/O6-R206-INDEPENDENT-VERIFICATION.json',result)
print(json.dumps({k:v for k,v in result.items() if k not in ['microUnits','crossLaneOverlapTimestampsUTC']},indent=2))
