#!/usr/bin/env python3
"""Append-only R203 measured inventory, exact ledger and pre-publication anchored archive."""
import datetime,hashlib,json,pathlib,re,subprocess,tarfile
ROOT=pathlib.Path(__file__).resolve().parents[1];OUT=pathlib.Path('/tmp/dgamma-r203');ART=ROOT/'research-tests'
sha=lambda b:hashlib.sha256(b).hexdigest()
archive=ART/'O6-R203-COMPILER-EVIDENCE.tar.gz';assert not archive.exists(), 'Append-only archive; gate replacement'
records=[json.loads(s) for s in (OUT/'ledger.jsonl').read_text().splitlines()];receipts=[json.loads(s) for s in (OUT/'commit-receipts.jsonl').read_text().splitlines()]
plan=json.loads((OUT/'final-validation-plan.json').read_text());scope=json.loads((ART/'O6-R203-VALIDATION-SCOPE.json').read_text())
assert json.loads((OUT/'final-validation-result.json').read_text())['status']=='PASS'
assert len(records)==225 and sum(r['passed'] for r in records)==215
rejected=[r['unit'] for r in records if not r['passed']];assert len(rejected)==10
assert len(plan)==182 and all(any(r['unit']==item['unit'] and r['passed'] and r['sourceSHA256']==item['sourceHash'] for r in records) for item in plan)
source_receipts=[r for r in receipts if r['event']=='GUARDED COMMIT'];assert len(source_receipts)==32
policy_bytes=(OUT/'execution-policy.json').read_bytes();policy=json.loads(policy_bytes)
anchor=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip();now=datetime.datetime.now(datetime.timezone.utc).isoformat()
cost=json.loads((ART/'O6-R202-ROOT-CONTRACT-COSTS.json').read_text());entries=cost['entries'];assert len(entries)==285
new=scope['newPaths'];assert len(new)==5
for path in new:
    assert path not in {x['path'] for x in entries}
    entries.append(dict(path=path,module='DGamma.'+pathlib.Path(path).stem,estimatedSeconds=None,estimatedSampleRSSKiB=None,estimateBasis='New R203 target',heavyLock=False,expectedDiagnostic=None,symbol=None))
measured=0
for item in entries:
    path=item['path'];actual=sha((ROOT/path).read_bytes())
    own=[r for r in records if r['path']==path and r['passed'] and r['sourceSHA256']==actual]
    item['historicalR202Cost']=dict(estimatedSeconds=item.get('estimatedSeconds'),estimatedSampleRSSKiB=item.get('estimatedSampleRSSKiB'),estimateBasis=item.get('estimateBasis'))
    item['heavyLock']=False;item['futureExecutionPolicy']='No cross-lane lock; one check per lane, own RSS guards';item['sourceSHA256']=actual
    item['r203Checks']=[dict(unit=r['unit'],seconds=r['seconds'],maxSampleRSSKiB=r['maxSampleRSSKiB'],rssLimitKiB=r['rssLimitKiB'],expectedDiagnostic=r['expectedDiagnostic'],startUTC=r['start'],endUTC=r['end'],executionPolicySHA256=r['executionPolicySHA256']) for r in own]
    if own:
        measured+=1;item['r203Status']='Current-source direct checked expected outcome';item['estimatedSeconds']=max(r['seconds'] for r in own);item['estimatedSampleRSSKiB']=max(r['maxSampleRSSKiB'] for r in own);item['estimateBasis']='R203 current-source one-second samples; NOT OS high-water; zero means no live sample'
    else:item['r203Status']='NOT rechecked in R203; inherited excluded TTC is NOT a fresh PASS'
    item['r203PeakMeasurementQuality']='one-second sample, NOT OS high-water' if own and item['estimatedSampleRSSKiB'] else 'NO R203 LIVE PEAK MEASUREMENT'
    item['ttcPresentAtR203Publication']=(ROOT/'build/ttc/2025081600'/pathlib.Path(item['module'].replace('.','/')+'.ttc')).exists()
assert len(entries)==290 and measured==179
inventory_paths={x['path'] for x in entries};auxiliary=[item for item in plan if item['path']!='package' and item['path'] not in inventory_paths];assert len(auxiliary)==2
cost.update(status='R203 complete measured refresh; seeded, NOT cold',preparedUTC=now,sourceFreezeHead=scope['sourceFreezeHead'],publicationAnchorCommit=anchor,inheritedR202InventoryCount=285,currentCount=290,r203MeasuredInventoryEntries=179,r203DirectSourceTargets=181,r203AuxiliaryInheritedTargetsOutsideInventory=auxiliary,r203UnvalidatedInventoryEntries=111,r203NewPaths=new,qualification='285 inherited R202 inventory+5 new=290;179 checked inventory entries+2 unchanged inherited main variants outside inventory=181 source targets. ALL176 inherited applicable paths+5 new+seeded package checked.111 other inventory paths remain NOT rechecked. Older round fields remain historical. No lane2 worktree or cold certification.')
(ART/'O6-R203-ROOT-CONTRACT-COSTS.json').write_text(json.dumps(cost,indent=2)+'\n')
keys=['unit','path','command','start','end','seconds','exit','fresh','passed','interrupted','targetMutationDetected','resourceStopped','sourceSHA256','maxSampleRSSKiB','rssLimitKiB','expectedDiagnostic','symbol','unexpectedBuilding','validationContinuationSHA256','runnerSHA256','heavyLock','executionPolicySHA256','crossLaneHeavyChecksPermitted','crossLaneOverlapTimestampsUTC']
(ART/'O6-R203-COMPILER-LEDGER.json').write_text(json.dumps(dict(anchorCommit=anchor,preparedUTC=now,executionPolicy=policy,records=[{k:r[k] for k in keys} for r in records]),indent=2)+'\n')
rows=['# R203 per-module direct measurements','','One-second OWN-worktree RSS samples, NOT OS high-water. Zero means no live sample.215/225 expected outcomes, including seven final expected negatives and the genuine but superseded B16-1 PASS. Ten failed snapshots remain failures.','','| Invocation | Target | Seconds | Sample KiB | Limit KiB | Outcome |','|---|---|---:|---:|---:|---|']
for r in records:
    outcome='REJECTED' if not r['passed'] else 'expected-negative PASS' if r['expectedDiagnostic'] else 'PASS (superseded cleanup)' if r['unit']=='B16-1' else 'PASS'
    rows.append(f"| {r['unit']} | `{r['path']}` | {r['seconds']:.3f} | {r['maxSampleRSSKiB']} | {r['rssLimitKiB']} | {outcome} |")
(ART/'O6-R203-PER-MODULE-COSTS.md').write_text('\n'.join(rows)+'\n')
rows=['# R203 micro-unit ledger','','B16 units/21 invocations; A16 units/22 invocations.32 retained top-level declarations,32 guarded source commits.43 development checks=33 PASS+10 failures. B16-1 is a genuine PASS superseded by B16-2 explicit-index cleanup; both snapshots and the exact two-line transformation are authenticated. C0/ineligible. No exhausted/reverted unit and no budget extension.','','| Unit | Attempt | Outcome | Source SHA256 | Guarded commit |','|---|---:|---|---|---|']
for r in records:
    if not re.fullmatch(r'[AB]\d+-\d+',r['unit']):continue
    receipt=next((x for x in source_receipts if x['invocation']==r['unit']),None);unit,attempt=r['unit'].rsplit('-',1)
    outcome='REJECTED' if not r['passed'] else 'PASS (superseded cleanup)' if r['unit']=='B16-1' else 'PASS'
    rows.append(f"| {unit} | {attempt} | {outcome} | `{r['sourceSHA256']}` | `{receipt['resultingCommitHash'] if receipt else 'none'}` |")
rows+=['','Failure explanations and exact declaration correspondence: `O6-R203-DECLARATIONS.md`. The policy label is R203 from the first invocation; no inherited-label correction occurred. Artifact publication/final-gate receipts intentionally follow the raw archive anchor.']
(ART/'O6-R203-MICRO-UNITS.md').write_text('\n'.join(rows)+'\n')
(OUT/'tooling').mkdir(exist_ok=True)
for p in sorted(ART.glob('*r203*.py')):(OUT/'tooling'/p.name).write_bytes(p.read_bytes())
excluded={'archive-publication.log','archive-verification.json','archive-verification.log','post-publication-independent.json','post-publication-independent.log','post-publication-frozen.json','post-publication-frozen.log','archive-anchor.json'}
files=[p for p in sorted(OUT.rglob('*')) if p.is_file() and p.name not in excluded and '__pycache__' not in p.parts];assert all(not p.is_symlink() for p in files)
manifest={str(p.relative_to(OUT)):sha(p.read_bytes()) for p in files}
info=dict(anchorCommit=anchor,preparedUTC=now,qualification='Anchor PRECEDES publication/final-gate commits; their future receipts are not claimed inside this archive. Every raw log/source snapshot, immutable plan, prior receipt and timestamp-only overlap record is retained, including10 failed snapshots and the genuine superseded B16-1 PASS.',filesSHA256=manifest)
(OUT/'archive-anchor.json').write_text(json.dumps(info,indent=2)+'\n')
with tarfile.open(archive,'w:gz') as tar:
    for p in files+[OUT/'archive-anchor.json']:tar.add(p,arcname='dgamma-r203/'+str(p.relative_to(OUT)))
verification=dict(anchorCommit=anchor,preparedUTC=now,archiveSHA256=sha(archive.read_bytes()),archiveBytes=archive.stat().st_size,archiveFiles=len(files)+1,invocations=225,expectedPASS=215,rejections=10,supersededPASS=['B16-1'],sourceReceipts=32,proofSourceReceipts=32,commentReceipts=0,finalChecks=182,finalSourceTargets=181,finalExpectedNegatives=7,seededPackageBuild=True,coldBuild=False,executionPolicySHA256=sha(policy_bytes),noLockOperations=True,crossLaneHeavyChecksPermitted=True,inventoryRechecked=179,inventoryTotal=290,auxiliarySourceTargets=2,unvalidatedInventoryEntries=111,resourceStops=[r['unit'] for r in records if r['resourceStopped']],currentSourceHashes={item['path']:item['sourceHash'] for item in plan},receiptQualification=info['qualification'])
(ART/'O6-R203-EVIDENCE-VERIFICATION.json').write_text(json.dumps(verification,indent=2)+'\n');print(json.dumps({k:v for k,v in verification.items() if k!='currentSourceHashes'},indent=2))
