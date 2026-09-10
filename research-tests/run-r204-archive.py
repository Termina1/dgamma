#!/usr/bin/env python3
"""Append-only R204 inventory, exact ledger and pre-publication anchored archive.
maximum sampled RSS over command-matching idris2 processes (single-process compiler; not an aggregate process-tree total; not OS high-water).
"""
import datetime, hashlib, json, pathlib, re, subprocess, tarfile
ROOT=pathlib.Path(__file__).resolve().parents[1]; OUT=pathlib.Path('/tmp/dgamma-r204'); ART=ROOT/'research-tests'
sha=lambda b:hashlib.sha256(b).hexdigest()
metric='maximum sampled RSS over command-matching idris2 processes (single-process compiler; not an aggregate process-tree total; not OS high-water)'
archive=ART/'O6-R204-COMPILER-EVIDENCE.tar.gz'; assert not archive.exists(), 'Append-only archive; gate replacement'
records=[json.loads(s) for s in (OUT/'ledger.jsonl').read_text().splitlines()]; receipts=[json.loads(s) for s in (OUT/'commit-receipts.jsonl').read_text().splitlines()]
plan=json.loads((OUT/'final-validation-plan.json').read_text()); scope=json.loads((ART/'O6-R204-VALIDATION-SCOPE.json').read_text())
assert json.loads((OUT/'final-validation-result.json').read_text())['status']=='PASS'
assert json.loads((OUT/'final-independent.json').read_text())['status']=='PASS'
assert len(records)==228 and sum(r['passed'] for r in records)==222
rejected=[r['unit'] for r in records if not r['passed']]; assert rejected==['U0a-1','B4-1','A3-1','A15-1','A15-2','A15-3']
assert len(plan)==190 and all(any(r['unit']==item['unit'] and r['passed'] and r['sourceSHA256']==item['sourceHash'] for r in records) for item in plan)
source_receipts=[r for r in receipts if r['event']=='GUARDED COMMIT']; assert len(source_receipts)==30
policy_bytes=(OUT/'execution-policy.json').read_bytes(); policy=json.loads(policy_bytes)
anchor=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(); now=datetime.datetime.now(datetime.timezone.utc).isoformat()
cost=json.loads((ART/'O6-R203-ROOT-CONTRACT-COSTS.json').read_text()); entries=cost['entries']; assert len(entries)==290
new=scope['newPaths']; assert len(new)==8
for path in new:
    assert path not in {x['path'] for x in entries}
    entries.append(dict(path=path,module='DGamma.'+pathlib.Path(path).stem,estimatedSeconds=None,estimatedSampleRSSKiB=None,estimateBasis='New R204 target',heavyLock=False,expectedDiagnostic=None,symbol=None))
measured=0
for item in entries:
    path=item['path']; actual=sha((ROOT/path).read_bytes())
    own=[r for r in records if r['path']==path and r['passed'] and r['sourceSHA256']==actual]
    item['historicalR203Cost']=dict(estimatedSeconds=item.get('estimatedSeconds'),estimatedSampleRSSKiB=item.get('estimatedSampleRSSKiB'),estimateBasis=item.get('estimateBasis'))
    item['heavyLock']=False; item['futureExecutionPolicy']='No cross-lane lock; one check per lane, own RSS guards'; item['sourceSHA256']=actual
    item['r204Checks']=[dict(unit=r['unit'],seconds=r['seconds'],maxSampleRSSKiB=r['maxSampleRSSKiB'],rssLimitKiB=r['rssLimitKiB'],expectedDiagnostic=r['expectedDiagnostic'],startUTC=r['start'],endUTC=r['end'],executionPolicySHA256=r['executionPolicySHA256']) for r in own]
    if own:
        measured+=1; item['r204Status']='Current-source direct checked expected outcome'; item['estimatedSeconds']=max(r['seconds'] for r in own); item['estimatedSampleRSSKiB']=max(r['maxSampleRSSKiB'] for r in own); item['estimateBasis']='R204 '+metric+'; one-second samples; zero means no live sample'
    else:item['r204Status']='NOT rechecked in R204; inherited excluded TTC is NOT a fresh PASS'
    item['r204PeakMeasurementQuality']=metric if own and item['estimatedSampleRSSKiB'] else 'NO R204 LIVE PEAK MEASUREMENT'
    item['ttcPresentAtR204Publication']=(ROOT/'build/ttc/2025081600'/pathlib.Path(item['module'].replace('.','/')+'.ttc')).exists()
assert len(entries)==298 and measured==187
inventory_paths={x['path'] for x in entries}; auxiliary=[item for item in plan if item['path']!='package' and item['path'] not in inventory_paths]; assert len(auxiliary)==2
cost.update(status='R204 complete measured refresh; seeded, NOT cold',preparedUTC=now,sourceFreezeHead=scope['sourceFreezeHead'],publicationAnchorCommit=anchor,inheritedR203InventoryCount=290,currentCount=298,r204MeasuredInventoryEntries=187,r204DirectSourceTargets=189,r204AuxiliaryInheritedTargetsOutsideInventory=auxiliary,r204UnvalidatedInventoryEntries=111,r204NewPaths=new,r204SampleQualification=metric,qualification='290 inherited R203 inventory+8 new=298;187 checked inventory entries+2 unchanged inherited main variants outside inventory=189 source targets. ALL181 inherited applicable paths+8 new+seeded package checked.111 other inventory paths remain NOT rechecked. Older round fields remain historical, including superseded RSS phrasing corrected by R204 P2. No lane2 worktree or cold certification.')
(ART/'O6-R204-ROOT-CONTRACT-COSTS.json').write_text(json.dumps(cost,indent=2)+'\n')
keys=['unit','path','command','start','end','seconds','exit','fresh','passed','interrupted','targetMutationDetected','resourceStopped','sourceSHA256','maxSampleRSSKiB','rssLimitKiB','expectedDiagnostic','symbol','unexpectedBuilding','validationContinuationSHA256','runnerSHA256','heavyLock','executionPolicySHA256','crossLaneHeavyChecksPermitted','crossLaneOverlapTimestampsUTC']
(ART/'O6-R204-COMPILER-LEDGER.json').write_text(json.dumps(dict(anchorCommit=anchor,preparedUTC=now,executionPolicy=policy,sampleQualification=metric,records=[{k:r[k] for k in keys} for r in records]),indent=2)+'\n')
rows=['# R204 per-module direct measurements','',metric+'. One-second samples; zero means no live sample.222/228 expected outcomes, including seven final expected negatives, the genuine whitespace-superseded A3-2 PASS and authorized unchanged-source V0-CACHE. Six rejected source snapshots remain failures.','','| Invocation | Target | Seconds | Sample KiB | Limit KiB | Outcome |','|---|---|---:|---:|---:|---|']
for r in records:
    outcome='REJECTED' if not r['passed'] else 'expected-negative PASS' if r['expectedDiagnostic'] else 'PASS (superseded rstrip-only)' if r['unit']=='A3-2' else 'PASS (authorized cache validation)' if r['unit']=='V0-CACHE' else 'PASS'
    rows.append(f"| {r['unit']} | `{r['path']}` | {r['seconds']:.3f} | {r['maxSampleRSSKiB']} | {r['rssLimitKiB']} | {outcome} |")
(ART/'O6-R204-PER-MODULE-COSTS.md').write_text('\n'.join(rows)+'\n')
(OUT/'tooling').mkdir(exist_ok=True)
for p in sorted(ART.glob('*r204*.py')):(OUT/'tooling'/p.name).write_bytes(p.read_bytes())
excluded={'archive-publication.log','archive-verification.json','archive-verification.log','post-publication-independent.json','post-publication-independent.log','post-publication-frozen.json','post-publication-frozen.log','archive-anchor.json'}
files=[p for p in sorted(OUT.rglob('*')) if p.is_file() and p.name not in excluded and '__pycache__' not in p.parts]; assert all(not p.is_symlink() for p in files)
manifest={str(p.relative_to(OUT)):sha(p.read_bytes()) for p in files}
info=dict(anchorCommit=anchor,preparedUTC=now,qualification='Anchor PRECEDES publication/final-gate commits; their future receipts are not claimed inside this archive. Every raw log/source snapshot, immutable plan, prior receipt and timestamp-only overlap record is retained, including six failed snapshots, genuine superseded A3-2 PASS, A15 full-revert audit and supervisor-authorized V0-CACHE. Read-only machine checks are NOT independent human review.',filesSHA256=manifest)
(OUT/'archive-anchor.json').write_text(json.dumps(info,indent=2)+'\n')
with tarfile.open(archive,'w:gz') as tar:
    for p in files+[OUT/'archive-anchor.json']:tar.add(p,arcname='dgamma-r204/'+str(p.relative_to(OUT)))
verification=dict(anchorCommit=anchor,preparedUTC=now,archiveSHA256=sha(archive.read_bytes()),archiveBytes=archive.stat().st_size,archiveFiles=len(files)+1,invocations=228,expectedPASS=222,rejections=6,supersededPASS=['A3-2'],sourceReceipts=30,proofSourceReceipts=29,bodyOnlyStyleReceipts=1,commentReceipts=0,finalChecks=190,finalSourceTargets=189,finalExpectedNegatives=7,seededPackageBuild=True,coldBuild=False,executionPolicySHA256=sha(policy_bytes),noLockOperations=True,crossLaneHeavyChecksPermitted=True,inventoryRechecked=187,inventoryTotal=298,auxiliarySourceTargets=2,unvalidatedInventoryEntries=111,resourceStops=[r['unit'] for r in records if r['resourceStopped']],currentSourceHashes={item['path']:item['sourceHash'] for item in plan},receiptQualification=info['qualification'])
(ART/'O6-R204-EVIDENCE-VERIFICATION.json').write_text(json.dumps(verification,indent=2)+'\n'); print(json.dumps({k:v for k,v in verification.items() if k!='currentSourceHashes'},indent=2))
