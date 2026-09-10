#!/usr/bin/env python3
"""Append-only measured inventory/ledger and source-anchored raw evidence archive."""
import datetime,hashlib,json,pathlib,re,subprocess,tarfile
ROOT=pathlib.Path(__file__).resolve().parents[1];OUT=pathlib.Path('/tmp/dgamma-r200');ART=ROOT/'research-tests'
sha=lambda b:hashlib.sha256(b).hexdigest()
archive=ART/'O6-R200-COMPILER-EVIDENCE.tar.gz';assert not archive.exists(), 'Append-only publication; gate replacement'
records=[json.loads(s) for s in (OUT/'ledger.jsonl').read_text().splitlines()];receipts=[json.loads(s) for s in (OUT/'commit-receipts.jsonl').read_text().splitlines()]
plan=json.loads((OUT/'final-validation-plan.json').read_text());scope=json.loads((ART/'O6-R200-VALIDATION-SCOPE.json').read_text())
assert json.loads((OUT/'final-validation-result.json').read_text())['status']=='PASS'
assert len(records)==212 and all(r['passed'] for r in records)
assert len(plan)==166 and all(any(r['unit']==item['unit'] and r['passed'] and r['sourceSHA256']==item['sourceHash'] for r in records) for item in plan)
source_receipts=[r for r in receipts if r['event']=='GUARDED COMMIT'];assert len(source_receipts)==45
assert sum(r.get('kind')!='authorized-comment-only' for r in source_receipts)==44
policy_bytes=(OUT/'execution-policy.json').read_bytes();policy=json.loads(policy_bytes)
anchor=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip();now=datetime.datetime.now(datetime.timezone.utc).isoformat()
cost=json.loads((ART/'O6-R199-ROOT-CONTRACT-COSTS.json').read_text());entries=cost['entries'];assert len(entries)==266
new=scope['newPaths'];assert len(new)==8
for path in new:
    assert path not in {x['path'] for x in entries}
    entries.append(dict(path=path,module='DGamma.'+pathlib.Path(path).stem,estimatedSeconds=None,estimatedSampleRSSKiB=None,estimateBasis='New R200 target',heavyLock=False,expectedDiagnostic=None,symbol=None))
measured=0
for item in entries:
    path=item['path'];actual=sha((ROOT/path).read_bytes())
    own=[r for r in records if r['path']==path and r['passed'] and r['sourceSHA256']==actual]
    item['historicalR199Cost']=dict(estimatedSeconds=item.get('estimatedSeconds'),estimatedSampleRSSKiB=item.get('estimatedSampleRSSKiB'),estimateBasis=item.get('estimateBasis'))
    item['heavyLock']=False
    item['futureExecutionPolicy']='Cross-lane heavy lock abolished; one check per lane, own RSS guards'
    item['sourceSHA256']=actual
    item['r200Checks']=[dict(unit=r['unit'],seconds=r['seconds'],maxSampleRSSKiB=r['maxSampleRSSKiB'],rssLimitKiB=r['rssLimitKiB'],expectedDiagnostic=r['expectedDiagnostic'],startUTC=r['start'],endUTC=r['end'],executionPolicySHA256=r['executionPolicySHA256']) for r in own]
    if own:
        measured+=1;item['r200Status']='Current-source direct checked expected outcome';item['estimatedSeconds']=max(r['seconds'] for r in own);item['estimatedSampleRSSKiB']=max(r['maxSampleRSSKiB'] for r in own);item['estimateBasis']='R200 current-source direct one-second samples; not OS high-water; zero means no live sample'
    else:item['r200Status']='NOT rechecked in R200; inherited excluded stale/unclassified/legacy TTC is not fresh PASS'
    item['r200PeakMeasurementQuality']='one-second sample, NOT OS high-water' if own and item['estimatedSampleRSSKiB'] else 'NO R200 LIVE PEAK MEASUREMENT'
    item['ttcPresentAtR200Publication']=(ROOT/'build/ttc/2025081600'/pathlib.Path(item['module'].replace('.','/')+'.ttc')).exists()
assert len(entries)==274 and measured==163
inventory_paths={x['path'] for x in entries};auxiliary=[item for item in plan if item['path']!='package' and item['path'] not in inventory_paths];assert len(auxiliary)==2
cost.update(status='R200 complete measured refresh; seeded, NOT cold',preparedUTC=now,sourceFreezeHead=scope['sourceFreezeHead'],publicationAnchorCommit=anchor,inheritedR199InventoryCount=266,currentCount=274,r200MeasuredInventoryEntries=163,r200DirectSourceTargets=165,r200AuxiliaryInheritedTargetsOutsideInventory=auxiliary,r200UnvalidatedInventoryEntries=111,r200NewPaths=new,qualification='266 inherited inventory+8 new=274;163 directly checked inventory entries+2 unchanged inherited main baseline variants outside inventory=165 source targets. ALL157 inherited applicable paths+8 new+seeded package checked.111 excluded inventory paths remain NOT rechecked. Earlier r198/r199 fields remain historical. No lane2 worktree or cold certification.')
(ART/'O6-R200-ROOT-CONTRACT-COSTS.json').write_text(json.dumps(cost,indent=2)+'\n')
keys=['unit','path','command','start','end','seconds','exit','fresh','passed','interrupted','targetMutationDetected','resourceStopped','sourceSHA256','maxSampleRSSKiB','rssLimitKiB','expectedDiagnostic','symbol','unexpectedBuilding','validationContinuationSHA256','runnerSHA256','heavyLock','executionPolicySHA256','crossLaneHeavyChecksPermitted','crossLaneOverlapTimestampsUTC']
(ART/'O6-R200-COMPILER-LEDGER.json').write_text(json.dumps(dict(anchorCommit=anchor,preparedUTC=now,executionPolicy=policy,records=[{k:r[k] for k in keys} for r in records]),indent=2)+'\n')
rows=['# R200 per-module direct measurements','','One-second own-worktree samples, NOT OS high-water. Zero means no captured live sample. All212 invocations achieved their expected result; seven validation fixtures are exact expected negatives, not positive typechecks.','','| Invocation | Target | Seconds | Sample KiB | Limit KiB | Outcome |','|---|---|---:|---:|---:|---|']
for r in records:
    outcome='expected-negative PASS' if r['expectedDiagnostic'] else 'PASS'
    rows.append(f"| {r['unit']} | `{r['path']}` | {r['seconds']:.3f} | {r['maxSampleRSSKiB']} | {r['rssLimitKiB']} | {outcome} |")
(ART/'O6-R200-PER-MODULE-COSTS.md').write_text('\n'.join(rows)+'\n')
rows=['# R200 micro-unit ledger','','B24 units/24 invocations, then A20 units/20 invocations; all44 retained declarations PASS1.45 source commits include the one authorized D1 comment correction. No exhausted/reverted unit; C0/ineligible. D2 documentation/plan; D3 evidence; D4 final gate.','','| Unit | Attempt | Outcome | Source SHA256 | Guarded commit |','|---|---:|---|---|---|']
for r in records:
    if not re.fullmatch(r'[AB]\d+-\d+',r['unit']):continue
    receipt=next(x for x in source_receipts if x['invocation']==r['unit']);unit,attempt=r['unit'].rsplit('-',1)
    rows.append(f"| {unit} | {attempt} | PASS | `{r['sourceSHA256']}` | `{receipt['resultingCommitHash']}` |")
comment=next(r for r in source_receipts if r.get('kind')=='authorized-comment-only')
rows+=['',f"D1-COMMENT: fresh own-target PASS, exact authorized doc replacement only, commit `{comment['resultingCommitHash']}`; before/after SHA in `O6-R200-COMMENT-CORRECTION.json`."]
(ART/'O6-R200-MICRO-UNITS.md').write_text('\n'.join(rows)+'\n')
# Later publication/verification/gate receipts intentionally lie outside this anchor.
excluded={'archive-publication.log','archive-verification.json','archive-verification.log','post-publication-independent.json','post-publication-independent.log','post-publication-frozen.json','post-publication-frozen.log','archive-anchor.json'}
files=[p for p in sorted(OUT.rglob('*')) if p.is_file() and p.name not in excluded and '__pycache__' not in p.parts];assert all(not p.is_symlink() for p in files)
manifest={str(p.relative_to(OUT)):sha(p.read_bytes()) for p in files}
info=dict(anchorCommit=anchor,preparedUTC=now,qualification='Anchor PRECEDES publication and final-gate commits; their own/future receipts are not claimed inside this archive. Raw logs/source snapshots, immutable plan, comment authorization, all prior receipts and timestamp-only overlap evidence retained.',filesSHA256=manifest)
(OUT/'archive-anchor.json').write_text(json.dumps(info,indent=2)+'\n')
with tarfile.open(archive,'w:gz') as tar:
    for p in files+[OUT/'archive-anchor.json']:tar.add(p,arcname='dgamma-r200/'+str(p.relative_to(OUT)))
verification=dict(anchorCommit=anchor,preparedUTC=now,archiveSHA256=sha(archive.read_bytes()),archiveBytes=archive.stat().st_size,archiveFiles=len(files)+1,invocations=212,expectedPASS=212,rejections=0,sourceReceipts=45,proofSourceReceipts=44,commentReceipts=1,finalChecks=166,finalSourceTargets=165,finalExpectedNegatives=7,seededPackageBuild=True,coldBuild=False,executionPolicySHA256=sha(policy_bytes),noLockOperations=True,crossLaneHeavyChecksPermitted=True,inventoryRechecked=163,inventoryTotal=274,auxiliarySourceTargets=2,unvalidatedInventoryEntries=111,resourceStops=[r['unit'] for r in records if r['resourceStopped']],currentSourceHashes={item['path']:item['sourceHash'] for item in plan},receiptQualification=info['qualification'])
(ART/'O6-R200-EVIDENCE-VERIFICATION.json').write_text(json.dumps(verification,indent=2)+'\n');print(json.dumps({k:v for k,v in verification.items() if k!='currentSourceHashes'},indent=2))
