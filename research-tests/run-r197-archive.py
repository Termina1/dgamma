#!/usr/bin/env python3
"""Publish measured R197 inventory, full invocation ledger and source-anchored archive."""
import datetime,hashlib,json,pathlib,subprocess,tarfile
ROOT=pathlib.Path(__file__).resolve().parents[1];OUT=pathlib.Path('/tmp/dgamma-r197');ART=ROOT/'research-tests'
sha=lambda b:hashlib.sha256(b).hexdigest()
archive=ART/'O6-R197-COMPILER-EVIDENCE.tar.gz'
assert not archive.exists(), 'Append-only archive publication; gate any replacement'
records=[json.loads(s) for s in (OUT/'ledger.jsonl').read_text().splitlines()]
receipts=[json.loads(s) for s in (OUT/'commit-receipts.jsonl').read_text().splitlines()]
plan=json.loads((OUT/'final-validation-plan.json').read_text())
assert json.loads((OUT/'final-validation-result.json').read_text())['status']=='PASS'
assert len(records)==189 and sum(r['passed'] for r in records)==178
assert all(any(r['unit']==item['unit'] and r['passed'] and r['sourceSHA256']==item['sourceHash'] for r in records) for item in plan)
assert len([r for r in receipts if r['event']=='GUARDED COMMIT'])==33
anchor=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
cost=json.loads((ART/'O6-R196-ROOT-CONTRACT-COSTS.json').read_text())
entries=cost['entries'];assert len(entries)==245
new=json.loads((ART/'O6-R197-VALIDATION-SCOPE.json').read_text())['newPaths']
for path in new:entries.append(dict(path=path,module='DGamma.'+pathlib.Path(path).stem,estimatedSeconds=None,estimatedSampleRSSKiB=None,estimateBasis='New R197 target',heavyLock=True,expectedDiagnostic=None,symbol=None))
measured=0
for item in entries:
    path=item['path'];actual=sha((ROOT/path).read_bytes())
    own=[r for r in records if r['path']==path and r['passed'] and r['sourceSHA256']==actual]
    item['historicalR196Cost']=dict(estimatedSeconds=item.get('estimatedSeconds'),estimatedSampleRSSKiB=item.get('estimatedSampleRSSKiB'),estimateBasis=item.get('estimateBasis'))
    item['sourceSHA256']=actual
    item['r197Checks']=[dict(unit=r['unit'],seconds=r['seconds'],maxSampleRSSKiB=r['maxSampleRSSKiB'],rssLimitKiB=r['rssLimitKiB'],expectedDiagnostic=r['expectedDiagnostic']) for r in own]
    if own:
        measured+=1;item['r197Status']='Current-source direct checked expected outcome'
        item['estimatedSeconds']=max(r['seconds'] for r in own);item['estimatedSampleRSSKiB']=max(r['maxSampleRSSKiB'] for r in own)
        item['estimateBasis']='R197 current-source direct one-second samples; not OS high-water; zero means no live sample'
    else:item['r197Status']='NOT re-checked in R197; inherited excluded stale/unclassified/legacy TTC, not fresh PASS'
    item['r197PeakMeasurementQuality']='one-second sample, NOT OS high-water' if own and item['estimatedSampleRSSKiB'] else 'NO R197 LIVE PEAK MEASUREMENT'
    ttc=ROOT/'build/ttc/2025081600'/pathlib.Path(item['module'].replace('.','/')+'.ttc')
    item['ttcPresentAtR197Publication']=ttc.exists()
assert len(entries)==252 and measured==141
inventory_paths={x['path'] for x in entries}
auxiliary=[item for item in plan if item['path']!='package' and item['path'] not in inventory_paths]
assert len(auxiliary)==2
cost.update(status='R197 complete measured refresh; seeded, not cold',preparedUTC=now,sourceFreezeHead=anchor,inheritedR196InventoryCount=245,currentCount=252,r197MeasuredInventoryEntries=141,r197DirectSourceTargets=143,r197AuxiliaryInheritedTargetsOutsideInventory=auxiliary,r197UnvalidatedInventoryEntries=111,r197NewPaths=new,qualification='245 inherited inventory +7 new=252;141 directly rechecked inventory entries plus2 unchanged inherited main baseline variants outside that inventory=143 source targets. All136 inherited current applicable paths and7 new paths checked.100 unclassified+11 legacy excluded inventory paths remain NOT rechecked. No lane2 or cold-build certification.')
(ART/'O6-R197-ROOT-CONTRACT-COSTS.json').write_text(json.dumps(cost,indent=2)+'\n')
keys=['unit','path','command','start','end','seconds','exit','fresh','passed','interrupted','targetMutationDetected','resourceStopped','sourceSHA256','maxSampleRSSKiB','rssLimitKiB','expectedDiagnostic','symbol','unexpectedBuilding','validationContinuationSHA256']
(ART/'O6-R197-COMPILER-LEDGER.json').write_text(json.dumps(dict(anchorCommit=anchor,preparedUTC=now,records=[{k:r[k] for k in keys} for r in records]),indent=2)+'\n')
rows=['# R197 per-module direct measurements','','One-second own-worktree samples, NOT OS high-water. Zero means no captured live sample. All eleven rejected attempts remain listed; none is PASS.','','| Invocation | Target | Seconds | Sample KiB | Limit KiB | Outcome |','|---|---|---:|---:|---:|---|']
for r in records:
    outcome='expected-negative PASS' if r['passed'] and r['expectedDiagnostic'] else 'PASS' if r['passed'] else 'RESOURCE STOP' if r['resourceStopped'] else 'REJECTED'
    rows.append(f"| {r['unit']} | `{r['path']}` | {r['seconds']:.3f} | {r['maxSampleRSSKiB']} | {r['rssLimitKiB']} | {outcome} |")
(ART/'O6-R197-PER-MODULE-COSTS.md').write_text('\n'.join(rows)+'\n')
rows=['# R197 micro-unit ledger','','One new declaration per proof invocation;33 retained commits. A26 retained; D7 of8 attempted retained. D5 exhausted3/3 and fully reverted. D3/D4 and D5/D6 reorder gates and D5 final signature amendment are explicit in the audit.','','| Unit | Attempt | Outcome | Source SHA256 | Guarded commit |','|---|---:|---|---|---|']
for r in records:
    if not r['unit'].startswith(('A','D')):continue
    receipt=next((x for x in receipts if x['event']=='GUARDED COMMIT' and x['invocation']==r['unit']),None)
    unit,attempt=r['unit'].rsplit('-',1)
    rows.append(f"| {unit} | {attempt} | {'PASS' if r['passed'] else 'REJECTED; full revert' if unit=='D5' else 'REJECTED; repaired within cap'} | `{r['sourceSHA256']}` | `{receipt['resultingCommitHash'] if receipt else 'not committed'}` |")
(ART/'O6-R197-MICRO-UNITS.md').write_text('\n'.join(rows)+'\n')
# No self-referential archive: publication/verification outputs and future
# artifact receipts are deliberately outside this anchor, never backdated.
excluded={'archive-publication.log','archive-verification.json','archive-verification.log','post-publication-independent.json','post-publication-independent.log','post-publication-frozen.json','post-publication-frozen.log','archive-anchor.json'}
files=[p for p in sorted(OUT.rglob('*')) if p.is_file() and p.name not in excluded and '__pycache__' not in p.parts]
assert all(not p.is_symlink() for p in files)
manifest={str(p.relative_to(OUT)):sha(p.read_bytes()) for p in files}
info=dict(anchorCommit=anchor,preparedUTC=now,qualification='Anchor PRECEDES this publication and future gate commits. Their own/future receipts are not claimed in the archive. Rejected attempts, exact rollback receipts, raw logs/source snapshots, plan and lock history retained.',filesSHA256=manifest)
(OUT/'archive-anchor.json').write_text(json.dumps(info,indent=2)+'\n')
with tarfile.open(archive,'w:gz') as tar:
    for p in files+[OUT/'archive-anchor.json']:tar.add(p,arcname='dgamma-r197/'+str(p.relative_to(OUT)))
verification=dict(anchorCommit=anchor,preparedUTC=now,archiveSHA256=sha(archive.read_bytes()),archiveBytes=archive.stat().st_size,archiveFiles=len(files)+1,invocations=len(records),expectedPASS=178,rejections=11,sourceReceipts=33,finalChecks=144,finalSourceTargets=143,finalExpectedNegatives=7,seededPackageBuild=True,coldBuild=False,inventoryRechecked=141,inventoryTotal=252,auxiliarySourceTargets=2,unvalidatedInventoryEntries=111,resourceStops=[r['unit'] for r in records if r['resourceStopped']],currentSourceHashes={item['path']:item['sourceHash'] for item in plan},receiptQualification=info['qualification'])
(ART/'O6-R197-EVIDENCE-VERIFICATION.json').write_text(json.dumps(verification,indent=2)+'\n')
print(json.dumps({k:v for k,v in verification.items() if k!='currentSourceHashes'},indent=2))
