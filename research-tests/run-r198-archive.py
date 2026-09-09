#!/usr/bin/env python3
"""Append-only measured inventory/ledger and source-anchored R198 raw evidence archive."""
import datetime,hashlib,json,pathlib,re,subprocess,tarfile
ROOT=pathlib.Path(__file__).resolve().parents[1];OUT=pathlib.Path('/tmp/dgamma-r198');ART=ROOT/'research-tests'
sha=lambda b:hashlib.sha256(b).hexdigest()
archive=ART/'O6-R198-COMPILER-EVIDENCE.tar.gz';assert not archive.exists(), 'Append-only publication; gate any replacement'
records=[json.loads(s) for s in (OUT/'ledger.jsonl').read_text().splitlines()];receipts=[json.loads(s) for s in (OUT/'commit-receipts.jsonl').read_text().splitlines()]
plan=json.loads((OUT/'final-validation-plan.json').read_text());scope=json.loads((ART/'O6-R198-VALIDATION-SCOPE.json').read_text())
assert json.loads((OUT/'final-validation-result.json').read_text())['status']=='PASS'
assert len(records)==202 and sum(r['passed'] for r in records)==195
assert all(any(r['unit']==item['unit'] and r['passed'] and r['sourceSHA256']==item['sourceHash'] for r in records) for item in plan)
source_receipts=[r for r in receipts if r['event']=='GUARDED COMMIT'];assert len(source_receipts)==41
anchor=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip();now=datetime.datetime.now(datetime.timezone.utc).isoformat()
cost=json.loads((ART/'O6-R197-ROOT-CONTRACT-COSTS.json').read_text());entries=cost['entries'];assert len(entries)==252
new=scope['newPaths'];assert len(new)==7
for path in new:
    assert path not in {x['path'] for x in entries}
    entries.append(dict(path=path,module='DGamma.'+pathlib.Path(path).stem,estimatedSeconds=None,estimatedSampleRSSKiB=None,estimateBasis='New R198 target',heavyLock=True,expectedDiagnostic=None,symbol=None))
measured=0
for item in entries:
    path=item['path'];actual=sha((ROOT/path).read_bytes())
    own=[r for r in records if r['path']==path and r['passed'] and r['sourceSHA256']==actual]
    item['historicalR197Cost']=dict(estimatedSeconds=item.get('estimatedSeconds'),estimatedSampleRSSKiB=item.get('estimatedSampleRSSKiB'),estimateBasis=item.get('estimateBasis'))
    item['sourceSHA256']=actual
    item['r198Checks']=[dict(unit=r['unit'],seconds=r['seconds'],maxSampleRSSKiB=r['maxSampleRSSKiB'],rssLimitKiB=r['rssLimitKiB'],expectedDiagnostic=r['expectedDiagnostic']) for r in own]
    if own:
        measured+=1;item['r198Status']='Current-source direct checked expected outcome';item['estimatedSeconds']=max(r['seconds'] for r in own);item['estimatedSampleRSSKiB']=max(r['maxSampleRSSKiB'] for r in own);item['estimateBasis']='R198 current-source direct one-second samples; not OS high-water; zero means no live sample'
    else:item['r198Status']='NOT re-checked in R198; inherited excluded stale/unclassified/legacy TTC, not fresh PASS'
    item['r198PeakMeasurementQuality']='one-second sample, NOT OS high-water' if own and item['estimatedSampleRSSKiB'] else 'NO R198 LIVE PEAK MEASUREMENT'
    item['ttcPresentAtR198Publication']=(ROOT/'build/ttc/2025081600'/pathlib.Path(item['module'].replace('.','/')+'.ttc')).exists()
assert len(entries)==259 and measured==148
inventory_paths={x['path'] for x in entries};auxiliary=[item for item in plan if item['path']!='package' and item['path'] not in inventory_paths];assert len(auxiliary)==2
cost.update(status='R198 complete measured refresh; seeded, NOT cold',preparedUTC=now,sourceFreezeHead=anchor,inheritedR197InventoryCount=252,currentCount=259,r198MeasuredInventoryEntries=148,r198DirectSourceTargets=150,r198AuxiliaryInheritedTargetsOutsideInventory=auxiliary,r198UnvalidatedInventoryEntries=111,r198NewPaths=new,qualification='252 inherited inventory +7 new=259;148 directly rechecked inventory entries plus2 unchanged inherited main baseline variants outside inventory=150 source targets. ALL143 inherited current applicable paths +7 new + seeded package checked.100 unclassified+11 legacy excluded inventory paths remain NOT rechecked. No lane2/cold certification. Historical r197 fields are retained as historical, not current claims.')
(ART/'O6-R198-ROOT-CONTRACT-COSTS.json').write_text(json.dumps(cost,indent=2)+'\n')
keys=['unit','path','command','start','end','seconds','exit','fresh','passed','interrupted','targetMutationDetected','resourceStopped','sourceSHA256','maxSampleRSSKiB','rssLimitKiB','expectedDiagnostic','symbol','unexpectedBuilding','validationContinuationSHA256']
(ART/'O6-R198-COMPILER-LEDGER.json').write_text(json.dumps(dict(anchorCommit=anchor,preparedUTC=now,records=[{k:r[k] for k in keys} for r in records]),indent=2)+'\n')
rows=['# R198 per-module direct measurements','','One-second own-worktree samples, NOT OS high-water. Zero means no captured live sample. All7 rejected attempts remain listed; none is PASS. A20-1 really compiled PASS but its whitespace-rejected commit was not made.','','| Invocation | Target | Seconds | Sample KiB | Limit KiB | Outcome |','|---|---|---:|---:|---:|---|']
for r in records:
    outcome='expected-negative PASS' if r['passed'] and r['expectedDiagnostic'] else 'PASS; whitespace commit guard rejected' if r['unit']=='A20-1' else 'PASS' if r['passed'] else 'RESOURCE STOP' if r['resourceStopped'] else 'REJECTED'
    rows.append(f"| {r['unit']} | `{r['path']}` | {r['seconds']:.3f} | {r['maxSampleRSSKiB']} | {r['rssLimitKiB']} | {outcome} |")
(ART/'O6-R198-PER-MODULE-COSTS.md').write_text('\n'.join(rows)+'\n')
rows=['# R198 micro-unit ledger','','A26 attempted micro-units/33 native invocations,25 retained declarations; B16 units/16 native invocations,16 retained.41 source commits. A3 STOP3/3 fully reverted; no fourth attempt. A20-1 compiler PASS was rejected by git diff --check; only EOF whitespace changed before fresh A20-2 PASS. C0; R197 D5 still exhausted/untouched. D documentation only.','','| Unit | Attempt | Outcome | Source SHA256 | Guarded commit |','|---|---:|---|---|---|']
for r in records:
    if not re.fullmatch(r'[AB]\d+-\d+',r['unit']):continue
    receipt=next((x for x in source_receipts if x['invocation']==r['unit']),None);unit,attempt=r['unit'].rsplit('-',1)
    outcome='PASS; whitespace guard refused commit' if r['unit']=='A20-1' else 'PASS' if r['passed'] else 'REJECTED; full revert' if unit=='A3' else 'REJECTED; bounded repair'
    rows.append(f"| {unit} | {attempt} | {outcome} | `{r['sourceSHA256']}` | `{receipt['resultingCommitHash'] if receipt else 'not committed'}` |")
(ART/'O6-R198-MICRO-UNITS.md').write_text('\n'.join(rows)+'\n')
# Publication and later verification/receipt files deliberately lie OUTSIDE the anchor.
excluded={'archive-publication.log','archive-verification.json','archive-verification.log','post-publication-independent.json','post-publication-independent.log','post-publication-frozen.json','post-publication-frozen.log','archive-anchor.json'}
files=[p for p in sorted(OUT.rglob('*')) if p.is_file() and p.name not in excluded and '__pycache__' not in p.parts];assert all(not p.is_symlink() for p in files)
manifest={str(p.relative_to(OUT)):sha(p.read_bytes()) for p in files}
info=dict(anchorCommit=anchor,preparedUTC=now,qualification='Anchor PRECEDES this publication and future final gate commits. Their own/future receipts are not claimed in this archive. All rejected attempts, exact rollback/whitespace receipts, raw logs/source snapshots, immutable plan and actual lock history retained.',filesSHA256=manifest)
(OUT/'archive-anchor.json').write_text(json.dumps(info,indent=2)+'\n')
with tarfile.open(archive,'w:gz') as tar:
    for p in files+[OUT/'archive-anchor.json']:tar.add(p,arcname='dgamma-r198/'+str(p.relative_to(OUT)))
verification=dict(anchorCommit=anchor,preparedUTC=now,archiveSHA256=sha(archive.read_bytes()),archiveBytes=archive.stat().st_size,archiveFiles=len(files)+1,invocations=202,expectedPASS=195,rejections=7,sourceReceipts=41,finalChecks=151,finalSourceTargets=150,finalExpectedNegatives=7,seededPackageBuild=True,coldBuild=False,inventoryRechecked=148,inventoryTotal=259,auxiliarySourceTargets=2,unvalidatedInventoryEntries=111,resourceStops=[r['unit'] for r in records if r['resourceStopped']],currentSourceHashes={item['path']:item['sourceHash'] for item in plan},receiptQualification=info['qualification'])
(ART/'O6-R198-EVIDENCE-VERIFICATION.json').write_text(json.dumps(verification,indent=2)+'\n');print(json.dumps({k:v for k,v in verification.items() if k!='currentSourceHashes'},indent=2))
