#!/usr/bin/env python3
"""Publish R196 measured inventory, immutable raw ledger and anchored evidence archive."""
import datetime,hashlib,json,pathlib,subprocess,tarfile
ROOT=pathlib.Path(__file__).resolve().parents[1];OUT=pathlib.Path('/tmp/dgamma-r196')
ART=ROOT/'research-tests'
records=[json.loads(s) for s in (OUT/'ledger.jsonl').read_text().splitlines()]
plan=json.loads((ART/'O6-R196-DEPENDENT-RECHECK-CONTINUATION.json').read_text())
cost=json.loads((ART/'O6-R195-ROOT-CONTRACT-COSTS.json').read_text())
sha=lambda b:hashlib.sha256(b).hexdigest()
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
anchor=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
excluded={x['path']:x for x in plan['excludedFromRunnableInventory']}
new_consumer='research/DGamma/CP5O20RootReplayLawProducerSpike.idr'
cost['inheritedR195InventoryCount']=len(cost['entries'])
cost['entries'].append(dict(module='DGamma.CP5O20RootReplayLawProducerSpike',path=new_consumer,sourceSHA256=sha((ROOT/new_consumer).read_bytes()),estimatedSeconds=None,estimatedSampleRSSKiB=None,estimateBasis='NEW R196 consumer; no R195 measurement',heavyLock=True,checkDisposition='R196 checked producer-law consumer source',expectedDiagnostic=None,symbol=None))
cost['currentCount']=len(cost['entries'])
cost['newConsumersSinceR195']=[new_consumer]
measured=0
for item in cost['entries']:
    path=item['path']; actual=sha((ROOT/path).read_bytes())
    own=[r for r in records if r['path']==path and r['passed'] and r['sourceSHA256']==actual]
    item['historicalR195Cost']=dict(estimatedSeconds=item['estimatedSeconds'],estimatedSampleRSSKiB=item['estimatedSampleRSSKiB'],estimateBasis=item['estimateBasis'])
    item['sourceSHA256']=actual
    item['r196Checks']=[dict(unit=r['unit'],seconds=r['seconds'],maxSampleRSSKiB=r['maxSampleRSSKiB'],rssLimitKiB=r['rssLimitKiB'],expectedDiagnostic=r['expectedDiagnostic']) for r in own]
    if own:
        measured+=1;item['r196Status']='directly re-checked at current source SHA; expected outcome authenticated'
        item['estimatedSeconds']=max(r['seconds'] for r in own);item['estimatedSampleRSSKiB']=max(r['maxSampleRSSKiB'] for r in own)
        item['estimateBasis']='R196 direct current-hash one-second samples; zero=no captured live sample; not OS high-water'
    elif path in excluded:
        item['r196Status']='stale TTC, not re-checked ('+('legacy' if 'FORBIDDEN' in excluded[path]['checkDisposition'] else 'unclassified')+')'
    else:item['r196Status']='NOT re-checked; execution stopped before this target'
    item['peakMeasurementQuality']='one-second sample; not OS high-water' if (item['estimatedSampleRSSKiB'] or 0)>0 else 'NO LIVE SAMPLE OR UNMEASURED; actual peak remains unknown'
    item['historicalAllSourceMaximumSampleRSSKiB']=max([r['maxSampleRSSKiB'] for r in records if r['path']==path]+[item['historicalR195Cost']['estimatedSampleRSSKiB'] or 0])
    ttc=ROOT/'build/ttc/2025081600'/pathlib.Path(item['module'].replace('.','/')+'.ttc')
    item['ttcPresentAtPublication']=ttc.exists()
cost.update(status='R196 refreshed measured cost inventory; excluded stale TTCs are NOT validated',preparedUTC=now,sourceFreezeHead=anchor,r196MeasuredInventoryEntries=measured,unknownCostCount=sum(x['estimatedSampleRSSKiB'] is None for x in cost['entries']),qualification='Inherited244-entry conservative inventory plus1 new R196 root consumer=245.100 unclassified+11legacy not rechecked. Main B scope135 source modules plus package; W adds/rechecks the new consumer (136 current source paths overall). Current-hash direct measurements only; samples0 mean no live capture, not zero actual memory. No cold build or lane2 certification.')
cost['unknownPeakCount']=sum(not x['estimatedSampleRSSKiB'] for x in cost['entries'])
(ART/'O6-R196-ROOT-CONTRACT-COSTS.json').write_text(json.dumps(cost,indent=2)+'\n')
summary=[{k:r[k] for k in ['unit','path','start','end','seconds','exit','fresh','passed','interrupted','targetMutationDetected','resourceStopped','sourceSHA256','maxSampleRSSKiB','rssLimitKiB','expectedDiagnostic','symbol','unexpectedBuilding']} for r in records]
(ART/'O6-R196-COMPILER-LEDGER.json').write_text(json.dumps(dict(anchorCommit=anchor,preparedUTC=now,records=summary),indent=2)+'\n')
rows=['# R196 per-module direct check measurements','','One-second sampled own-worktree RSS, not OS high-water. Zero is no captured live sample. Every rejected/resource-stopped invocation remains listed.','','| Unit | Target | Seconds | Sample KiB | Limit KiB | Outcome |','|---|---|---:|---:|---:|---|']
for r in records:
    outcome='expected PASS' if r['passed'] else 'RESOURCE STOP' if r.get('resourceStopped') else 'REJECTED'
    rows.append(f"| {r['unit']} | `{r['path']}` | {r['seconds']:.3f} | {r['maxSampleRSSKiB']} | {r['rssLimitKiB']} | {outcome} |")
(ART/'O6-R196-PER-MODULE-COSTS.md').write_text('\n'.join(rows)+'\n')
receipts=[json.loads(s) for s in (OUT/'commit-receipts.jsonl').read_text().splitlines()]
rows=['# R196 micro-unit ledger','','| Unit | Attempt | Outcome | Source hash | Commit |','|---|---:|---|---|---|']
for r in records:
    if '-' not in r['unit']:continue
    receipt=next((c for c in receipts if c['event']=='GUARDED COMMIT' and c['invocation']==r['unit']),None)
    rows.append(f"| {r['unit'].rsplit('-',1)[0]} | {r['unit'].rsplit('-',1)[1]} | {'PASS' if r['passed'] else 'RESOURCE STOP' if r.get('resourceStopped') else 'REJECTED'} | `{r['sourceSHA256']}` | `{receipt['resultingCommitHash'] if receipt else 'not committed'}` |")
(ART/'O6-R196-MICRO-UNITS.md').write_text('\n'.join(rows)+'\n')
excluded_publication_files={'archive-publication.log','archive-verification.json','archive-verification.log'}
archive_info=dict(anchorCommit=anchor,preparedUTC=now,qualification='Archive anchor precedes publication commit; own/future artifact receipts are not claimed inside. Original source snapshots and logs retained, including proposal before/after and owner ruling.',files=[str(p.relative_to(OUT)) for p in OUT.rglob('*') if p.is_file() and 'pycache' not in p.parts and p.name not in excluded_publication_files])
(OUT/'archive-anchor.json').write_text(json.dumps(archive_info,indent=2)+'\n')
archive=ART/'O6-R196-COMPILER-EVIDENCE.tar.gz'
with tarfile.open(archive,'w:gz') as tar:
    for p in sorted(OUT.rglob('*')):
        if p.is_file() and 'pycache' not in p.parts and p.name not in excluded_publication_files:tar.add(p,arcname='dgamma-r196/'+str(p.relative_to(OUT)))
verification=dict(anchorCommit=anchor,archiveSHA256=sha(archive.read_bytes()),archiveBytes=archive.stat().st_size,invocations=len(records),inventoryRechecked=measured,inventoryTotal=len(cost['entries']),inheritedInventoryTotal=244,unknownCostsRemaining=cost['unknownCostCount'],unknownPeakCount=cost['unknownPeakCount'],BCompleted=sum(r['passed'] and r['unit'].startswith('B') for r in records),BTotal=133,WCompleted=sum(r['passed'] and r['unit'].startswith('W') for r in records),WTotal=127,resourceStops=[r['unit'] for r in records if r.get('resourceStopped')],currentSourceHashes={p:sha((ROOT/p).read_bytes()) for p in {r['path'] for r in records if r['path']!='package'}},receiptQualification=archive_info['qualification'])
(ART/'O6-R196-EVIDENCE-VERIFICATION.json').write_text(json.dumps(verification,indent=2)+'\n')
print(json.dumps({k:v for k,v in verification.items() if k!='currentSourceHashes'},indent=2))
