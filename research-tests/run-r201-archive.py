#!/usr/bin/env python3
"""R200-derived append-only measured inventory/ledger and anchored raw archive."""
import datetime,hashlib,json,pathlib,re,subprocess,tarfile
ROOT=pathlib.Path(__file__).resolve().parents[1];OUT=pathlib.Path('/tmp/dgamma-r201');ART=ROOT/'research-tests'
sha=lambda b:hashlib.sha256(b).hexdigest()
archive=ART/'O6-R201-COMPILER-EVIDENCE.tar.gz';assert not archive.exists(), 'Append-only publication; gate replacement'
records=[json.loads(s) for s in (OUT/'ledger.jsonl').read_text().splitlines()];receipts=[json.loads(s) for s in (OUT/'commit-receipts.jsonl').read_text().splitlines()]
plan=json.loads((OUT/'final-validation-plan.json').read_text());scope=json.loads((ART/'O6-R201-VALIDATION-SCOPE.json').read_text())
assert json.loads((OUT/'final-validation-result.json').read_text())['status']=='PASS'
assert len(records)==220 and sum(r['passed'] for r in records)==218
assert [r['unit'] for r in records if not r['passed']]==['A5-1','A19-1']
assert len(plan)==172 and all(any(r['unit']==item['unit'] and r['passed'] and r['sourceSHA256']==item['sourceHash'] for r in records) for item in plan)
source_receipts=[r for r in receipts if r['event']=='GUARDED COMMIT'];assert len(source_receipts)==45
policy_bytes=(OUT/'execution-policy.json').read_bytes();policy=json.loads(policy_bytes)
anchor=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip();now=datetime.datetime.now(datetime.timezone.utc).isoformat()
cost=json.loads((ART/'O6-R200-ROOT-CONTRACT-COSTS.json').read_text());entries=cost['entries'];assert len(entries)==274
new=scope['newPaths'];assert len(new)==6
for path in new:
    assert path not in {x['path'] for x in entries}
    entries.append(dict(path=path,module='DGamma.'+pathlib.Path(path).stem,estimatedSeconds=None,estimatedSampleRSSKiB=None,estimateBasis='New R201 target',heavyLock=False,expectedDiagnostic=None,symbol=None))
measured=0
for item in entries:
    path=item['path'];actual=sha((ROOT/path).read_bytes())
    own=[r for r in records if r['path']==path and r['passed'] and r['sourceSHA256']==actual]
    item['historicalR200Cost']=dict(estimatedSeconds=item.get('estimatedSeconds'),estimatedSampleRSSKiB=item.get('estimatedSampleRSSKiB'),estimateBasis=item.get('estimateBasis'))
    item['heavyLock']=False;item['futureExecutionPolicy']='Cross-lane heavy lock abolished; one check per lane, own RSS guards';item['sourceSHA256']=actual
    item['r201Checks']=[dict(unit=r['unit'],seconds=r['seconds'],maxSampleRSSKiB=r['maxSampleRSSKiB'],rssLimitKiB=r['rssLimitKiB'],expectedDiagnostic=r['expectedDiagnostic'],startUTC=r['start'],endUTC=r['end'],executionPolicySHA256=r['executionPolicySHA256']) for r in own]
    if own:
        measured+=1;item['r201Status']='Current-source direct checked expected outcome';item['estimatedSeconds']=max(r['seconds'] for r in own);item['estimatedSampleRSSKiB']=max(r['maxSampleRSSKiB'] for r in own);item['estimateBasis']='R201 current-source direct one-second samples; not OS high-water; zero means no live sample'
    else:item['r201Status']='NOT rechecked in R201; inherited excluded stale/unclassified/legacy TTC is not fresh PASS'
    item['r201PeakMeasurementQuality']='one-second sample, NOT OS high-water' if own and item['estimatedSampleRSSKiB'] else 'NO R201 LIVE PEAK MEASUREMENT'
    item['ttcPresentAtR201Publication']=(ROOT/'build/ttc/2025081600'/pathlib.Path(item['module'].replace('.','/')+'.ttc')).exists()
assert len(entries)==280 and measured==169
inventory_paths={x['path'] for x in entries};auxiliary=[item for item in plan if item['path']!='package' and item['path'] not in inventory_paths];assert len(auxiliary)==2
cost.update(status='R201 complete measured refresh; seeded, NOT cold',preparedUTC=now,sourceFreezeHead=scope['sourceFreezeHead'],publicationAnchorCommit=anchor,inheritedR200InventoryCount=274,currentCount=280,r201MeasuredInventoryEntries=169,r201DirectSourceTargets=171,r201AuxiliaryInheritedTargetsOutsideInventory=auxiliary,r201UnvalidatedInventoryEntries=111,r201NewPaths=new,qualification='274 inherited inventory+6 new=280;169 directly checked inventory entries+2 unchanged inherited main baseline variants outside inventory=171 source targets. ALL165 inherited applicable paths+6 new+seeded package checked.111 excluded inventory paths remain NOT rechecked. Earlier round fields remain historical. No lane2 worktree or cold certification.')
(ART/'O6-R201-ROOT-CONTRACT-COSTS.json').write_text(json.dumps(cost,indent=2)+'\n')
keys=['unit','path','command','start','end','seconds','exit','fresh','passed','interrupted','targetMutationDetected','resourceStopped','sourceSHA256','maxSampleRSSKiB','rssLimitKiB','expectedDiagnostic','symbol','unexpectedBuilding','validationContinuationSHA256','runnerSHA256','heavyLock','executionPolicySHA256','crossLaneHeavyChecksPermitted','crossLaneOverlapTimestampsUTC']
(ART/'O6-R201-COMPILER-LEDGER.json').write_text(json.dumps(dict(anchorCommit=anchor,preparedUTC=now,executionPolicy=policy,records=[{k:r[k] for k in keys} for r in records]),indent=2)+'\n')
rows=['# R201 per-module direct measurements','','One-second own-worktree samples, NOT OS high-water. Zero means no captured live sample.218/220 expected outcomes; A5-1 and A19-1 remain rejected snapshots. Seven final fixtures are exact expected negatives, not positive typechecks.','','| Invocation | Target | Seconds | Sample KiB | Limit KiB | Outcome |','|---|---|---:|---:|---:|---|']
for r in records:
    outcome='REJECTED' if not r['passed'] else 'expected-negative PASS' if r['expectedDiagnostic'] else 'PASS'
    rows.append(f"| {r['unit']} | `{r['path']}` | {r['seconds']:.3f} | {r['maxSampleRSSKiB']} | {r['rssLimitKiB']} | {outcome} |")
(ART/'O6-R201-PER-MODULE-COSTS.md').write_text('\n'.join(rows)+'\n')
rows=['# R201 micro-unit ledger','','B26 micro-units/26 invocations, A19 micro-units/21 invocations.45 retained declarations and immediate guarded source commits. A5-1 is a signature text-generation error; A19-1 is the wrong append-order fixture expectation, NOT a producer defect. Both pass on attempt2. No exhausted/reverted unit; C0/ineligible. Owner clarified caps count micro-units and authorized the exact A19 correction. A20 not started; freeze after A19 explicitly permitted.','','| Unit | Attempt | Outcome | Source SHA256 | Guarded commit |','|---|---:|---|---|---|']
for r in records:
    if not re.fullmatch(r'[AB]\d+-\d+',r['unit']):continue
    receipt=next((x for x in source_receipts if x['invocation']==r['unit']),None);unit,attempt=r['unit'].rsplit('-',1)
    rows.append(f"| {unit} | {attempt} | {'PASS' if r['passed'] else 'REJECTED'} | `{r['sourceSHA256']}` | `{receipt['resultingCommitHash'] if receipt else 'none'}` |")
rows+=['','A19 authorization and byte-exact list-only correction: `O6-R201-A19-FIXTURE-RULING.json`. Every source receipt is inside the raw archive; artifact publication and final-gate receipts deliberately follow its anchor.']
(ART/'O6-R201-MICRO-UNITS.md').write_text('\n'.join(rows)+'\n')
excluded={'archive-publication.log','archive-verification.json','archive-verification.log','post-publication-independent.json','post-publication-independent.log','post-publication-frozen.json','post-publication-frozen.log','archive-anchor.json'}
files=[p for p in sorted(OUT.rglob('*')) if p.is_file() and p.name not in excluded and '__pycache__' not in p.parts];assert all(not p.is_symlink() for p in files)
manifest={str(p.relative_to(OUT)):sha(p.read_bytes()) for p in files}
info=dict(anchorCommit=anchor,preparedUTC=now,qualification='Anchor PRECEDES publication/final-gate commits; their future receipts are not claimed inside the archive. All raw logs/source snapshots, immutable plan, A19 authorization/correction, prior receipts and timestamp-only overlap evidence retained, including two rejected development snapshots.',filesSHA256=manifest)
(OUT/'archive-anchor.json').write_text(json.dumps(info,indent=2)+'\n')
with tarfile.open(archive,'w:gz') as tar:
    for p in files+[OUT/'archive-anchor.json']:tar.add(p,arcname='dgamma-r201/'+str(p.relative_to(OUT)))
verification=dict(anchorCommit=anchor,preparedUTC=now,archiveSHA256=sha(archive.read_bytes()),archiveBytes=archive.stat().st_size,archiveFiles=len(files)+1,invocations=220,expectedPASS=218,rejections=2,sourceReceipts=45,proofSourceReceipts=45,commentReceipts=0,finalChecks=172,finalSourceTargets=171,finalExpectedNegatives=7,seededPackageBuild=True,coldBuild=False,executionPolicySHA256=sha(policy_bytes),noLockOperations=True,crossLaneHeavyChecksPermitted=True,inventoryRechecked=169,inventoryTotal=280,auxiliarySourceTargets=2,unvalidatedInventoryEntries=111,resourceStops=[r['unit'] for r in records if r['resourceStopped']],currentSourceHashes={item['path']:item['sourceHash'] for item in plan},receiptQualification=info['qualification'])
(ART/'O6-R201-EVIDENCE-VERIFICATION.json').write_text(json.dumps(verification,indent=2)+'\n');print(json.dumps({k:v for k,v in verification.items() if k!='currentSourceHashes'},indent=2))
