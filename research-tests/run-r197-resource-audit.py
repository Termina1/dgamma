#!/usr/bin/env python3
"""Authenticate R197 native lifetimes, actual shared-lock intervals and RSS limits."""
import datetime,json,pathlib,subprocess
ROOT=pathlib.Path(__file__).resolve().parents[1];OUT=pathlib.Path('/tmp/dgamma-r197')
records=[json.loads(s) for s in (OUT/'ledger.jsonl').read_text().splitlines()]
events=[json.loads(s) for s in (OUT/'lock-events.jsonl').read_text().splitlines()]
intervals=[]
for r in records:
    a=[e for e in events if e['event']=='acquired' and e['unit']==r['unit']]
    z=[e for e in events if e['event']=='released' and e['unit']==r['unit']]
    assert len(a)==len(z)==1 and a[0]==r['heavyLock'][0]
    assert a[0]['pid']==z[0]['owner']['pid'] and a[0]['lane']==z[0]['owner']['lane']=='R197-main'
    assert a[0]['timestampUTC']<=r['start']<=r['end']<=z[0]['timestampUTC']
    intervals.append((a[0]['timestampUTC'],z[0]['timestampUTC'],r['unit']))
    assert r['rssLimitKiB']==(52 if r['path'].endswith('CP5ConfluenceLocalDiamondSpike.idr') else 48)*1024*1024
    assert r['maxSampleRSSKiB']==max([s['rssKiB'] for s in r['rssSamples']] or [0])
    if r['passed']:assert r['maxSampleRSSKiB']<=r['rssLimitKiB'] and not r['resourceStopped'] and not r['targetMutationDetected']
for first,second in zip(intervals,intervals[1:]):assert first[1]<=second[0], 'Own shared-lock intervals overlap'
owner=pathlib.Path('/tmp/dgamma-heavy.lock/owner')
current=json.loads(owner.read_text()) if owner.exists() else None
assert not current or current.get('lane')!='R197-main'
report=dict(status='PASS',timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),invocations=len(records),allCompilerLifetimesCovered=True,lockIntervalsNonoverlapping=True,lockEvents=events,resourceStops=[r['unit'] for r in records if r['resourceStopped']],sourceMutations=[r['unit'] for r in records if r['targetMutationDetected']],extraBuildingRejectedUnits=[r['unit'] for r in records if r['unexpectedBuilding']],zeroSampleUnits=[r['unit'] for r in records if not r['maxSampleRSSKiB']],sampleQualification='Own-worktree one-second RSS samples are NOT OS high-water; zero means no live sample captured, not zero actual peak',maxLocalDiamondSampleRSSKiB=max([r['maxSampleRSSKiB'] for r in records if r['path'].endswith('CP5ConfluenceLocalDiamondSpike.idr')] or [0]),maxOtherSampleRSSKiB=max(r['maxSampleRSSKiB'] for r in records if not r['path'].endswith('CP5ConfluenceLocalDiamondSpike.idr')),maxUniqueOrdinalSampleRSSKiB=max([r['maxSampleRSSKiB'] for r in records if r['path'].endswith('CP5UniqueRawNameOrdinalCapital.idr')] or [0]),staleLockRemovals=[e for e in events if e['event']=='removed-stale-dead-owner-lock'],waitEvents=[e for e in events if e['event']=='waiting'],noMainLock=True,currentForeignLock=current,lane2CompilerObservations=[dict(unit=r['unit'],processes=r['lane2Compilers']) for r in records if r['lane2Compilers']])
(OUT/'final-resource.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ['lockEvents','zeroSampleUnits','lane2CompilerObservations']},indent=2))
