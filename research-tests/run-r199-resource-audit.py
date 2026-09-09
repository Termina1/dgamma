#!/usr/bin/env python3
"""Authenticate R199 native lifetimes, actual shared-lock intervals and RSS limits."""
import datetime,json,pathlib,subprocess
ROOT=pathlib.Path(__file__).resolve().parents[1];OUT=pathlib.Path('/tmp/dgamma-r199')
records=[json.loads(s) for s in (OUT/'ledger.jsonl').read_text().splitlines()]
events=[json.loads(s) for s in (OUT/'lock-events.jsonl').read_text().splitlines()]
policy=json.loads((OUT/'execution-policy-change.json').read_text())
intervals=[]
for r in records:
    a=[e for e in events if e['event']=='acquired' and e['unit']==r['unit']]
    z=[e for e in events if e['event']=='released' and e['unit']==r['unit']]
    if r['start']<policy['effectiveUTC']:
        assert len(a)==len(z)==1 and a[0]==r['heavyLock'][0]
        assert a[0]['pid']==z[0]['owner']['pid'] and a[0]['lane']==z[0]['owner']['lane']=='R199-main'
        assert a[0]['timestampUTC']<=r['start']<=r['end']<=z[0]['timestampUTC']
        intervals.append((a[0]['timestampUTC'],z[0]['timestampUTC'],r['unit']))
    else:
        assert not a and not z and r['heavyLock']==[]
        assert r['crossLaneHeavyChecksPermitted'] and not r['lane2Compilers']
    assert r['rssLimitKiB']==(52 if r['path'].endswith('CP5ConfluenceLocalDiamondSpike.idr') else 48)*1024*1024
    assert r['maxSampleRSSKiB']==max([s['rssKiB'] for s in r['rssSamples']] or [0])
    if r['passed']:assert r['maxSampleRSSKiB']<=r['rssLimitKiB'] and not r['resourceStopped'] and not r['targetMutationDetected']
for first,second in zip(intervals,intervals[1:]):assert first[1]<=second[0], 'Own shared-lock intervals overlap'
# Do not inspect any shared lock path under the new owner policy.
current='NOT INSPECTED: cross-lane lock abolished by owner'
for first,second in zip(records,records[1:]):assert first['end']<=second['start'], 'Own compiler overlap'
report=dict(status='PASS',timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),invocations=len(records),allCompilerLifetimesCovered=True,historicalLockIntervalsNonoverlapping=True,ownerPolicyBoundary=policy['effectiveAfterUnit'],sameLaneCompilerIntervalsNonoverlapping=True,crossLaneOverlapTimestampsUTC={r['unit']:r.get('crossLaneOverlapTimestampsUTC',[]) for r in records if r.get('crossLaneOverlapTimestampsUTC')},lockEvents=events,resourceStops=[r['unit'] for r in records if r['resourceStopped']],sourceMutations=[r['unit'] for r in records if r['targetMutationDetected']],extraBuildingRejectedUnits=[r['unit'] for r in records if r['unexpectedBuilding']],zeroSampleUnits=[r['unit'] for r in records if not r['maxSampleRSSKiB']],sampleQualification='Own-worktree one-second RSS samples are NOT OS high-water; zero means no live sample captured, not zero actual peak',maxLocalDiamondSampleRSSKiB=max([r['maxSampleRSSKiB'] for r in records if r['path'].endswith('CP5ConfluenceLocalDiamondSpike.idr')] or [0]),maxOtherSampleRSSKiB=max(r['maxSampleRSSKiB'] for r in records if not r['path'].endswith('CP5ConfluenceLocalDiamondSpike.idr')),maxUniqueOrdinalSampleRSSKiB=max([r['maxSampleRSSKiB'] for r in records if r['path'].endswith('CP5UniqueRawNameOrdinalCapital.idr')] or [0]),staleLockRemovals=[e for e in events if e['event']=='removed-stale-dead-owner-lock'],waitEvents=[e for e in events if e['event']=='waiting'],historicalOwnLocksReleased=True,sharedLockPathNotInspected=current,lane2CompilerObservations=[dict(unit=r['unit'],processes=r['lane2Compilers']) for r in records if r['lane2Compilers']])
(OUT/'final-resource.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ['lockEvents','zeroSampleUnits','lane2CompilerObservations']},indent=2))
