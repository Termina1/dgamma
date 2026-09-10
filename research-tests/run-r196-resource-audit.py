#!/usr/bin/env python3
"""Authenticate every R196 compiler lifetime against its recorded shared-lock interval."""
import datetime,json,pathlib,subprocess
ROOT=pathlib.Path(__file__).resolve().parents[1];OUT=pathlib.Path('/tmp/dgamma-r196')
records=[json.loads(s) for s in (OUT/'ledger.jsonl').read_text().splitlines()]
windows={};window_events=[]
for name in ['window-events.jsonl','window2-events.jsonl']:
    events=[json.loads(s) for s in (OUT/name).read_text().splitlines()]
    acquired=[e for e in events if e['event']=='acquired'];released=[e for e in events if e['event']=='released']
    assert len(acquired)==len(released)==1
    assert acquired[0]['owner']==released[0]['owner']
    windows[acquired[0]['owner']['pid']]=(acquired[0]['timestampUTC'],released[0]['timestampUTC'])
    window_events+=events
consumer=[json.loads(s) for s in (OUT/'consumer-lock-events.jsonl').read_text().splitlines()]
for r in records:
    lock=r['heavyLock'][0]
    if lock['event']=='continuous-window-owned':
        start,end=windows[lock['pid']]
    else:
        entries=[e for e in consumer if e.get('owner',{}).get('unit')==r['unit']]
        acquired=[e for e in entries if e['event']=='acquired'];released=[e for e in entries if e['event']=='released']
        assert len(acquired)==len(released)==1
        assert acquired[0]['owner']==released[0]['owner']
        start,end=acquired[0]['timestampUTC'],released[0]['timestampUTC']
    assert start<=r['start']<=r['end']<=end, r['unit']
    assert r['rssLimitKiB']==(52 if r['path'].endswith('CP5ConfluenceLocalDiamondSpike.idr') else 48)*1024*1024
    assert r['maxSampleRSSKiB']<=r['rssLimitKiB'] and not r['resourceStopped'] and not r['targetMutationDetected']
    assert r['maxSampleRSSKiB']==max([s['rssKiB'] for s in r['rssSamples']] or [0])
lock=pathlib.Path('/tmp/dgamma-heavy.lock')
current=json.loads((lock/'owner').read_text()) if (lock/'owner').exists() else None
assert not current or current.get('lane')!='R196-main'
window=pathlib.Path('/tmp/dgamma-rebuild-window.json')
assert not window.exists() or json.loads(window.read_text()).get('lane')!='R196-main'
report=dict(status='PASS',timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),invocations=len(records),allCompilerLifetimesCovered=True,windowEvents=window_events,consumerLockEvents=consumer,resourceStops=[],sourceMutations=[],extraBuildingRejectedUnits=[r['unit'] for r in records if r['unexpectedBuilding']],zeroSampleUnits=[r['unit'] for r in records if not r['maxSampleRSSKiB']],sampleQualification='Own-worktree one-second RSS samples are not OS high-water; zero means no live sample captured',maxLocalDiamondSampleRSSKiB=max(r['maxSampleRSSKiB'] for r in records if r['path'].endswith('CP5ConfluenceLocalDiamondSpike.idr')),maxOtherSampleRSSKiB=max(r['maxSampleRSSKiB'] for r in records if not r['path'].endswith('CP5ConfluenceLocalDiamondSpike.idr')),staleLockRemovals=[e for e in window_events+consumer if e['event']=='removed-stale-dead-owner-lock'],noMainLockOrWindow=True,currentForeignLock=current)
(OUT/'final-resource.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ['windowEvents','consumerLockEvents','zeroSampleUnits']},indent=2))
