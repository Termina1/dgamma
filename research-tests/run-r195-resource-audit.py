"""Read-only R195 sampled-resource/shared-lock audit; no compiler or git writes."""
import datetime, json, pathlib
ROOT = pathlib.Path('/Users/vyacheslavshebanov/Work/dgamma')
OUT = pathlib.Path('/tmp/dgamma-r195')
assert (OUT / 'final-validation-complete.json').exists()
records = [json.loads(line) for line in (OUT / 'ledger.jsonl').read_text().splitlines()]
known = set(json.loads((ROOT / 'research-tests/O6-R195-HEAVY-PATHS.json').read_text()))
heavy = []
for r in records:
    required = r['path'] in known or pathlib.Path(r['path']).stem.startswith('R8') or r['maxSampleRSSKiB'] >= 19 * 1024 * 1024
    assert r['maxSampleRSSKiB'] == max([s['rssKiB'] for s in r['rssSamples']] or [0])
    assert not r['targetMutationDetected'] and not r['interrupted']
    assert r['maxSampleRSSKiB'] <= r['rssLimitKiB']
    if required:
        acquired = [e for e in r['heavyLock'] if e['event'] == 'acquired']
        assert len(acquired) == 1 and acquired[0]['lane'] == 'R195-main' and acquired[0]['unit'] == r['unit']
        assert acquired[0]['path'] == r['path']
        monitor = OUT / (r['unit'] + '.monitor')
        assert 'HEAVY LOCK RELEASE ' + r['unit'] in monitor.read_text()
        heavy.append(dict(unit=r['unit'], path=r['path'], peakRSSKiB=r['maxSampleRSSKiB'], acquired=acquired[0], releaseObserved=True))
report = dict(status='PASS', timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    invocationCount=len(records), knownOrObservedHeavyCount=len(heavy), heavyChecks=heavy,
    maxSampleRSSKiB=max(r['maxSampleRSSKiB'] for r in records),
    noLiveSampleUnits=[r['unit'] for r in records if r['maxSampleRSSKiB'] == 0],
    staleLockCleanups=[dict(unit=r['unit'], event=e) for r in records for e in r['heavyLock'] if e['event'] != 'acquired'],
    interruptions=0, targetMutations=0, allKnownOrObservedHeavyChecksLockedAndReleased=True,
    qualification='1-second retained RSS samples, not OS high-water. Zero means no live sample captured. No lane2 process was counted or killed.')
(OUT / 'resource-audit.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
