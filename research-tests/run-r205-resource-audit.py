#!/usr/bin/env python3
"""Read-only resource/invocation audit; never an OS high-water or causation claim."""
import sys,pathlib,json,collections
sys.dont_write_bytecode=True
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from r205_common import *
from r205_evidence_contract import validate_record
from r205_pressure import parse_vm_stat,steady_growth,free_percent,corrected_pressure_stop
records=[json.loads(s) for s in (OUT/'ledger.jsonl').read_text().splitlines()]
by_path=collections.defaultdict(list)
for r in records:
    unit=r['unit']
    validate_record(r,(OUT/(unit+'.source')).read_bytes(),(OUT/(unit+'.log')).read_text(),ROOT)
    assert sha((OUT/(unit+'.runner.py')).read_bytes())==r['runnerSHA256']
    assert sha((OUT/(unit+'.common.py')).read_bytes())==r['commonSHA256']
    assert sha((OUT/(unit+'.sources.json')).read_bytes())==r['sourceManifestSHA256']
    if unit in ['S31-3','S31-4']:
        pressure=r['memoryPressureSamples']
        for sample in pressure:
            assert all(sample[k]==v for k,v in parse_vm_stat(sample['vmStatRaw']).items())
        assert r['rssLimitKiB']==200*1024*1024
        if unit=='S31-4':
            for sample in pressure:assert free_percent(sample['memoryPressureQueryRaw'])==sample['freePercent']
        if r['memoryPressureStopped'] and not r['memoryPressureSamplingError']:assert (steady_growth(pressure) if unit=='S31-3' else corrected_pressure_stop(pressure))
        if r['wallTimeStopped']:assert r['seconds']>=(2700 if unit=='S31-3' else 3600)
    by_path[r['path']].append(r)
entries=[]
for path,rs in sorted(by_path.items()):
    successful=[r for r in rs if r['passed']]
    entries.append(dict(path=path,invocations=[dict(unit=r['unit'],sourceSHA256=r['sourceSHA256'],passed=r['passed'],fresh=r['fresh'],exit=r['exit'],seconds=r['seconds'],sampledPeakKiB=r['maxSampleRSSKiB'],guardKiB=r['rssLimitKiB'],resourceStopped=r['resourceStopped'],memoryPressureStopped=r.get('memoryPressureStopped',False),wallTimeStopped=r.get('wallTimeStopped',False),ownBuildingLines=len(r['buildingLines'])) for r in rs],maximumObservedSampleKiB=max(r['maxSampleRSSKiB'] for r in rs),maximumSuccessfulSampleKiB=max([r['maxSampleRSSKiB'] for r in successful] or [0]),preUnfreezeIsolatedPeak='UNKNOWN: prior seeded validation is not a fresh isolated cost measurement' if path=='src/DGamma/CP4SupportSolution.idr' else 'Not investigated in R205; no growth claim',qualification='A stopped check is a lower bound on needed resources, not a completed-check peak. Zero samples means the short-lived compiler escaped one-second sampling.'))
report=dict(timestampUTC=utc(),entries=entries,totalInvocations=len(records),passedInvocations=sum(r['passed'] for r in records),resourceStops=[r['unit'] for r in records if r['resourceStopped']],memoryPressureStops=[r['unit'] for r in records if r.get('memoryPressureStopped')],wallTimeStops=[r['unit'] for r in records if r.get('wallTimeStopped')],unexpectedDependencyBuilds=[r['unit'] for r in records if r['unexpectedBuilding']],sourceMutationInvocations=[r['unit'] for r in records if r['targetMutationDetected']],multipleCompilerInvocations=[r['unit'] for r in records if r['multipleOwnedCompilers']],crossLaneOverlapTimestampsUTC=[t for r in records for t in r['crossLaneOverlapTimestampsUTC']],measurement='maximum sampled RSS over command-matching idris2 processes; one compiler; one-second samples; NOT aggregate tree RSS, NOT OS high-water. Only the owned process group is ever signalled.',CP4SupportSolutionDatum='isolated stops >=64.02GiB and128.21GiB under unfrozen CP3. S31-3 pressure-stopped at147.61GiB. NEW supervisor-owned gate acknowledges pressure-rule miscalibration and authorizes S31-4 at200GiB/60min:two samples free<15% OR three rising swapouts; compressor counts recorded only. S31-4 PASSED at160.765930GiB/986.351957s; future SupportSolution guard200GiB accepted by datum. Pre-unfreeze isolated cost UNKNOWN; no claim CP3 caused growth; see diagnosis (zero patched-type matches).')
write_json(ROOT/'research-tests/O6-R205-RESOURCE-AUDIT.json',report)
print('verified resource receipts',len(records),'RSS stops',report['resourceStops'],'pressure stops',report['memoryPressureStops'])
