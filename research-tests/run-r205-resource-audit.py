#!/usr/bin/env python3
"""Read-only resource/invocation audit; never an OS high-water or causation claim."""
import sys,pathlib,json,collections
sys.dont_write_bytecode=True
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from r205_common import *
from r205_evidence_contract import validate_record
records=[json.loads(s) for s in (OUT/'ledger.jsonl').read_text().splitlines()]
by_path=collections.defaultdict(list)
for r in records:
    unit=r['unit']
    validate_record(r,(OUT/(unit+'.source')).read_bytes(),(OUT/(unit+'.log')).read_text(),ROOT)
    assert sha((OUT/(unit+'.runner.py')).read_bytes())==r['runnerSHA256']
    assert sha((OUT/(unit+'.common.py')).read_bytes())==r['commonSHA256']
    assert sha((OUT/(unit+'.sources.json')).read_bytes())==r['sourceManifestSHA256']
    by_path[r['path']].append(r)
entries=[]
for path,rs in sorted(by_path.items()):
    successful=[r for r in rs if r['passed']]
    entries.append(dict(path=path,invocations=[dict(unit=r['unit'],sourceSHA256=r['sourceSHA256'],passed=r['passed'],fresh=r['fresh'],exit=r['exit'],seconds=r['seconds'],sampledPeakKiB=r['maxSampleRSSKiB'],guardKiB=r['rssLimitKiB'],resourceStopped=r['resourceStopped'],ownBuildingLines=len(r['buildingLines'])) for r in rs],maximumObservedSampleKiB=max(r['maxSampleRSSKiB'] for r in rs),maximumSuccessfulSampleKiB=max([r['maxSampleRSSKiB'] for r in successful] or [0]),preUnfreezeIsolatedPeak='UNKNOWN: prior seeded validation is not a fresh isolated cost measurement' if path=='src/DGamma/CP4SupportSolution.idr' else 'Not investigated in R205; no growth claim',qualification='A stopped check is a lower bound on needed resources, not a completed-check peak. Zero samples means the short-lived compiler escaped one-second sampling.'))
report=dict(timestampUTC=utc(),entries=entries,totalInvocations=len(records),passedInvocations=sum(r['passed'] for r in records),resourceStops=[r['unit'] for r in records if r['resourceStopped']],unexpectedDependencyBuilds=[r['unit'] for r in records if r['unexpectedBuilding']],sourceMutationInvocations=[r['unit'] for r in records if r['targetMutationDetected']],multipleCompilerInvocations=[r['unit'] for r in records if r['multipleOwnedCompilers']],crossLaneOverlapTimestampsUTC=[t for r in records for t in r['crossLaneOverlapTimestampsUTC']],measurement='maximum sampled RSS over command-matching idris2 processes; one compiler; one-second samples; NOT aggregate tree RSS, NOT OS high-water. Only the owned process group is ever signalled.',CP4SupportSolutionDatum='isolated measured peak >=64.02GiB under unfrozen CP3; supervisor authorized128GiB for ONE S31-2 attempt. Pre-unfreeze isolated cost UNKNOWN; no claim CP3 caused growth.')
write_json(ROOT/'research-tests/O6-R205-RESOURCE-AUDIT.json',report)
print('verified resource receipts',len(records),'stops',report['resourceStops'])
