#!/usr/bin/env python3
"""Authenticate native lifetimes, no-lock policy and RSS limits; never inspect shared paths."""
import datetime,hashlib,importlib.util,json,pathlib,subprocess,sys
ROOT=pathlib.Path(__file__).resolve().parents[1];OUT=pathlib.Path('/tmp/dgamma-r203')
sys.dont_write_bytecode=True
spec=importlib.util.spec_from_file_location('contract',ROOT/'research-tests/r203_evidence_contract.py');c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
records=[json.loads(s) for s in (OUT/'ledger.jsonl').read_text().splitlines()]
policy_bytes=(OUT/'execution-policy.json').read_bytes()
for r in records:
    c.validate_execution_policy(r,policy_bytes)
    assert r['rssLimitKiB']==(52 if r['path'].endswith('CP5ConfluenceLocalDiamondSpike.idr') else 48)*1024*1024
    assert r['maxSampleRSSKiB']==max([s['rssKiB'] for s in r['rssSamples']] or [0])
    if r['passed']:assert r['maxSampleRSSKiB']<=r['rssLimitKiB'] and not r['resourceStopped'] and not r['targetMutationDetected']
for first,second in zip(records,records[1:]):assert first['end']<=second['start'], 'Own compiler overlap'
report=dict(status='PASS',timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),invocations=len(records),allCompilerLifetimesCovered=True,sameLaneCompilerIntervalsNonoverlapping=True,crossLaneOverlapTimestampsUTC={r['unit']:r['crossLaneOverlapTimestampsUTC'] for r in records if r['crossLaneOverlapTimestampsUTC']},noLockOperations=True,ownerPolicySHA256=hashlib.sha256(policy_bytes).hexdigest(),resourceStops=[r['unit'] for r in records if r['resourceStopped']],sourceMutations=[r['unit'] for r in records if r['targetMutationDetected']],extraBuildingRejectedUnits=[r['unit'] for r in records if r['unexpectedBuilding']],zeroSampleUnits=[r['unit'] for r in records if not r['maxSampleRSSKiB']],sampleQualification='Own-worktree one-second RSS samples are NOT OS high-water; zero means no live sample captured, not zero actual peak',maxLocalDiamondSampleRSSKiB=max([r['maxSampleRSSKiB'] for r in records if r['path'].endswith('CP5ConfluenceLocalDiamondSpike.idr')] or [0]),maxOtherSampleRSSKiB=max([r['maxSampleRSSKiB'] for r in records if not r['path'].endswith('CP5ConfluenceLocalDiamondSpike.idr')] or [0]),maxUniqueOrdinalSampleRSSKiB=max([r['maxSampleRSSKiB'] for r in records if r['path'].endswith('CP5UniqueRawNameOrdinalCapital.idr')] or [0]),sharedLockPathNotInspected=True)
(OUT/'final-resource.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
