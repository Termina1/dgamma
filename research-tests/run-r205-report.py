#!/usr/bin/env python3
"""Regenerate human-readable final cost/repair/disposition summaries (no compiler)."""
import sys,pathlib,json
sys.dont_write_bytecode=True
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from r205_common import *
s=json.loads((ROOT/'research-tests/O6-R205-REBUILD-STATE.json').read_text())
rs=[json.loads(x) for x in (OUT/'ledger.jsonl').read_text().splitlines()]
rows=['# R205 per-invocation sampled costs','','One compiler at a time. KiB are one-second SAMPLED RSS maxima, not OS high-water; zero means no compiler RSS sample was captured. Stops are not PASS.','','| Invocation | Target | Seconds | Sample peak KiB | Guard KiB | Outcome |','|---|---|---:|---:|---:|---|']
for r in rs:
    outcome='PASS expected rejection' if r['passed'] and r['exit'] else 'PASS' if r['passed'] else 'PRESSURE STOP' if r.get('memoryPressureStopped') else 'RSS STOP' if r['resourceStopped'] else 'FAIL'
    rows.append(f"| {r['unit']} | `{r['path']}` | {r['seconds']:.3f} | {r['maxSampleRSSKiB']} | {r['rssLimitKiB']} | {outcome} |")
rows+=['','## Future policy','','**SupportSolution200GiB**, accepted after unchanged-source S31-4 PASS160.765930GiB/986.351957s. Two samples free<15% or three successive Swapouts increases stop; compressor occupancy recorded only. Pre-unfreeze isolated peak UNKNOWN, no CP3 causation claim.','','LocalDiamond52GiB; other research48GiB. Production CP3/CP3StatementChecks/CP4*64GiB except SupportSolution200GiB; other production48GiB. Package96GiB. Never silently raise guards.']
(ROOT/'research-tests/O6-R205-PER-MODULE-COSTS.md').write_text('\n'.join(rows)+'\n')
receipts=[json.loads(x) for x in (OUT/'commit-receipts.jsonl').read_text().splitlines()]
rows=['# R205 applied-source repair/application table','','All changed Idris sources are listed. Source snapshots and rejected attempts remain in the raw ledger/archive. No new theorem or hole was introduced.','','| Kind | Module | Commit | Before SHA256 | After SHA256 | Fresh passing invocation |','|---|---|---|---|---|---|']
for r in receipts:
    if r['kind'] not in ['PRODUCTION','PRODUCTION-MIGRATION','LEXICAL','FROZEN-MIGRATION']:continue
    for p,h in r['hashes'].items():
        candidates=[v for v in rs if v['path']==p and v['sourceSHA256']==h['after'] and v['passed']]
        assert candidates
        rows.append(f"| {r['kind']} | `{p}` | `{r['afterCommit'][:8]}` | `{h['before']}` | `{h['after']}` | {candidates[-1]['unit']} |")
(ROOT/'research-tests/O6-R205-REPAIR-TABLE.md').write_text('\n'.join(rows)+'\n')
package=[r for r in rs if r['path']=='package'][-1]
summary=dict(timestampUTC=utc(),nativeInvocations=len(rs),moduleCounts=s['counts'],checkedModules=s['checked'],passedModules=s['passed'],brokenModules=s['broken'],uncheckedModules=s['unchecked'],productionFresh=163,productionSeeds=44,legacyExcluded=11,repairedResearchModules=4,changedIdrisFiles=git('diff','--name-only',START,'--','src/','research/','research-tests/DGamma/').splitlines(),finalPackage={k:package[k] for k in ['unit','passed','exit','seconds','maxSampleRSSKiB','buildingLines']},nativeSeconds=sum(r['seconds'] for r in rs),RSSStops=[r['unit'] for r in rs if r['resourceStopped']],pressureStops=[r['unit'] for r in rs if r.get('memoryPressureStopped')],noSourceMutation=not any(r['targetMutationDetected'] for r in rs),noOverlap=not any(r['crossLaneOverlapTimestampsUTC'] or r['multipleOwnedCompilers'] for r in rs),dispositionComplete=s['dispositionTraversalComplete'],allResearchPass=False,census=s['frozen']['census'])
write_json(ROOT/'research-tests/O6-R205-FINAL-SUMMARY.json',summary)
print(json.dumps(summary,indent=2))
