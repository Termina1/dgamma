#!/usr/bin/env python3
"""Compiler-free L2R16 final checked-scope summary. No self-referential commit hash."""
from pathlib import Path
import datetime,hashlib,json,re,subprocess
ROOT=Path('/Users/vyacheslavshebanov/Work/dgamma-lane2');OUT=Path('/tmp/dgamma-l2r16');P='research-tests/O6-L2R16-'
assert Path.cwd()==ROOT

def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT)
closed=json.loads((OUT/'source-closed.json').read_text());final=json.loads((OUT/'final-validation-result.json').read_text());assert final['passed']
state=json.loads((ROOT/(P+'RECHECK-STATE.json')).read_text());decisions=json.loads((OUT/'RECHECK-DECISIONS.json').read_text())
records=[json.loads(s) for s in (OUT/'ledger.jsonl').read_text().splitlines()]
receipts=[json.loads(s) for s in (OUT/'commit-receipts.jsonl').read_text().splitlines()]
source=[r for r in receipts if r['event']=='GUARDED COMMIT']
qualification=[p for p,d in decisions.items() if d.get('kind')=='lexical' and d.get('changes') and all('qualified' in c for c in d['changes'])]
other=[p for p,d in decisions.items() if d.get('kind')=='lexical' and any('qualified' not in c for c in d.get('changes',[]))]
sem=[r for r in source if r['unit'].startswith('S')]
assert not git('diff','--cached','--name-only').strip()
processes=subprocess.check_output(['ps','-axo','pid,ppid,command'],text=True)
assert not any('/idris2_app/idris2' in row and str(ROOT)+'/' in row and re.match(r'^\s*\d+\s+\d+\s+(?:\S*/)?(?:chez|scheme|chezscheme|idris2(?:\.so)?)(?:\s|$)',row) for row in processes.splitlines())
longs=json.loads((OUT/'LONG-PRE-UNFREEZE-RECEIPTS.json').read_text());longnames={x['module'] for x in longs}
long_rows=[]
for row in state['modules']:
 if row['module'] not in longnames:continue
 last=next((r for r in reversed(records) if r['path']==row['path']),None)
 long_rows.append(dict(module=row['module'],status=row['status'],receipt=last['unit'] if last else None,seconds=last['seconds'] if last else None,preUnfreeze=next(x for x in longs if x['module']==row['module'])))
summary=dict(shift='L2R16',timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),sourceBoundary=closed['head'],summaryBoundary=git('rev-parse','HEAD').decode().strip(),boundaryNote='Later metadata-only publication commit is named by the final gate, not recursively embedded here.',production='452420c73c59a6af2d204cafa6e722b3a0fff995',merges=['28da551de112f123eb5dc8f997945c26b919d281','b16591547b55dd05f13c1ac95da8f2b69433b50b'],inheritedTotal=state['total'],inheritedCounts=state['counts'],inheritedFreshGreen=state['counts'].get('PASSED',0)+state['counts'].get('REPAIRED',0),inheritedFullyGreen=state['fullyGreen'],longChecks=long_rows,Tier2=dict(attemptedMicroUnits=18,retainedDeclarations=17,modules=12,kinds=dict(executable=7,type=1,proof=9),failedFullyReverted=['T12'],exhaustedName='L2R16 T12: UniqueRawNameInsertions on the anchor fixture via if-reduction',headline='Exact global-distance-frame instance is rejected CONDITIONALLY on UniqueRawNameInsertions as the sole unassembled premise.',vectors=dict(old=[3,0],crossed=[2,1],total=[3,3],secondTarget=[8,7],anchors=[4,6]),generalNormalizer=False,fullRetirementClaim=False,next='First L2R17 unit: different explicit-dictionary computed uniqueness omega-data route and erased Bool=True consumer; no T12 retry.'),repairs=dict(qualificationOnlyModules=len(qualification),qualificationCap='exempt from40; at most2 attempts each',otherLexicalModules=len(other),otherLexicalCap=40,semanticRestatements=len(sem),guardedSourceCommits=len(source)),compiler=dict(invocations=len(records),freshPasses=sum(r['passed'] for r in records),failedInvocations=[r['unit'] for r in records if not r['passed']],preflightOnly=['V1024','T17-2'],rssDefinition='maximum sampled RSS over command-matching idris2 processes',maximumSampledRSSKiB=max(r['maxSampleRSSKiB'] for r in records),defaultGuardGiB=18,predeclaredHeavyGuardGiB=48,newModuleFinalValidation=final),supportSolution=dict(sha256='0572d487cd7d341c091a94b5fa1d6d6685eade50c2b618f38ffc19fca7dce340',seededMtimePreserved=True,historicalGiB=160.8,rebuilt=False),scope=dict(laneOwnedProductionChanges=False,protectedScopeDiffEmpty=(OUT/'FINAL-PROTECTED-SCOPE.txt').read_bytes()==b'',packageOrColdBuild=False,mainBuildRsyncCount=1,newHoles=0,newUnsafeEscapes=0,productionCensusUnchanged='4 = 1/2/0/0/1; production bytes unchanged by this lane'),evidenceTests=23,changedSourceFiles=sorted({r['paths'][0] for r in source}),toolFiles=[str(p.relative_to(ROOT)) for p in sorted((ROOT/'research-tests').glob('run-l2r16-*.py'))],noStagedFiles=True,ownCompilerRunning=False,mathematicalReview='Parent-owned reviewer gate required; not supplied by mechanical script.',residualRisks=['UniqueRawNameInsertions consumer remains unassembled; T18 is conditional, not full retirement.','Six external R206 blockers may remain; see exact final state and errors.','General physical phase producer, production attachedC adapters, normalizer, four lifecycle shape premises and cross-bundle history remain open.'])
(ROOT/(P+'FINAL-SUMMARY.json')).write_text(json.dumps(summary,indent=2)+'\n');(OUT/'FINAL-SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(dict(inheritedCounts=state['counts'],Tier2Declarations=17,compilerRecords=len(records),sourceCommits=len(source),noStagedFiles=True),indent=2))
