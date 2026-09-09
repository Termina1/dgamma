#!/usr/bin/env python3
"""Adapted from run-l2r7-archive.py: archive this bounded lane's actual records.
Compiler-free; writes only L2R8 evidence artifacts. Handles A10 stopped3/3,
B3 deferred2/3 and the authorized C1-C5 scope; no fictitious cap completion.
"""
import datetime,hashlib,json,pathlib,re,shutil,subprocess,tarfile
ROOT=pathlib.Path('/Users/vyacheslavshebanov/Work/dgamma-lane2');OUT=pathlib.Path('/tmp/dgamma-l2r8');BASE='4469421e'
assert pathlib.Path.cwd()==ROOT
records=[json.loads(s) for s in (OUT/'ledger.jsonl').read_text().splitlines()]
receipts=[json.loads(s) for s in (OUT/'commit-receipts.jsonl').read_text().splitlines()]
origins=json.loads((OUT/'declaration-origins-prepublication.json').read_text());assert len(origins)==37
report=json.loads((ROOT/'research-tests/O6-L2R8-PREPUBLICATION-VERIFICATION.json').read_text());assert report['result']=='PASS'
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip();assert report['head']==head
caps={'A':10,'B':14,'C':8,'D':10,'E':3};groups={}
for r in records:
 if re.fullmatch(r'[ABCD]\d+-[1-3]',r['unit']):groups.setdefault(r['unit'].split('-')[0],[]).append(r)
types={'ObservedReleaseFixtures','ContiguityNativeExecution','GeneralCoreContiguityRestored','PlacedPrefixPhaseInvariant','LocatedExtendedCore'}
recordTypes={'DistanceSearch','RegionEmbedding','OriginObservation'}
for o in origins:
 name=o['declaration'];o['status']='TYPE ONLY; producer/fixture OPEN' if name in types else ('checked record/family; producer separately listed' if name in recordTypes else ('executable explicit states ONLY; native fixture DEFERRED' if name=='contiguityState' else 'checked total definition/proof; exact scope and quantity in source/audit'))
 lines=(ROOT/o['path']).read_text().splitlines();o['line']=next(i for i,s in enumerate(lines,1) if re.match(r'^(?:[01] |record |data )?'+re.escape(name)+r'\b',s))
rows=[]
for u,attempts in sorted(groups.items(),key=lambda x:(x[0][0],int(x[0][1:]))):
 origin=next((o for o in origins if o['unit']==u),None)
 status=origin['status'] if origin else ('STOPPED3/3; full revert; no restatement' if u=='A10' else 'DEFERRED2/3; full revert; one attempt remains only under future gate')
 rows.append({'unit':u,'status':status,'declarations':[origin['declaration']] if origin else [],'commit':origin['commit'] if origin else None,'attempts':[{k:r[k] for k in ['unit','passed','fresh','exit','interrupted','sourceSHA256','maxSampleRSSKiB','seconds']} for r in attempts]})
(OUT/'declaration-origins-enriched.json').write_text(json.dumps(origins,indent=2)+'\n')
(ROOT/'research-tests/O6-L2R8-MICRO-UNIT-LEDGER.json').write_text(json.dumps({'base':BASE,'sourceBoundary':'d11d13c0','archiveBoundary':head,'caps':caps,'attemptedSlots':{'A':10,'B':14,'C':5,'D':10},'CQualification':'Supervisor explicitly authorized finite-iteration arithmetic and placed-prefix invariant TYPE; scope complete at C5, NOT general normalization.','retainedDeclarations':37,'stopped':['A10'],'deferred':['B3'],'records':rows},indent=2)+'\n')
s='# L2R8 declaration origins\n\n37 checked declarations in12 modules. A10 stopped3/3; B3 deferred2/3. All retained sources have own-target final PASS and guarded source receipts. No predecessor proof edit.\n\n| Unit | Declaration | File:line | Fresh PASS | Commit | Status |\n|---|---|---|---|---|---|\n'
for o in origins:s+=f"| {o['unit']} | `{o['declaration']}` | `{pathlib.Path(o['path']).stem}:{o['line']}` | {o['check']} | `{o['commit'][:8]}` | {o['status']} |\n"
s+='''\n## Exact origin/scope qualifications\n\n- SharedKey/ReleaseScan: NEW isElem call-site observations. General AnyHit shared-key extraction and native located own-child release enumeration are quantity-0 proofs, not runtime ordinal decoders. releaseScanAgrees with the unchanged Bool scan remains OPEN. A10 concrete agreement producer was fully reverted.\n- ContiguityStates/Execution: explicit one-origin schedule states and a parameterized17-edge/2-endpoint contract only. The finite proof producer B3 is deferred after two18 GiB light stops. No native crossing/core-restoration fixture exists.\n- CoreContract: complete physical core contract and general action-word restoration obligation TYPE. Exact core-state equality is not claimed; final endpoints are RegistryExtensional in the uninhabited conclusion.\n- NativeWords: GENERAL exact physical length and executable concatenation with full native action-word transport; not a swap/existence theorem.\n- DistanceSearch: NEW unrestricted ordered first-positive search with producer-owned Nat observations, exact zero-prefix and decomposition; a positive-total observed result gives a genuine first-positive witness. Actual native catalog fixture instantiation, forcing linkage and move existence remain OPEN.\n- IterationArithmetic/PrefixPhase: proof-erased count, GENERAL given-chain balance, terminal-zero count and length bound; revised exact placed-prefix/selected-root invariant TYPE. Not normalization; move/phase producers open. No old iteration obligation weakened; D8 not reproduced from general producers.\n- RegionEmbedding: GENERAL actual prefix/region/suffix occurrence embedding with exact offset + local ordinal, same native source and root-control-kind transport. No front/NF/placement oracle. Inter-block integration still needs the corresponding actual decomposition/offset equations.\n- OriginMembership: GENERAL authentic maximum/filtered-catalog ordinal membership and unrestricted unchanged rootOriginAt observation producer. Map/filter-to-entry/native-birth identity and maximality converse remain OPEN.\n- No produceForcedRootPhases, produceAdmittedDistanceMove, normalizePhaseDistance, produceAttachedNormalForm or all-premises-produced zero-gap application is retained or claimed.\n'''
(ROOT/'research-tests/O6-L2R8-DECLARATION-ORIGINS.md').write_text(s)
archive=ROOT/'research-tests/O6-L2R8-COMPILER-EVIDENCE.tar.gz';assert not archive.exists()
tooling=OUT/'tooling';tooling.mkdir()
for p in ROOT.glob('research-tests/run-l2r8-*.py'):shutil.copyfile(p,tooling/p.name)
for p in ROOT.glob('research-tests/O6-L2R8-PREPUBLICATION-VERIFICATION.*'):shutil.copyfile(p,OUT/p.name)
with tarfile.open(archive,'w:gz') as tar:
 for p in sorted(OUT.iterdir()):tar.add(p,arcname='dgamma-l2r8/'+p.name)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
ledger={'shift':'L2R8','base':BASE,'sourceBoundary':'d11d13c0','archiveBoundary':head,'recordCount':len(records),'passedCount':sum(r['passed'] for r in records),'failedCount':sum(not r['passed'] for r in records),'retainedDeclarations':37,'finalOwnTargetChecks':12,'unitCaps':caps,'maximumSampleRSSKiB':max(r['maxSampleRSSKiB'] for r in records),'monitorQualification':'250ms samples, not continuous peak guarantee. Light18 GiB stop is stricter than48 GiB; all recorded samples <19 GiB. Two B3 sampled18 GiB stops, no lock interaction.','commitReceipts':receipts,'rulings':json.loads((OUT/'rulings.json').read_text()),'protocolIncidents':json.loads((OUT/'protocol-incidents.json').read_text()),'resumeAndScopeRulings':json.loads((OUT/'E-resume-rulings.json').read_text()),'evidenceArchive':archive.name,'evidenceArchiveSHA256':sha(archive),'publicationBoundary':'Archive contains all proof/final checks and E1 receipt. E2/E3 artifact receipts cannot recursively be inside their own archive; live append-only receipts authenticate them.','records':records}
(ROOT/'research-tests/O6-L2R8-COMPILER-LEDGER.json').write_text(json.dumps(ledger,indent=2)+'\n')
print(json.dumps({k:ledger[k] for k in ['recordCount','passedCount','failedCount','retainedDeclarations','maximumSampleRSSKiB','evidenceArchiveSHA256']},indent=2))
