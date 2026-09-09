#!/usr/bin/env python3
"""Compiler-free L2R9 immutable archive/origin/ledger publication.
Does not promote diagnostic evaluation, state recipes, TYPE contracts or failed
producer attempts. Human mathematical review remains parent-owned.
"""
import datetime,hashlib,json,pathlib,re,shutil,subprocess,tarfile
ROOT=pathlib.Path('/Users/vyacheslavshebanov/Work/dgamma-lane2')
OUT=pathlib.Path('/tmp/dgamma-l2r9');BASE='a7120095'
assert pathlib.Path.cwd()==ROOT
records=[json.loads(s) for s in (OUT/'ledger.jsonl').read_text().splitlines()]
receipts=[json.loads(s) for s in (OUT/'commit-receipts.jsonl').read_text().splitlines()]
origins=json.loads((OUT/'declaration-origins-prepublication.json').read_text());assert len(origins)==50
report=json.loads((ROOT/'research-tests/O6-L2R9-PREPUBLICATION-VERIFICATION.json').read_text());assert report['result']=='PASS'
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip();assert report['head']==head
closure=json.loads((OUT/'source-closed.json').read_text());boundary=closure['boundary']
caps={'A':16,'B':12,'C':14,'D':14,'E':3};groups={}
for r in records:
 if re.fullmatch(r'[ABCD]\d+-[1-3]',r['unit']):groups.setdefault(r['unit'].split('-')[0],[]).append(r)
onlyTypes={'OrdinalFixtures','SplitPathPacket','CoreRestorationFixture','NativeLifecycleRetirementRole'}
producedTypes={'RestoredFirstPacket','RestoredLastPacket','ControlClass','PredecessorClass','NativeDistanceSelection','LaneProviderHeadObserved'}
qualifications={
 'releaseOrdinalScan':'GENERAL executable ordinal scan; not old-scan agreement or phase producer',
 'releaseOrdinalLink':'GENERAL exact projection equality to erased enumeration; arbitrary-release completeness/old scan agreement OPEN',
 'ordinalFixtureTrails':'unrestricted native availability trail pair ONLY; REPL [3]/[3] diagnostic, data-agreement proof OPEN',
 'contiguityEndpoints':'native original/restored and split-state-recipe snapshots equal; split execution/restoration OPEN',
 'classifyPredecessor':'GENERAL actual source/action observation sum; selected-native local/missing exclusion and move production OPEN',
 'selectNativeDistanceRoot':'GENERAL actual native-catalog first-positive observation/positive-total decoder + authentic native-birth decoder',
 'rootControlHeadExcluded':'LOCAL exact head-guard contradiction only; whole accepted-scan extraction OPEN',
 'positiveFloorAtGuard':'GENERAL observed conditional-distance/floor arithmetic; no floor producer',
 'rootBirthPredecessorExcluded':'native adjacent root-birth exclusion UNDER numeric externalFloor and stated Front/Never/phase domain',
 'laneNativeAtBool':'GENERIC conditional equality lemma; D5-1 native splice failed, working adapter uses D6 instead',
 'laneProviderHeadSame':'GENERAL native head equality FROM actual observed record, no projected/recreated if type',
 'providerRetirementEntries':'GENERAL exact native provider invariance for an actually installed retirement',
 'resolveRetirementEntries':'GENERAL exact native resolver invariance for an actually installed retirement',
 'retirementFrameResolverSame':'GENERAL primitive AND observed resolver equality from actual RetirementProviderFrame; replay OPEN'}
for o in origins:
 name=o['declaration'];o['status']=qualifications.get(name,'TYPE ONLY; producer/fixture OPEN' if name in onlyTypes else ('checked data/record/family; producer separately listed' if name in producedTypes else 'checked total definition/proof; exact native scope/quantity in source'))
 lines=(ROOT/o['path']).read_text().splitlines();o['line']=next(i for i,s in enumerate(lines,1) if re.match(r'^(?:[01] |record |data )?'+re.escape(name)+r'\b',s))
rows=[]
for u,attempts in sorted(groups.items(),key=lambda x:(x[0][0],int(x[0][1:]))):
 origin=next((o for o in origins if o['unit']==u),None)
 status=origin['status'] if origin else ('STOP3/3; full revert; no restatement' if u in {'A14','B4','B12'} else 'CAP STOP after2/3; third UNUSED; full revert; TYPE ONLY')
 rows.append({'unit':u,'status':status,'declarations':[origin['declaration']] if origin else [],'commit':origin['commit'] if origin else None,'attempts':[{k:r[k] for k in ['unit','passed','fresh','exit','interrupted','sourceSHA256','maxSampleRSSKiB','seconds']} for r in attempts]})
rows.extend([{'unit':'A16','status':'NOT ATTEMPTED; one-slot old-scan agreement cannot close remaining chain; no cap extension','declarations':[],'commit':None,'attempts':[]},{'unit':'B3','status':'NOT LAUNCHED this shift; inherited L2R8 third/final attempt unspent because split producer missing','declarations':[],'commit':None,'attempts':[]}])
rows.sort(key=lambda r:(r['unit'][0],int(r['unit'][1:])))
(OUT/'declaration-origins-enriched.json').write_text(json.dumps(origins,indent=2)+'\n')
micro={'base':BASE,'sourceBoundary':boundary,'archiveBoundary':head,'caps':caps,'attemptedSlots':{'A':15,'B':11,'C':14,'D':14},'retainedByUnit':{'A':14,'B':9,'C':14,'D':13},'retainedDeclarations':50,'stopped3of3':['A14','B4','B12'],'capStopped2of3':['D14'],'notAttempted':['A16','B3'],'EBookkeeping':['E1 ed09d119 exact authorization/source closure','E2 bd28c47b exact predecessor TYPE-comment repair/V5','E3 4dcfd2ab honest Tier-2 sync'],'records':rows}
(ROOT/'research-tests/O6-L2R9-MICRO-UNIT-LEDGER.json').write_text(json.dumps(micro,indent=2)+'\n')
s='# L2R9 declaration origins\n\n50 checked declarations in17 modules. A14/B4/B12 STOP3/3; D14 cap STOP after2/3 (third unused); A16/B3 not attempted. All retained sources have individual final own-target PASS and guarded append-only source receipts. The sole predecessor edit is the exact authorized E2 TYPE comment, not code.\n\n| Unit | Declaration | File:line | Fresh PASS | Commit | Exact status |\n|---|---|---|---|---|---|\n'
for o in sorted(origins,key=lambda r:(r['unit'][0],int(r['unit'][1:]))):s+=f"| {o['unit']} | `{o['declaration']}` | `{pathlib.Path(o['path']).stem}:{o['line']}` | {o['check']} | `{o['commit'][:8]}` | {o['status']} |\n"
s+='''
## Scope/origin qualifications

- A: new unrestricted ordinal data, linked by exact equality to the retained erased enumeration. This is not arbitrary-located-release completeness or old elemDec scan equivalence. Both public trail scans evaluate [3] in ONE authorized REPL diagnostic; fixture agreement and phases are unproduced. No A14/A16/L2R7 A8/L2R8 A10 promotion/re-entry.
- B: native original5+2 and restored3+4 path packets + actual snapshot equality are proved. Split3-edge packet is TYPE ONLY/producer3/3 stopped; exact core restoration TYPE unproduced here/assembly3/3 stopped. No complete17-edge assembly, exact contiguous action-word instance, or universal GeneralCoreContiguityRestored proof.
- C: general actual-source/action sum keeps local/missing cases for arbitrary inputs. Native catalog selection uses actual scanRootCatalog/rootDistance/searchDistance and authentic scanCatalogBirth, not supplied catalog/birth oracles. Numeric-floor exclusion is explicitly conditional; floor production and global control-head extraction remain open. ForcedRootNeverRetired retained; attachedC controls-in-earlier-bundles lift open. Move/D8-from-producer/normalization not attempted in revised branch(A).
- D: ONLY main40d0d59e observed-head TYPE/shape copied to distinct lane names; new lane producers/consumers and native replacement/dependency folds prove general provider/resolver invariance, including actual frame equality. No native view equality is assumed. D4 is checked generic capital, not the working native splice. D5 uses D6 dependent observed-Bool elimination without if reconstruction.
- Lifecycle roles: D13 is a precise three-role TYPE alias requiring original checked edge/frame/current-cut validity and returning alternate checked edge plus exact retired-child snapshot. D14 failed2/3 at LBegin native-owner/lifecycle decoding; its LIter/LFinish source clauses were not independently reached. Third attempt unused at cap; no producer, full single or R191 replay/endpoint claimed.
- All data definitions needed for reduction are public export/unrestricted; proof helpers are erased where indicated. Retained modules are default total/unbound-implicits-off; no unsafe escapes, let/with, postulates or retained failed definitions.
- Existing draft Idris fragments/all30 renamings remain unchanged. Exact E2 before/after hash + fresh V5 are catalogued separately. Complete attached grammar/placement cure remains NOT SIGNABLE; human mathematical review is still parent-owned.
'''
(ROOT/'research-tests/O6-L2R9-DECLARATION-ORIGINS.md').write_text(s)
archive=ROOT/'research-tests/O6-L2R9-COMPILER-EVIDENCE.tar.gz';assert not archive.exists()
tooling=OUT/'tooling';tooling.mkdir()
for p in ROOT.glob('research-tests/run-l2r9-*.py'):shutil.copyfile(p,tooling/p.name)
for p in ROOT.glob('research-tests/O6-L2R9-PREPUBLICATION-VERIFICATION.*'):shutil.copyfile(p,OUT/p.name)
repair=json.loads((ROOT/'research-tests/O6-L2R9-COMMENT-REPAIR.json').read_text())
(OUT/'comment-repair-before.source').write_bytes(subprocess.check_output(['git','show',BASE+':'+repair['path']],cwd=ROOT))
(OUT/'comment-repair-after.source').write_bytes((ROOT/repair['path']).read_bytes())
shutil.copyfile(ROOT/'research-tests/O6-L2R9-COMMENT-REPAIR.json',OUT/'comment-repair-authority.json')
with tarfile.open(archive,'w:gz') as tar:
 for p in sorted(OUT.iterdir()):tar.add(p,arcname='dgamma-l2r9/'+p.name)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
ledger={'shift':'L2R9','base':BASE,'sourceBoundary':boundary,'archiveBoundary':head,'recordCount':len(records),'passedCount':sum(r['passed'] for r in records),'failedCount':sum(not r['passed'] for r in records),'retainedDeclarations':50,'finalOwnTargetChecks':17,'unitCaps':caps,'maximumSampleRSSKiB':max(r['maxSampleRSSKiB'] for r in records),'monitorQualification':'250ms samples, not continuous peak guarantee. Light18 GiB sampled stop; all recorded samples <19 GiB. Main compilers only observed as separate processes; no lock/window operation.','commitReceipts':receipts,'diagnostic':json.loads((OUT/'A14-diagnostic.json').read_text()),'commentRepair':repair,'rulings':json.loads((OUT/'rulings.json').read_text()),'protocolIncidents':json.loads((OUT/'protocol-incidents.json').read_text()),'sourceClosure':closure,'evidenceArchive':archive.name,'evidenceArchiveSHA256':sha(archive),'publicationBoundary':'Archive includes all92 compiler records, final17 checks, one REPL diagnostic, guards/tests/stops and receipts through archiveBoundary. Its own publication/final-report receipts cannot recursively be included; the live append-only receipt ledger authenticates later artifact-only commits. No compiler runs after the final plan.','records':records}
(ROOT/'research-tests/O6-L2R9-COMPILER-LEDGER.json').write_text(json.dumps(ledger,indent=2)+'\n')
print(json.dumps({k:ledger[k] for k in ['recordCount','passedCount','failedCount','retainedDeclarations','maximumSampleRSSKiB','evidenceArchiveSHA256']},indent=2))
