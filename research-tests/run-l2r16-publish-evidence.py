#!/usr/bin/env python3
"""L2R16 compiler-free evidence publisher, adapted from L2R15.
Derives declaration/repair origins from actual git blobs and guarded receipts.
Archives the immutable raw boundary; excludes its later publication receipt.
Does not claim mathematical review. RSS = maximum sampled RSS over
command-matching idris2 processes, not an aggregate or OS high-water mark.
"""
from pathlib import Path
import datetime,gzip,hashlib,io,json,re,subprocess,tarfile
ROOT=Path('/Users/vyacheslavshebanov/Work/dgamma-lane2');RAW=Path('/tmp/dgamma-l2r16')
P='research-tests/O6-L2R16-'
assert Path.cwd()==ROOT

def sha(data):return hashlib.sha256(data).hexdigest()
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT)
def decls(data):
 text=data.decode();return set(re.findall(r'^(?:[01] )?([A-Za-z_]\w*)\s*:',text,re.M)+re.findall(r'^(?:record|data)\s+([A-Za-z_]\w*)',text,re.M))
def write(suffix,value):(ROOT/(P+suffix)).write_text(json.dumps(value,indent=2)+'\n')
closed=json.loads((RAW/'source-closed.json').read_text())
final=json.loads((RAW/'final-validation-result.json').read_text());assert final['passed']
assert not git('diff','--cached','--name-only').strip()
processes=subprocess.check_output(['ps','-axo','pid,ppid,command'],text=True)
assert not any('/idris2_app/idris2' in row and str(ROOT)+'/' in row and re.match(r'^\s*\d+\s+\d+\s+(?:\S*/)?(?:chez|scheme|chezscheme|idris2(?:\.so)?)(?:\s|$)',row) for row in processes.splitlines())
records=[json.loads(s) for s in (RAW/'ledger.jsonl').read_text().splitlines()]
receipts=[json.loads(s) for s in (RAW/'commit-receipts.jsonl').read_text().splitlines()]
byid={r['unit']:r for r in records};source_receipts=[r for r in receipts if r['event']=='GUARDED COMMIT']
decisions=json.loads((RAW/'RECHECK-DECISIONS.json').read_text())
boundary=git('rev-parse','HEAD').decode().strip();now=datetime.datetime.now(datetime.timezone.utc).isoformat()
origins=[];repairs=[]
for receipt in source_receipts:
 r=byid[receipt['invocation']];commit=receipt['resultingCommitHash'];path=r['path'];data=git('show',commit+':'+path)
 old=subprocess.run(['git','show',commit+'^:'+path],cwd=ROOT,capture_output=True)
 before=old.stdout if old.returncode==0 else b'';added=decls(data)-decls(before);removed=decls(before)-decls(data)
 row=dict(unit=receipt['unit'],invocation=receipt['invocation'],commit=commit,path=path,beforeSHA256=sha(before),checkedSourceSHA256=r['sourceSHA256'],currentSourceSHA256=sha((ROOT/path).read_bytes()),declarationsAdded=sorted(added),declarationsRemoved=sorted(removed))
 if receipt['unit'].startswith('T'):
  assert len(added)==1 and not removed
  name=next(iter(added));current=(ROOT/path).read_text();match=re.search(r'^(?:[01] )?'+re.escape(name)+r'\s*:|^(?:record|data)\s+'+re.escape(name)+r'\b',current,re.M);assert match
  line=current[:match.start()].count('\n')+1
  is_record=bool(re.search(r'^(?:record|data)\s+'+re.escape(name)+r'\b',current,re.M))
  kind='type' if is_record else ('proof' if re.search(r'^0 '+re.escape(name)+r'\s*:',current,re.M) else 'executable')
  status=closed['statusByUnit'][receipt['unit']]
  row.update(name=name,line=line,kind=kind,status=status);origins.append(row)
 else:
  row['classification']=decisions.get(path,{}).get('category',decisions.get(path,{}).get('kind','authorized-semantic'))
  row['changes']=decisions.get(path,{}).get('changes',[]);repairs.append(row)
assert len(origins)==closed['retainedDeclarations']==17
assert len({x['path'] for x in origins})==closed['retainedModules']
# All files are regular files; there is no recursive symlink traversal or TTC copy.
raw={p.name:p.read_bytes() for p in sorted(RAW.iterdir()) if p.is_file() and p.name not in ['PUBLISH-EVIDENCE.log','INDEPENDENT-ARCHIVE-VERIFY.log']}
archive=ROOT/(P+'RAW-EVIDENCE.tar.gz')
with archive.open('wb') as out:
 with gzip.GzipFile(filename='',mode='wb',fileobj=out,mtime=0) as gz:
  with tarfile.open(fileobj=gz,mode='w') as tf:
   for name,data in raw.items():
    info=tarfile.TarInfo('raw/'+name);info.size=len(data);info.mode=0o644;info.mtime=0;tf.addfile(info,io.BytesIO(data))
write('RAW-EVIDENCE-MANIFEST.json',dict(archive=str(archive.relative_to(ROOT)),archiveSHA256=sha(archive.read_bytes()),boundaryHead=boundary,boundaryUTC=now,receiptScope='All raw compiler/preflight/source snapshots, bounded repair/proof receipts, merge/reseed authorities, visibility companion and final validation evidence through this boundary. Later archive-publication receipt is excluded to avoid self-reference. Publisher/archived-verifier output logs are excluded.',files={name:dict(sha256=sha(data),bytes=len(data)) for name,data in raw.items()}))
groups={}
for r in records:
 if not r['unit'].startswith('V'):groups.setdefault(r['unit'].rsplit('-',1)[0],[]).append(r)
statement_groups=[]
for unit,rows in sorted(groups.items(),key=lambda x:(x[0][0],int(x[0][1:]))):
 attempts=[r['unit'] for r in rows];preflights=['T17-2'] if unit=='T17' else []
 statement_groups.append(dict(unit=unit,compilerInvocations=attempts,preflightOnlyRequests=preflights,requestCount=len(attempts)+len(preflights),status='guarded PASS' if any(r['passed'] for r in rows) else 'FULL REVERT + AUDIT',successfulInvocation=next((r['unit'] for r in rows if r['passed']),None)))
write('MICRO-UNIT-LEDGER.json',dict(sourceBoundary=closed,T2Declarations=origins,repairs=repairs,statementAttemptGroups=statement_groups,visibilityCompanion=json.loads((RAW/'VISIBILITY-COMPANION-AUTHORITY.json').read_text()),exhausted=[json.loads((RAW/'T12-STOP.json').read_text())],preflightOnly=[json.loads((RAW/'V1024-PREFLIGHT-REJECTION.json').read_text()),json.loads((RAW/'T17-2-PREFLIGHT-REJECTION.json').read_text())],documentationUnits=[dict(unit='O1',status='live Tier2 status supersedes signed historical patch'),dict(unit='O2',status='source boundary, import-ordered final validation and final audit'),dict(unit='O3',status='archive, generated origins/ledgers and independent mechanical verification')],unattemptedUniquenessAlternative='First L2R17 micro-unit: explicit-dictionary computed uniqueness omega-data check and erased Bool=True consumer; NOT a T12 retry.'))
commit_by_id={r['invocation']:r['resultingCommitHash'] for r in source_receipts};summary=[];overlaps=[]
for r in records:
 keys=['unit','path','start','end','seconds','exit','passed','fresh','interrupted','sourceMutationObserved','sourceSHA256','maxSampleRSSKiB','buildingCount','buildingLines','expectedDiagnostic','declaredHeavy','rssLimitKiB']
 row={k:r[k] for k in keys};row.update(guardedSourceCommit=commit_by_id.get(r['unit']),rawRecord='raw/'+r['unit']+'.json',deadlineInterrupted=r.get('deadlineInterrupted',False),deadlineStopUTC=r.get('deadlineStopUTC'));summary.append(row)
 for x in r['separateCompilerObservations']:overlaps.append(dict(invocation=r['unit'],firstObservedUTC=x['firstObservedUTC'],lastObservedUTC=x['lastObservedUTC']))
write('COMPILER-LEDGER.json',dict(boundaryHead=boundary,rssDefinition='maximum sampled RSS over command-matching idris2 processes',invocations=summary,archive=str(archive.relative_to(ROOT)),archiveSHA256=sha(archive.read_bytes()),guardedReceipts=receipts))
write('OVERLAP-LOG.json',dict(timestampObservations=overlaps,foreignCompilersNeverSignalled=True,format='Timestamp-only observations throughout L2R16; no foreign PID/RSS/command metadata persisted. No shared locks or rebuild windows.'))
qualifications=[dict(path=path,unit=d.get('repairUnit',d.get('unit')),names=[dict(name=c['name'],qualified=c['qualified'],occurrences=c.get('occurrences')) for c in d['changes']]) for path,d in decisions.items() if d.get('kind')=='lexical' and d.get('changes') and all('qualified' in c for c in d['changes'])]
write('QUALIFICATION-TABLE.json',dict(capAuthority='QUALIFICATION-RULING.json: qualification-only modules exempt from40, at most2 attempts',modules=qualifications))
lines=['# L2R16 declaration and repair origins','',f"Boundary **{boundary[:8]}**; **17 checked Tier2 declarations in {closed['retainedModules']} modules**.",'T12 was completely reverted. T18 is conditional on uniqueness; no unconditional normalization or full global-frame retirement is claimed.','RSS terminology is fixed in the compiler ledger. TYPE definitions and their inhabitants are separate.','','| Unit | Source:name | Kind and exact status | Invocation | Guarded commit |','|---|---|---|---|---|']
for r in origins:lines.append(f"| {r['unit']} | `{Path(r['path']).name}:{r['line']}:{r['name']}` | {r['kind']}: {r['status']} | {r['invocation']} | `{r['commit'][:8]}` |")
lines+=['','## Repair origins','',f'{len(repairs)} separately guarded lexical/semantic repair commits. Full before/after hashes and signature deltas are in MICRO-UNIT-LEDGER; namespace names/occurrence counts are in QUALIFICATION-TABLE.','', '## Exhausted and unattempted','', '- L2R16 T12: UniqueRawNameInsertions on the anchor fixture via if-reduction — interface-vs-primitive wall; 3/3 failed, fully reverted.', '- The different explicit-dictionary uniqueness data-agreement route was not attempted; it is the first proposed L2R17 micro-unit.', '', 'Mechanical verification is not parent-owned mathematical review. No lane-owned production or protected-source change occurred.', '']
(ROOT/(P+'DECLARATION-ORIGINS.md')).write_text('\n'.join(lines))
print(json.dumps(dict(archiveSHA256=sha(archive.read_bytes()),archiveFiles=len(raw),T2Declarations=len(origins),repairCommits=len(repairs),records=len(records),freshPasses=sum(r['passed'] for r in records),overlapObservations=len(overlaps)),indent=2))
