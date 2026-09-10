#!/usr/bin/env python3
"""Read-only R199 exact whole-frozen-source/body/census/seed audit; no compiler."""
import datetime, hashlib, json, pathlib, re, subprocess, sys
ROOT=pathlib.Path(__file__).resolve().parents[1]
START='fdf96f9a'
OUT=pathlib.Path('/tmp/dgamma-r199')
def git(*args): return subprocess.check_output(['git',*args],cwd=ROOT,text=True)
def sha(data): return hashlib.sha256(data).hexdigest()
assert git('branch','--show-current').strip()=='cp5-thm73-scoping'
assert not git('diff','34b21c9','--','src/','dgamma.ipkg')
assert git('hash-object','src/DGamma/CP3.idr').strip()=='2c697e532e83989de8591fa6a4378747c6a501c0'
assert not git('diff','--cached','--name-only')
assert not git('diff','--check',START)
assert not git('diff','--name-only','--','src/','research/','research-tests/DGamma/','dgamma.ipkg')
owned=[]; lane2=[]; unknown=[]
for row in subprocess.check_output(['ps','-axo','pid,ppid,command'],text=True).splitlines():
    cells=row.strip().split(None,2)
    if len(cells)!=3 or not re.search(r'/idris2_app/idris2(?:\.so)?(?:\s|$)',cells[2]): continue
    if str(ROOT)+'/' in cells[2]: owned.append(row)
    elif '/Users/vyacheslavshebanov/Work/dgamma-lane2/' in cells[2]: lane2.append(row)
    else: unknown.append(row)
assert not owned and not unknown, 'Main/unknown compiler active (lane2 never killed)'
parts=['CanonicalSort','CrossTrace','DeletionChain','LocalDiamond','RenamingComposition']
paths={p:'research/DGamma/CP5Confluence'+p+'Spike.idr' for p in parts}
contract_states={path:sha((ROOT/path).read_bytes()) for path in paths.values()}
for part,path in paths.items():
    assert (ROOT/path).read_bytes()==subprocess.check_output(['git','show',START+':'+path],cwd=ROOT), part
old_frozen=json.loads((ROOT/'research-tests/O6-R198-FROZEN-AUDIT.json').read_text())
for part in ['LocalDiamond','DeletionChain']:
    assert contract_states[paths[part]]==old_frozen['authorizedContractSourceSHA256'][paths[part]]
assert not git('diff',START,'--','research/DGamma/CP5O19SurfaceSpike.idr')
for old_candidate in ['CP5O20CanonicalSynchronizationGoalSpike','CP5O20StampedHistoryFoldSpike']:
    assert not git('diff',START,'--','research/DGamma/'+old_candidate+'.idr'), 'Old superseded candidate must stay byte-unchanged'
# Entire frozen parts are byte-pinned; this additionally gives named-region hashes.
local=(ROOT/paths['LocalDiamond']).read_bytes(); at=local.index(b'0 adjacentSwapSuffixSpike :')
full=sha(local[at:at+1470]); statement=sha(local[at:at+1154])
assert full=='2d01486bf953f11191b758ac3cfb5722d1d02b1a192b6e552adc8a3f58199ecf'
assert statement=='3aae5a9fbc5b14e0411b4a91e557a6f3dc68c9a6282b9ec2b3fc658cec337adf'
cross=(ROOT/paths['CrossTrace']).read_text(); body='0 operationalAdjacentBlockSwapSpike :'+cross.split('0 operationalAdjacentBlockSwapSpike :',1)[1].split('\n\n',1)[0]
old=git('show',START+':'+paths['CrossTrace']); old_body='0 operationalAdjacentBlockSwapSpike :'+old.split('0 operationalAdjacentBlockSwapSpike :',1)[1].split('\n\n',1)[0]
assert body==old_body
assert len(body.encode())==1286 and sha(body.encode())=='cbd0954303c35141af0309e515bdb9e98e988e7c23be70b9764d8c1ce18fd396'
holes={p:re.findall(r'\?\w+',(ROOT/paths[p]).read_text()) for p in parts}
assert [len(holes[p]) for p in parts]==[1,2,0,0,1]
protected={}
for part,name in [('CanonicalSort','sortClosingFreeTraceSpike'),('CrossTrace','selectOperationalCanonicalPermutationSpike'),('CrossTrace','canonicalSchedulesConvergeSpike'),('RenamingComposition','replayedCanonicalToOriginalEndpointSpike')]:
    text=(ROOT/paths[part]).read_text(); old=git('show',START+':'+paths[part])
    decl=lambda s:('0 '+name+' :'+s.split('0 '+name+' :',1)[1].split('\n\n',1)[0])
    assert decl(text)==decl(old); protected[name]=sha(decl(text).encode())
# All inherited lane-owned source paths stay pinned; only validate them in MAIN.
for path in git('ls-files','research/','research-tests/DGamma/').splitlines():
    if any(k in path for k in ['ActorLifecycleOnlyExtended','CP5AvailabilityAware','CP5L2R','L2R']): assert not git('diff',START,'--',path),path
changed=[p for p in git('diff','--name-only',START,'--','research/','research-tests/DGamma/').splitlines() if p.endswith('.idr')]
assert changed, "R199 retained research modules required"
for p in changed:
    assert '%default total' in (ROOT/p).read_text()
    assert subprocess.run(['git','cat-file','-e',START+':'+p],cwd=ROOT,capture_output=True).returncode!=0, 'Only new source modules are authorized'
assert not git('ls-files','--others','--exclude-standard','--','src/','research/','research-tests/DGamma/')
added=[l[1:] for l in git('diff',START,'--','research/','research-tests/DGamma/').splitlines() if l.startswith('+') and not l.startswith('+++')]
code='\n'.join(l for l in added if not l.lstrip().startswith(('--','|||')))
prohibited={p:re.findall(p,code,re.M) for p in [r'\bbelieve_me\b',r'\bassert_total\b',r'^\s*partial\b',r'\?\w+',r'\blet\b',r'\bwith\b',r'\bprefix\b',r'\bdeletionTheoremProof\b',r'\bpostulate\b']}
assert not any(prohibited.values()),prohibited
review=sha((ROOT/'review-o6-body-adversarial.md').read_bytes());assert review=='61fc23ae4cea4565b442c840be39c41746ecbac73b8c2f73d04f1e3b4f4681e8'
modules=re.findall(r'DGamma\.[A-Za-z0-9_.]+',(ROOT/'dgamma.ipkg').read_text());seed=ROOT/'build/ttc/2025081600'
assert len(modules)==207 and all((seed/(m.replace('.','/')+'.ttc')).is_file() for m in modules)
untracked=git('ls-files','--others','--exclude-standard').splitlines()
allowed=all(p.startswith('paper/') or p=='review-o6-body-adversarial.md' for p in untracked)
clean=not git('diff','--name-only')
if '--allow-artifacts' not in sys.argv: assert allowed and clean
record=dict(timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),head=git('rev-parse','HEAD').strip(),baseline=START,productionDiffVs34b21c9='empty',CP3Blob='2c697e532e83989de8591fa6a4378747c6a501c0',authorizedContractSourceSHA256=contract_states,O19BodyBytes=len(body.encode()),O19BodySHA256=sha(body.encode()),adjacentFullBytes=1470,adjacentFullSHA256=full,adjacentStatementBytes=1154,adjacentStatementSHA256=statement,holes=holes,census=[len(holes[p]) for p in parts],seeds='207/207 retained (presence, not a fresh package PASS)',protectedDeclarations=protected,prohibitedAdditions=prohibited,changedIdrisFiles=changed,noMainCompiler=True,lane2Compilers=[],foreignCompilerObservedAtUTC=([datetime.datetime.now(datetime.timezone.utc).isoformat()] if lane2 else []),noStagedFiles=True,cleanTrackedTree=clean,allowedUntrackedOnly=allowed,untracked=untracked,reviewSHA256=review)
record['supersededCandidateSourceSHA256']={p:sha((ROOT/p).read_bytes()) for p in ['research/DGamma/CP5O20CanonicalSynchronizationGoalSpike.idr','research/DGamma/CP5O20StampedHistoryFoldSpike.idr']}
record['declaredNewSourceNames']={p:re.findall(r'^(?:[01] )?([A-Za-z_]\w*)\s*:',(ROOT/p).read_text(),re.M)+re.findall(r'^(?:record|data)\s+([A-Za-z_]\w*)',(ROOT/p).read_text(),re.M) for p in changed}
record['retainedNewDeclarations']=sum(len(v) for v in record['declaredNewSourceNames'].values())
receipts=[json.loads(s) for s in (OUT/'commit-receipts.jsonl').read_text().splitlines()]
assert record['retainedNewDeclarations']==sum(r['event']=='GUARDED COMMIT' for r in receipts)
output=pathlib.Path(next((s for s in sys.argv[1:] if s.startswith('/tmp/')),str(OUT/'frozen.json')))
output.write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record,indent=2))
