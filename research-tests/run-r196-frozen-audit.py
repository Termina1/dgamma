#!/usr/bin/env python3
"""Read-only R196 exact contract-delta/frozen-body/census/seed audit; no compiler."""
import datetime, hashlib, importlib.util, json, pathlib, re, subprocess, sys
ROOT=pathlib.Path(__file__).resolve().parents[1]
START='58f88c63ea70bca97bc974648f8e4939055fffd7'
OUT=pathlib.Path('/tmp/dgamma-r196')
def git(*args): return subprocess.check_output(['git',*args],cwd=ROOT,text=True)
def sha(data): return hashlib.sha256(data).hexdigest()
spec=importlib.util.spec_from_file_location('contract',ROOT/'research-tests/r196_evidence_contract.py')
contract=importlib.util.module_from_spec(spec);spec.loader.exec_module(contract)
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
manifest_bytes=(ROOT/'research-tests/O6-R196-ROOT-CONTRACT-EXECUTION.json').read_bytes()
assert sha(manifest_bytes)=='18b4ebf7c396b3407f4de3e2fc617dfa86af1bc7849746b0ff63352e07e98340'
manifest=json.loads(manifest_bytes)
possible={}; generated={}
for item in manifest['items']:
    path=item['path']; before=generated.get(path)
    if before is None: before=git('show',START+':'+path); possible[path]=[sha(before.encode())]
    assert sha(before.encode())==item['beforeSHA256']
    after=contract.apply_manifest_diff(before,item['diff'])
    assert sha(after.encode())==item['afterSHA256']
    generated[path]=after; possible[path].append(item['afterSHA256'])
amendment=json.loads((ROOT/'research-tests/O6-R196-A4-SYNTAX-AMENDMENT.json').read_text())
amendment_before=git('show',START+':'+amendment['path'])
assert sha(amendment_before.encode())==amendment['beforeSHA256']
amendment_after=contract.apply_manifest_diff(amendment_before,amendment['diff'])
assert sha(amendment_after.encode())==amendment['afterSHA256']=='7fadaf6b3e71030290813393d8954afee0da79ec93b293fcfcd977deb4562578'
possible[amendment['path']].append(amendment['afterSHA256'])
contract_states={p:sha((ROOT/p).read_bytes()) for p in possible}
assert all(contract_states[p] in possible[p] for p in possible)
parts=['CanonicalSort','CrossTrace','DeletionChain','LocalDiamond','RenamingComposition']
paths={p:'research/DGamma/CP5Confluence'+p+'Spike.idr' for p in parts}
for p in ['CanonicalSort','CrossTrace','RenamingComposition']:
    assert not git('diff',START,'--',paths[p]), p
assert not git('diff',START,'--','research/DGamma/CP5O19SurfaceSpike.idr')
# Entire frozen parts are byte-pinned; this additionally gives named-region hashes.
local=(ROOT/paths['LocalDiamond']).read_bytes(); at=local.index(b'0 adjacentSwapSuffixSpike :')
full=sha(local[at:at+1470]); statement=sha(local[at:at+1154])
assert full=='2d01486bf953f11191b758ac3cfb5722d1d02b1a192b6e552adc8a3f58199ecf'
assert statement=='3aae5a9fbc5b14e0411b4a91e557a6f3dc68c9a6282b9ec2b3fc658cec337adf'
cross=(ROOT/paths['CrossTrace']).read_text(); body='0 operationalAdjacentBlockSwapSpike :'+cross.split('0 operationalAdjacentBlockSwapSpike :',1)[1].split('\n\n',1)[0]
old=git('show',START+':'+paths['CrossTrace']); old_body='0 operationalAdjacentBlockSwapSpike :'+old.split('0 operationalAdjacentBlockSwapSpike :',1)[1].split('\n\n',1)[0]
assert body==old_body
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
for p in changed: assert '%default total' in (ROOT/p).read_text()
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
record=dict(timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),head=git('rev-parse','HEAD').strip(),baseline=START,productionDiffVs34b21c9='empty',CP3Blob='2c697e532e83989de8591fa6a4378747c6a501c0',authorizedContractSourceSHA256=contract_states,O19BodyBytes=len(body.encode()),O19BodySHA256=sha(body.encode()),adjacentFullBytes=1470,adjacentFullSHA256=full,adjacentStatementBytes=1154,adjacentStatementSHA256=statement,holes=holes,census=[len(holes[p]) for p in parts],seeds='207/207 retained (presence, not a fresh package PASS)',protectedDeclarations=protected,prohibitedAdditions=prohibited,changedIdrisFiles=changed,noMainCompiler=True,lane2Compilers=lane2,noStagedFiles=True,cleanTrackedTree=clean,allowedUntrackedOnly=allowed,untracked=untracked,reviewSHA256=review)
output=pathlib.Path(next((s for s in sys.argv[1:] if s.startswith('/tmp/')),str(OUT/'frozen.json')))
output.write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record,indent=2))
