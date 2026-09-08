#!/usr/bin/env python3
"""Read-only R189 source/cache/census gate; never compiles or deletes seeds."""
import datetime
import hashlib
import json
import pathlib
import re
import subprocess
import sys
ROOT = pathlib.Path(__file__).resolve().parents[1]
START = '8e133ed5'
PARTS = ['CanonicalSort', 'CrossTrace', 'DeletionChain', 'LocalDiamond', 'RenamingComposition']
PATHS = {p: 'research/DGamma/CP5Confluence'+p+'Spike.idr' for p in PARTS}
def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT, text=True)
def text(path):
    return (ROOT/path).read_text()
def sha(data):
    return hashlib.sha256(data).hexdigest()
assert git('branch','--show-current').strip() == 'cp5-thm73-scoping'
assert not git('diff','34b21c9','--','src/','dgamma.ipkg')
assert git('hash-object','src/DGamma/CP3.idr').strip() == '2c697e532e83989de8591fa6a4378747c6a501c0'
assert not git('diff','--cached','--name-only')
assert not git('diff','--name-only')
assert not git('diff','--check',START)
untracked = git('ls-files','--others','--exclude-standard').splitlines()
assert all(p.startswith('paper/') or p == 'review-o6-body-adversarial.md' for p in untracked)
processes = subprocess.check_output(['ps','-axo','pid,ppid,command'],text=True)
assert not re.search(r'/idris2_app/idris2(?:\.so)?(?:\s|$)', processes)
for part in PARTS:
    if part not in ['LocalDiamond','CrossTrace']:
        assert not git('diff',START,'--',PATHS[part]), part
visibility = {}
local = (ROOT/PATHS['LocalDiamond']).read_bytes()
assert local == subprocess.check_output(['git','show',START+':'+PATHS['LocalDiamond']],cwd=ROOT)
start = local.index(b'0 adjacentSwapSuffixSpike :')
full, statement = sha(local[start:start+1470]), sha(local[start:start+1154])
assert full == '2d01486bf953f11191b758ac3cfb5722d1d02b1a192b6e552adc8a3f58199ecf'
assert statement == '3aae5a9fbc5b14e0411b4a91e557a6f3dc68c9a6282b9ec2b3fc658cec337adf'
review = sha((ROOT/'review-o6-body-adversarial.md').read_bytes())
assert review == '61fc23ae4cea4565b442c840be39c41746ecbac73b8c2f73d04f1e3b4f4681e8'
holes = {p:re.findall(r'\?\w+',text(PATHS[p])) for p in PARTS}
closed = '?operationalAdjacentBlockSwapSpike_rhs' not in text(PATHS['CrossTrace'])
assert [len(holes[p]) for p in PARTS] == ([1,2,0,0,1] if closed else [1,3,0,0,1])
protected = {}
for part, name in [('CanonicalSort','sortClosingFreeTraceSpike'),('CrossTrace','operationalAdjacentBlockSwapSpike'),('CrossTrace','selectOperationalCanonicalPermutationSpike'),('CrossTrace','canonicalSchedulesConvergeSpike'),('RenamingComposition','replayedCanonicalToOriginalEndpointSpike')]:
    old = git('show',START+':'+PATHS[part])
    new = text(PATHS[part])
    old_decl = old[old.index('0 '+name+' :'):].split('\n\n',1)[0]
    new_decl = new[new.index('0 '+name+' :'):].split('\n\n',1)[0]
    if name == 'operationalAdjacentBlockSwapSpike':
        old_decl = old_decl.split('\n'+name+' ',1)[0]
        new_decl = new_decl.split('\n'+name+' ',1)[0]
    assert old_decl == new_decl, name
    protected[name] = sha(new_decl.encode())
# Ratified rehome is exact baseline subtraction/concatenation, not a relaxed
# diff whitelist. The only later addition permitted is the exact O19 body.
cross_path=PATHS['CrossTrace']
original=git('show',START+':'+cross_path)
positions=list(re.finditer(r'(?m)^(?:\|\|\|[^\n]*\n)*(?:(?:public export|export|private)\n)?(?=(?:record|data) |(?:[01] )?\w+[ \t]*:)(?:[01] )?(?:(?:record|data) )?([A-Za-z_]\w*)',original))
spans={m[1]:(m.start(),positions[i+1].start() if i+1<len(positions) else len(original)) for i,m in enumerate(positions)}
names=[m[1] for m in positions[:28] if m[1]!='CertifiedActorPermutation']
assert len(names)==27
names+=['CertifiedActorPermutation','OperationalActorPermutation','MappedCanonicalSupportOrders','canonicalActorBlockDecomposition','CertifiedOperationalCanonicalPermutation']
chunks={name:original[slice(*spans[name])] for name in names}
expected_cross=original
for name in names: expected_cross=expected_cross.replace(chunks[name],'',1)
expected_cross=expected_cross.replace('\n\nimport DGamma.Core','\n\nimport public DGamma.CP5O19SurfaceSpike\nimport DGamma.Core',1)
expected_surface=original[:positions[0].start()].replace('module DGamma.CP5ConfluenceCrossTraceSpike','module DGamma.CP5O19SurfaceSpike')+''.join(chunks[name] for name in names[:26]+names[27:]+[names[26]])
assert text('research/DGamma/CP5O19SurfaceSpike.idr')==expected_surface[:-1], 'Only final separating LF normalized by explicit gate'
if closed:
    expected_cross=expected_cross.replace('import public DGamma.CP5O19SurfaceSpike\n','import public DGamma.CP5O19SurfaceSpike\nimport DGamma.CP5O19OperationalAssemblySpike\n',1)
    expected_cross=expected_cross.replace('operationalAdjacentBlockSwapSpike = ?operationalAdjacentBlockSwapSpike_rhs',
      'operationalAdjacentBlockSwapSpike nameEq keyEq protocol orderSwap sourceTrace sourceBlocks sourcePremises sourceUnique applicableSafety =\n  o19ActualOperationalBlockSwap nameEq keyEq protocol orderSwap sourceTrace sourceBlocks sourcePremises applicableSafety sourceUnique',1)
assert text(cross_path)==expected_cross, 'CrossTrace differs beyond ratified move and exact O19 body'
changed = [p for p in git('diff','--name-only',START,'--','research/','research-tests/DGamma/').splitlines() if p.endswith('.idr')]
assert all('%default total' in text(p) for p in changed)
assert not any(re.findall(r'\?\w+',text(p)) for p in changed if p not in PATHS.values())
added = [l[1:] for l in git('diff',START,'--','research/','research-tests/DGamma/').splitlines() if l.startswith('+') and not l.startswith('+++')]
code = '\n'.join(l for l in added if not l.lstrip().startswith(('--','|||')))
patterns = [r'\bbelieve_me\b',r'\bassert_total\b',r'^\s*partial\b',r'\?\w+',r'\blet\b',r'\bwith\b',r'\bprefix\b',r'\bdeletionTheoremProof\b',r'\bpostulate\b',r'\b[A-Za-z_]\w*@\s*[\(\[]']
prohibited = {p:re.findall(p,code,re.M) for p in patterns}
assert not any(prohibited.values()), prohibited
modules = re.findall(r'DGamma\.[A-Za-z0-9_.]+',text('dgamma.ipkg'))
seed = ROOT/'build/ttc/2025081600'
assert len(modules) == 207 and all((seed/(m.replace('.','/')+'.ttc')).exists() for m in modules)
local_ttc = seed/'DGamma/CP5ConfluenceLocalDiamondSpike.ttc'
assert local_ttc.stat().st_size > 125000000 # seeded TTC retained/refreshed by serialized frozen regression
local_time = datetime.datetime.fromtimestamp(local_ttc.stat().st_mtime,datetime.timezone.utc).isoformat()
# No LocalDiamond visibility change in R189; seeded TTC retained without deletion.
report = dict(timestamp=datetime.datetime.now(datetime.timezone.utc).isoformat(),head=git('rev-parse','HEAD').strip(),start=START,
    O19Closed=closed,ratifiedMovedDeclarations=names,holes=holes,split=[len(holes[p]) for p in PARTS],productionDiffVs34b21c9='empty',CP3Blob=git('hash-object','src/DGamma/CP3.idr').strip(),
    LocalDiamondDiffVsStart='empty',LocalDiamondUnchanged=True,LocalDiamondAuthorizedVisibility=visibility,CanonicalSortDiffVsStart='empty',CanonicalSortAuthorizedVisibility={},DeletionChainDiffVsStart='empty',
    CrossTraceDiffVsStart='32 ratified byte-identical declaration moves/public import'+(' + exact authorized O19 body/assembler import' if closed else ''),RenamingCompositionDiffVsStart='empty',
    adjacentFullBytes=1470,adjacentFullSHA256=full,adjacentStatementBytes=1154,adjacentStatementSHA256=statement,reviewSHA256=review,
    seeds='207/207',LocalDiamondTTC=dict(bytes=local_ttc.stat().st_size,mtimeUTC=local_time),changedIdrisFiles=changed,
    sourceSHA256={p:sha((ROOT/p).read_bytes()) for p in changed},protectedDeclarationSHA256=protected,prohibitedAdditions=prohibited,
    noCompiler=True,noStagedFiles=True,cleanTrackedTree=True,allowedUntrackedOnly=True)
out = pathlib.Path(sys.argv[1] if len(sys.argv)>1 else '/tmp/dgamma-r189/frozen.json')
assert str(out).startswith('/tmp/')
out.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
