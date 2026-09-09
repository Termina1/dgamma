"""R205 main-only inventories and frozen-region authentication (no compiler)."""
import datetime, hashlib, json, pathlib, re, subprocess
ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = pathlib.Path('/tmp/dgamma-r205')
START = 'ba88088626a3a497db76df811c2ac08acde9c7bc'
OWNER = 'Давайттак размораживай то что нужно я же все разрешил'
PATCH_SHA = '42d957748fcc67ff534c33a6c369eded4bad65e0f37e5c72e4539b737a68fb8a'
def utc(): return datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(data): return hashlib.sha256(data).hexdigest()
def git(*args): return subprocess.check_output(['git', *args], cwd=ROOT, text=True)
def write_json(path, value):
    path = pathlib.Path(path)
    temp = path.with_suffix(path.suffix + '.tmp')
    temp.write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n')
    temp.replace(path)
def source_paths():
    return sorted(p for p in git('ls-files','src/','research/','research-tests/').splitlines() if p.endswith('.idr'))
def inventory():
    entries = []
    for path in source_paths():
        data = (ROOT/path).read_bytes(); text=data.decode()
        module = re.search(r'^module\s+([\w.]+)', text, re.M)[1]
        ttcs = []
        for ttc in (ROOT/'build/ttc').glob('*/'+module.replace('.','/')+'.ttc'):
            ttcs.append(dict(path=str(ttc.relative_to(ROOT)),sha256=sha(ttc.read_bytes()),bytes=ttc.stat().st_size,mtimeNs=ttc.stat().st_mtime_ns))
        entries.append(dict(path=path,module=module,sourceSHA256=sha(data),bytes=len(data),sourceMtimeNs=(ROOT/path).stat().st_mtime_ns,imports=re.findall(r'^import\s+(?:public\s+)?([\w.]+)',text,re.M),ttc=ttcs))
    return entries
PARTS=['CanonicalSort','CrossTrace','DeletionChain','LocalDiamond','RenamingComposition']
PATHS={p:'research/DGamma/CP5Confluence'+p+'Spike.idr' for p in PARTS}
PROTECTED_PATHS=set(PATHS.values())|{'research/DGamma/CP5O19SurfaceSpike.idr'}
def frozen():
    texts={p:(ROOT/f).read_text() for p,f in PATHS.items()}
    local=texts['LocalDiamond'].encode(); at=local.index(b'0 adjacentSwapSuffixSpike :')
    body=('0 operationalAdjacentBlockSwapSpike :'+texts['CrossTrace'].split('0 operationalAdjacentBlockSwapSpike :',1)[1].split('\n\n',1)[0]).encode()
    bridge=('record ReplayedCanonicalEndpointBridge\n'+texts['RenamingComposition'].split('record ReplayedCanonicalEndpointBridge\n',1)[1].split('\n\n||| Record-style compatibility eliminator',1)[0]).encode()
    holes={p:re.findall(r'\?\w+',texts[p]) for p in PARTS}
    statements={}
    for part,name in [('CanonicalSort','sortClosingFreeTraceSpike'),('CrossTrace','selectOperationalCanonicalPermutationSpike'),('CrossTrace','canonicalSchedulesConvergeSpike'),('RenamingComposition','replayedCanonicalToOriginalEndpointSpike')]:
        decl='0 '+name+' :'+texts[part].split('0 '+name+' :',1)[1].split('\n\n',1)[0]
        statement=decl.split('\n'+name,1)[0]
        statements[name]=dict(path=PATHS[part],statementVerbatim=statement,statementSHA256=sha(statement.encode()),declarationVerbatim=decl,declarationSHA256=sha(decl.encode()))
    regions={'adjacentSwapSuffixSpike':local[at:at+1470],'O19Body':body,'LocalDiamond':local,'DeletionChain':texts['DeletionChain'].encode(),'ReplayedCanonicalEndpointBridge':bridge}
    return dict(regions={k:dict(bytes=len(v),sha256=sha(v)) for k,v in regions.items()},protectedModuleHashes={p:sha((ROOT/p).read_bytes()) for p in sorted(PROTECTED_PATHS)},holes=holes,census=[len(holes[p]) for p in PARTS],holeStatements=statements)
def assert_frozen():
    pre=json.loads((ROOT/'research-tests/O6-R205-PRE-STATE.json').read_text())
    assert frozen()==pre['frozen'], 'Protected source/region/statement changed; separate exact-diff gate required'
def compiler_scopes():
    own, foreign, unknown=[],[],[]
    for row in subprocess.check_output(['ps','-axo','pid,ppid,command'],text=True).splitlines():
        cells=row.strip().split(None,2)
        if len(cells)!=3 or not re.search(r'/idris2_app/idris2(?:\.so)?(?:\s|$)',cells[2]): continue
        if str(ROOT)+'/' in cells[2]: own.append(int(cells[0]))
        elif '/Users/vyacheslavshebanov/Work/dgamma-lane2/' in cells[2]: foreign.append(int(cells[0]))
        else:
            probe=subprocess.run(['lsof','-a','-p',cells[0],'-d','cwd','-Fn'],capture_output=True,text=True)
            dirs=[x[1:] for x in probe.stdout.splitlines() if x.startswith('n')]
            if str(ROOT) in dirs: own.append(int(cells[0]))
            elif '/Users/vyacheslavshebanov/Work/dgamma-lane2' in dirs: foreign.append(int(cells[0]))
            else: unknown.append(int(cells[0]))
    return own,foreign,unknown
