"""Compiler-free independent derivation of R205 evidence claims."""
import hashlib,re

def validate_record(record,source,log,root):
    assert hashlib.sha256(source).hexdigest()==record['sourceSHA256']
    assert log==record['transcript']
    building=re.findall(r'^\d+/\d+: Building (.+)$',log,re.M)
    assert building==record['buildingLines']
    path=record['path']
    assert path=='package' or path.startswith(('src/','research/','research-tests/'))
    if path=='package':
        seeded=record.get('seededPackageNoBuilding',False)
        fresh=not building if seeded else bool(building); unexpected=building if seeded else []; limit=96*1024*1024
    else:
        module=re.search(r'^module\s+([\w.]+)',source.decode(),re.M)[1]
        target=module+' ('+str(root/path)+')'
        fresh=building==[target]
        unexpected=[b for i,b in enumerate(building) if b!=target or i>0]
        stem=path.rsplit('/',1)[-1][:-4]
        limit=(64 if path.startswith('src/') and (stem in ['CP3','CP3StatementChecks'] or stem.startswith('CP4')) else 52 if path.endswith('/CP5ConfluenceLocalDiamondSpike.idr') else 48)*1024*1024
    if record.get('unit') in ['S31-2','S31-3']:
        assert path=='src/DGamma/CP4SupportSolution.idr'
        assert record['sourceSHA256']=='812d874baff27ce025c17ad09527e285079b6ee26a50fec2c4b231723593fda0'
        limit=(128 if record['unit']=='S31-2' else 200)*1024*1024
    if record.get('memoryPressureStopped') or record.get('wallTimeStopped'):
        assert record['interrupted'] and not record['passed']
    if record['resourceStopped']:
        assert record['interrupted'] and not record['passed']
    assert record['fresh']==fresh
    assert record['unexpectedBuilding']==unexpected
    assert record['rssLimitKiB']==limit
    maximum=max([s['rssKiB'] for s in record['rssSamples']] or [0])
    assert maximum==record['maxSampleRSSKiB']
    multiple=any(len(s['ownedPids'])>1 for s in record['rssSamples'])
    assert multiple==record['multipleOwnedCompilers']
    assert record['targetMutationDetected']==bool(record['mutatedPaths'])
    expected=record['expectedDiagnostic'];symbol=record['symbol']
    diagnostic_ok=(record['exit']!=0 and expected in log and symbol and symbol in log) if expected else record['exit']==0 and 'Error:' not in log
    passed=bool(fresh and diagnostic_ok and not record['interrupted'] and not record['mutatedPaths'] and not unexpected and not multiple and maximum<=limit)
    assert passed==record['passed'],'PASS was not justified by exact evidence'
    assert all(record['start']<=s['timestampUTC']<=record['end'] for s in record['rssSamples'])
    assert all(record['start']<=t<=record['end'] for t in record['crossLaneOverlapTimestampsUTC'])
    return passed

def validate_plan(plan,read_source):
    ordered=plan['allModulesTopological']; modules={i['module']:i['path'] for i in ordered}
    assert len(modules)==len(ordered)
    seen=set()
    for item in ordered:
        data=read_source(item['path'])
        assert hashlib.sha256(data).hexdigest()==item['sourceSHA256']
        imports=re.findall(r'^import\s+(?:public\s+)?([\w.]+)',data.decode(),re.M)
        assert imports==item['imports']
        deps={modules[m] for m in imports if m in modules}
        assert deps==set(item['dependencies'])
        assert deps<=seen,'Not import-topological'
        seen.add(item['path'])
    assert {i['path'] for i in plan['targets']}=={p for p in seen if not p.startswith('src/')}
    assert len(seen)==plan['productionCount']+plan['researchFixtureCount']
    return seen
