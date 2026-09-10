#!/usr/bin/env python3
"""Capture and independently verify R205 raw evidence plus current source/artifacts.
No extraction, symlinks, cache trust, compiler or execution of archived code.
"""
import sys,pathlib,json,tarfile,gzip,io,hashlib
sys.dont_write_bytecode=True
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from r205_common import *
assert compiler_scopes()==([],[],[])
assert json.loads((OUT/'active.json').read_text())['status']=='IDLE'
assert not git('diff','--cached','--name-only').strip()
assert_frozen()
archive=ROOT/'research-tests/O6-R205-RAW-EVIDENCE.tar.gz'
manifest_path=ROOT/'research-tests/O6-R205-ARCHIVE-MANIFEST.json'
verification_path=ROOT/'research-tests/O6-R205-ARCHIVE-VERIFICATION.json'
files={}
for p in sorted(OUT.rglob('*')):
    if p.is_file():
        assert not p.is_symlink();files['raw/'+str(p.relative_to(OUT))]=p
for path in source_paths()+['dgamma.ipkg']:
    files['current-source/'+path]=ROOT/path
for p in sorted((ROOT/'research-tests').glob('*r205*.py')):files['artifacts/research-tests/'+p.name]=p
for p in sorted((ROOT/'research-tests').glob('O6-R205-*')):
    if p.is_file() and p not in [archive,manifest_path,verification_path] and p.suffix!='.gz':files['artifacts/research-tests/'+p.name]=p
for p in ['README.md','NOTES.md','THM73-PLAN.md']:files['artifacts/'+p]=ROOT/p
entries={name:dict(bytes=p.stat().st_size,sha256=sha(p.read_bytes())) for name,p in sorted(files.items())}
manifest=dict(timestampUTC=utc(),headAtCapture=git('rev-parse','HEAD').strip(),rawCutoff='All371 native invocations through final P3; later artifact-only commits and supervisor final ruling may be outside this capture.',entries=entries)
manifest_bytes=(json.dumps(manifest,indent=2,sort_keys=True)+'\n').encode()
def add(tar,name,data):
    info=tarfile.TarInfo(name);info.size=len(data);info.mtime=0;info.mode=0o644;tar.addfile(info,io.BytesIO(data))
with archive.open('wb') as destination:
    with gzip.GzipFile(filename='',mode='wb',fileobj=destination,mtime=0) as zipped:
        with tarfile.open(fileobj=zipped,mode='w') as tar:
            add(tar,'MANIFEST.json',manifest_bytes)
            for name,p in sorted(files.items()):
                data=p.read_bytes();assert sha(data)==entries[name]['sha256'];add(tar,name,data)
# Independently enumerate archive bytes; reject duplicates, links or unexpected members.
with tarfile.open(archive,'r:gz') as tar:
    members=tar.getmembers();names=[m.name for m in members]
    assert len(names)==len(set(names)) and set(names)==set(entries)|{'MANIFEST.json'}
    assert all(m.isfile() and '..' not in pathlib.PurePosixPath(m.name).parts and not m.name.startswith('/') for m in members)
    assert tar.extractfile('MANIFEST.json').read()==manifest_bytes
    for name,entry in entries.items():
        data=tar.extractfile(name).read();assert len(data)==entry['bytes'] and sha(data)==entry['sha256']
    ledger=[json.loads(x) for x in tar.extractfile('raw/ledger.jsonl').read().splitlines()]
    assert len(ledger)==371 and ledger[-1]['unit']=='P3' and ledger[-1]['passed']
    state=json.loads(tar.extractfile('artifacts/research-tests/O6-R205-REBUILD-STATE.json').read())
    for row in state['modules']:assert entries['current-source/'+row['path']]['sha256']==row['sourceSHA256']
manifest_path.write_bytes(manifest_bytes)
write_json(verification_path,dict(timestampUTC=utc(),status='PASS',archive=str(archive.relative_to(ROOT)),archiveSHA256=sha(archive.read_bytes()),archiveBytes=archive.stat().st_size,verifiedMembers=len(entries)+1,rawNativeInvocations=len(ledger),allCurrentSources=543,allMemberHashesVerified=True,noExtraction=True,sourceHashesMatchRebuildState=True,notes='Archive is evidence, not certification of six failed or133 blocked modules. Historical policy reconstruction provenance is included. Final artifact-only receipts after capture are deliberately outside this archive.'))
print(verification_path.read_text())
