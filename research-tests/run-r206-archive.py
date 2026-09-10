#!/usr/bin/env python3
"""Curated immutable evidence archive; excludes drafts and unused candidate files."""
import sys,pathlib,json,tarfile,io
sys.dont_write_bytecode=True
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from r206_common import ROOT,OUT,sha,write_json,utc
rs=[json.loads(x) for x in (OUT/'ledger.jsonl').read_text().splitlines()]
files={}
for r in rs:
    for suffix in ['.json','.log','.source','.runner.py','.common.py','.sources.json','.launch.log']:
        p=OUT/(r['unit']+suffix)
        if p.exists():files['native/'+p.name]=p.read_bytes()
for name in ['ledger.jsonl','commit-receipts.jsonl','evidence-tests.log','support-before-package.json','toolchain-version.txt']:
    files['meta/'+name]=(OUT/name).read_bytes()
for p in OUT.glob('*-closure*.json'):files['closure/'+p.name]=p.read_bytes()
for p in OUT.glob('commit-receipts.jsonl'):assert p.exists()
for p in sorted((ROOT/'research-tests').glob('*r206*.py')):files['tools/'+p.name]=p.read_bytes()
for name in ['r205_common.py','O6-R205-POST-FROZEN-BASELINE.json','O6-R206-SEMANTIC-GATE.md','O6-R206-VISIBILITY.json','O6-R206-O19-EXPANSION-DESIGN.md']:
    files['context/'+name]=(ROOT/'research-tests'/name).read_bytes()
archive=ROOT/'research-tests/O6-R206-EVIDENCE.tar.gz'
with tarfile.open(archive,'w:gz') as tf:
    for name,data in sorted(files.items()):
        entry=tarfile.TarInfo(name);entry.size=len(data);entry.mtime=0;entry.mode=0o644
        tf.addfile(entry,io.BytesIO(data))
write_json(ROOT/'research-tests/O6-R206-ARCHIVE-MANIFEST.json',dict(timestampUTC=utc(),archiveSHA256=sha(archive.read_bytes()),nativeReceipts=len(rs),members={p:sha(b) for p,b in sorted(files.items())},qualification='Native receipts include unsuccessful attempts. Drafts are excluded. Commit receipts stop before the artifact/seal commit that stores this archive.'))
print('archive',len(files),'members',archive.stat().st_size,'bytes',sha(archive.read_bytes()))
