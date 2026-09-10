#!/usr/bin/env python3
"""L2R16 explicit bounded lexical qualification preparation, no compiler/commit.
One caller-selected consumer and one research namespace; never changes production.
All replacements logged with counts, original validation receipt and exact errors.
"""
from pathlib import Path
import json,re,sys,subprocess
ROOT=Path('/Users/vyacheslavshebanov/Work/dgamma-lane2')
OUT=Path('/tmp/dgamma-l2r16')
unit,path,receipt,namespace,*names=sys.argv[1:]
assert Path.cwd()==ROOT and re.fullmatch(r'R[1-9]\d*',unit)
assert path in (OUT/'TARGETS.txt').read_text().splitlines()
assert not path.startswith('src/') and 'CP5ActorLifecycleOnlyExtended' not in path
assert names and namespace.startswith('DGamma.') and namespace!='DGamma.CP3'
assert (OUT/'QUALIFICATION-RULING.json').exists()
p=ROOT/path;s=p.read_text();old=s
assert 'import '+namespace in s
assert not subprocess.check_output(['git','diff','--',path],text=True)
changes=[]
for n in names:
 assert re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',n)
 assert not re.search(r'^(?:[01] )?'+re.escape(n)+r'\s*:',s,re.M),'Cannot qualify own declaration'
 pat=r'(?<![.\w])'+n+r'\b';count=len(re.findall(pat,s))
 if count:s=re.sub(pat,namespace+'.'+n,s);changes.append({'name':n,'qualified':namespace+'.'+n,'occurrences':count})
assert old!=s
p.write_text(s)
q=OUT/'RECHECK-DECISIONS.json';d=json.loads(q.read_text()) if q.exists() else {}
assert path not in d
r=json.loads((OUT/(receipt+'.json')).read_text());assert r['path']==path and not r['passed']
d[path]={'kind':'lexical','repairUnit':unit,'changes':changes,'originalReceipt':receipt,'exactErrors':r['transcript']}
q.write_text(json.dumps(d,indent=2)+'\n')
print(json.dumps(d[path],indent=2))
