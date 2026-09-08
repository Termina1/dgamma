#!/usr/bin/env python3
"""Compiler-free source-derived old/new location and byte identity map."""
import datetime
import hashlib
import json
import pathlib
import re
import subprocess
import sys
ROOT=pathlib.Path(__file__).resolve().parents[1]
CROSS='research/DGamma/CP5ConfluenceCrossTraceSpike.idr'
LOWER='research/DGamma/CP5O19SurfaceSpike.idr'
old=subprocess.check_output(['git','show','8e133ed5:'+CROSS],cwd=ROOT,text=True)
new=(ROOT/CROSS).read_text()
lower=(ROOT/LOWER).read_text()
pattern=r'(?m)^(?:\|\|\|[^\n]*\n)*(?:(?:public export|export|private)\n)?(?=(?:record|data) |(?:[01] )?\w+[ \t]*:)(?:[01] )?(?:(?:record|data) )?([A-Za-z_]\w*)'
def spans(text):
    matches=list(re.finditer(pattern,text))
    return {m[1]:(m.start(),matches[i+1].start() if i+1<len(matches) else len(text)) for i,m in enumerate(matches)}
def sha(text):
    return hashlib.sha256(text.encode()).hexdigest()
a,b=spans(old),spans(lower)
names=list(b)
assert len(names)==32
rows=[]
for name in names:
    oldText=old[slice(*a[name])].rstrip('\n')+'\n'
    newText=lower[slice(*b[name])].rstrip('\n')+'\n'
    assert oldText==newText,name
    oldLine=old[:a[name][0]].count('\n')+1
    newLine=lower[:b[name][0]].count('\n')+1
    count=oldText.count('\n')
    definition=re.search(r'(?m)^(?:[01] )?(?:(?:record|data) )?'+re.escape(name)+r'\s*[:\n (]',oldText)
    assert definition
    signatureOffset=oldText[:definition.start()].count('\n')
    rows.append(dict(declaration=name,oldFile=CROSS,newFile=LOWER,oldRange=[oldLine,oldLine+count-1],newRange=[newLine,newLine+count-1],lineDelta=newLine-oldLine,oldSignatureLine=oldLine+signatureOffset,newSignatureLine=newLine+signatureOffset,definitionSHA256=sha(oldText),definitionBytes=len(oldText.encode()),byteIdentical=True))
protected=[]
for name in ['operationalAdjacentBlockSwapSpike','selectOperationalCanonicalPermutationSpike','canonicalSchedulesConvergeSpike']:
    marker='0 '+name+' :'
    oldStart=old.index(marker);newStart=new.index(marker)
    oldEnd=old.index('\n'+name+' ',oldStart);newEnd=new.index('\n'+name+' ',newStart)
    assert old[oldStart:oldEnd]==new[newStart:newEnd],name
    protected.append(dict(declaration=name,oldSignatureLine=old[:oldStart].count('\n')+1,newSignatureLine=new[:newStart].count('\n')+1,oldBodyLine=old[:oldEnd].count('\n')+2,newBodyLine=new[:newEnd].count('\n')+2,signatureSHA256=sha(old[oldStart:oldEnd]),signatureUnchanged=True))
report=dict(generatedUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),startCommit='8e133ed5',endCommit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),moves=rows,protected=protected,separatorQualification='All declaration text/comment/fields/body bytes identical; inter-declaration blank separators excluded from each hash. Exactly one surplus final LF was removed under W1 explicit supervisor gate. Extra five declarations inserted ahead of the stable final projection without another EOF edit.')
print(json.dumps(report,indent=2))
