"""R207 main-lane frozen authentication and immutable evidence helpers."""
import datetime, hashlib, json, pathlib, re, subprocess, sys
sys.dont_write_bytecode = True
ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = pathlib.Path('/tmp/dgamma-r207')
START = 'fec9525287d83303aba90efe95829da5993299ac'
sys.path.insert(0, str(ROOT/'research-tests'))
from r205_common import frozen, compiler_scopes, PROTECTED_PATHS

def utc(): return datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(data): return hashlib.sha256(data).hexdigest()
def git(*args): return subprocess.check_output(['git', *args], cwd=ROOT, text=True)
def write_json(path, value):
    path = pathlib.Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    temp = path.with_suffix(path.suffix+'.tmp')
    temp.write_text(json.dumps(value, indent=2, ensure_ascii=False)+'\n')
    temp.replace(path)
def records():
    p = OUT/'ledger.jsonl'
    return [json.loads(s) for s in p.read_text().splitlines()] if p.exists() else []
def source_paths():
    return sorted(p for p in git('ls-files','src/','research/','research-tests/').splitlines()
                  if p.endswith('.idr') and (ROOT/p).exists())
def assert_frozen():
    expected = json.loads((ROOT/'research-tests/O6-R205-POST-FROZEN-BASELINE.json').read_text())['frozen']
    assert frozen() == expected, 'Frozen source/region/declaration differs from post-unfreeze baseline'
    assert not git('diff', START, '--', 'src/', 'dgamma.ipkg'), 'Production must remain byte-identical tofec95252'
    assert git('hash-object','src/DGamma/CP3.idr').strip() == 'eeaa70aa4414648bb2a1173d58244267997d16d7'
