"""Read-only macOS memory-pressure sampling for owner-gated final S31-3 only."""
import datetime,re,subprocess

def parse_vm_stat(text):
    page_size=int(re.search(r'page size of (\d+) bytes',text)[1])
    def count(label):return int(re.search(r'^'+re.escape(label)+r':\s+(\d+)\.',text,re.M)[1])
    return dict(pageSizeBytes=page_size,swapouts=count('Swapouts'),compressorPages=count('Pages occupied by compressor'),storedCompressorPages=count('Pages stored in compressor'))

def steady_growth(samples):
    """Three consecutive positive deltas (four snapshots), not old totals."""
    if len(samples)<4:return False
    recent=samples[-4:]
    return any(all(b[field]>a[field] for a,b in zip(recent,recent[1:])) for field in ['swapouts','compressorPages'])

def free_percent(text):
    return int(re.search(r'System-wide memory free percentage:\s*(\d+)%',text)[1])

def corrected_pressure_stop(samples):
    low_free=len(samples)>=2 and all(s['freePercent']<15 for s in samples[-2:])
    swaps=len(samples)>=4 and all(b['swapouts']>a['swapouts'] for a,b in zip(samples[-4:],samples[-3:]))
    return low_free or swaps

def sample_pressure():
    vm=subprocess.check_output(['vm_stat'],text=True,timeout=5)
    # -Q is QUERY ONLY. Never run memory_pressure's synthetic allocation mode.
    pressure=subprocess.check_output(['memory_pressure','-Q'],text=True,timeout=5)
    return dict(timestampUTC=datetime.datetime.now(datetime.timezone.utc).isoformat(),**parse_vm_stat(vm),freePercent=free_percent(pressure),vmStatRaw=vm,memoryPressureQueryRaw=pressure)
