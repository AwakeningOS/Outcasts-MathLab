import hashlib
import json
import os
import re
import subprocess
import time
from pathlib import Path

run = Path('/mnt/hdd1t/outcasts-reply-20261011-xanKS3')
repo = Path('/mnt/hdd1t/outcasts-obstruction-review-20261006-D3Hr7e/repo')
binpath = Path('/mnt/hdd1t/outcasts-replies-20261003-qS7H8a/toolchain/bin')
env = dict(os.environ, LEAN_NUM_THREADS='1')
env['PATH'] = str(binpath)+':'+env['PATH']
previous = json.loads((run/'lean-review-results.json').read_text())
assert [r['exit_code'] for r in previous['results']] == [0,0,0,'timeout']
(run/'lean-review-first-attempt.json').write_text(json.dumps(previous,indent=2)+'\n')
dependencies = subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=repo,env=env,text=True).strip()
src = run/'pr6'
env['LEAN_PATH'] = str(src)+':'+dependencies
path = src/'OutcastsMathLab/Research/JacobiObstruction.lean'
assert hashlib.sha256(path.read_bytes()).hexdigest() == previous['results'][-1]['source_sha256']
log = run/'JacobiObstruction-lean-review-retry.log'
start = time.monotonic()
try:
    with log.open('w') as stream:
        p = subprocess.run(['lean','--root='+str(src),'-j','1','-o',str(path.with_suffix('.olean')),str(path)],cwd=repo,env=env,stdout=stream,stderr=subprocess.STDOUT,timeout=180)
    code = p.returncode
except subprocess.TimeoutExpired:
    code = 'timeout'
out = log.read_text()
decl = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",out)
item = dict(previous['results'][-1],exit_code=code,seconds=round(time.monotonic()-start,3),log=str(log),axioms={d:[a.strip() for a in ax.split(',') if a.strip()] for d,ax in decl})
record = dict(previous,pr7_head='fd7b0724602a8fff96d3c182f67f4018512b0d26',pr6_head='b7a27ee156dcff9d4009d5f68ce102772aa7157a',dependency_head='fc6ed0305974e2501721aefd73186907ed45d7f6',dependency_manifests_exactly_equal=True,full_project_fresh_build=False,first_attempt_retained=True,results=previous['results'][:-1]+[item])
record['all_exits_zero'] = all(r['exit_code']==0 for r in record['results'])
record['theorems_checked'] = sum(r['theorems'] for r in record['results'] if r['exit_code']==0)
record['all_axioms_standard_subset'] = all(len(r['axioms'])==r['theorems'] and all(set(ax)<={'propext','Classical.choice','Quot.sound'} for ax in r['axioms'].values()) for r in record['results'])
(run/'lean-review-results.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items() if k!='results'}),flush=True)
assert code==0 and len(decl)==12 and 'warning:' not in out and 'error:' not in out and record['all_axioms_standard_subset'], out
