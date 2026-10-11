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
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip() == 'fc6ed0305974e2501721aefd73186907ed45d7f6'
env = dict(os.environ)
env['PATH'] = str(binpath) + ':' + env['PATH']
env['LEAN_NUM_THREADS'] = '1'
dependencies = subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=repo,env=env,text=True).strip()
version = subprocess.check_output(['lean','--version'],cwd=repo,env=env,text=True).strip()
for pr in ('pr6','pr7'):
    assert json.loads((run/pr/'lake-manifest.json').read_text()) == json.loads((repo/'lake-manifest.json').read_text())
    assert (run/pr/'lean-toolchain').read_text() == (repo/'lean-toolchain').read_text()
modules = [('pr7','ESReduction',22),('pr7','ESWitnessTarget',26),('pr7','ESSmallShifts',26),('pr6','JacobiObstruction',12)]
results = []
for pr,name,count in modules:
    src = run/pr
    path = src/'OutcastsMathLab'/'Research'/(name+'.lean')
    raw = path.read_bytes()
    text = raw.decode()
    assert len(re.findall(r'^theorem\s+',text,re.M)) == count
    assert len(re.findall(r'^#print axioms ',text,re.M)) == count
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b','\n'.join(line for line in text.splitlines() if not line.startswith('#print axioms')))
    env['LEAN_PATH'] = str(src) + ':' + dependencies
    log = run/(name+'-lean-review.log')
    start = time.monotonic()
    try:
        with log.open('w') as stream:
            p = subprocess.run(['lean','--root='+str(src),'-j','1','-o',str(path.with_suffix('.olean')),str(path)],cwd=repo,env=env,stdout=stream,stderr=subprocess.STDOUT,timeout=180)
        exit_code = p.returncode
    except subprocess.TimeoutExpired:
        exit_code = 'timeout'
    output = log.read_text()
    item = {'pr':pr,'module':name,'exit_code':exit_code,'seconds':round(time.monotonic()-start,3),'theorems':count,'source_sha256':hashlib.sha256(raw).hexdigest(),'log':str(log)}
    declarations = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",output)
    item['axioms'] = {decl:[a.strip() for a in axioms.split(',') if a.strip()] for decl,axioms in declarations}
    results.append(item)
    (run/'lean-review-results.json').write_text(json.dumps({'lean_version':version,'results':results},indent=2)+'\n')
    print(json.dumps({k:v for k,v in item.items() if k!='axioms'}),flush=True)
    assert exit_code == 0, output
    assert 'warning:' not in output and 'error:' not in output
    assert len(declarations) == count
    assert all(set(ax) <= {'propext','Classical.choice','Quot.sound'} for ax in item['axioms'].values())
record = {'pr7_head':'fd7b0724602a8fff96d3c182f67f4018512b0d26','pr6_head':'b7a27ee156dcff9d4009d5f68ce102772aa7157a','dependency_head':'fc6ed0305974e2501721aefd73186907ed45d7f6','dependency_manifests_exactly_equal':True,'lean_version':version,'modules_recompiled':4,'theorems_checked':86,'all_exits_zero':True,'all_axioms_standard_subset':True,'full_project_fresh_build':False,'results':results}
(run/'lean-review-results.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items() if k!='results'}),flush=True)
