import hashlib
import json
import os
import re
import subprocess
import time
from pathlib import Path

run=Path('/mnt/hdd1t/outcasts-reply-20261015-ACqg3d')
repo=Path('/mnt/hdd1t/outcasts-obstruction-review-20261006-D3Hr7e/repo')
toolchain=Path('/mnt/hdd1t/outcasts-replies-20261003-qS7H8a/toolchain/bin')
env=dict(os.environ,LEAN_NUM_THREADS='1')
env['PATH']=str(toolchain)+':'+env['PATH']
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip()=='fc6ed0305974e2501721aefd73186907ed45d7f6'
env['LEAN_PATH']=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=repo,env=env,text=True).strip()
source=run/'OddSquareLift20261015.lean'
assert not re.search(r'\b(sorry|admit|native_decide)\b',source.read_text())
log=run/'OddSquareLift20261015.log'
version=subprocess.check_output(['lean','--version'],cwd=repo,env=env,text=True).strip()
start=time.monotonic()
with log.open('w') as out:
    proc=subprocess.run(['lean','--root='+str(run),'-j','1','-o',str(run/'OddSquareLift20261015.olean'),str(source)],cwd=repo,env=env,stdout=out,stderr=subprocess.STDOUT,timeout=60)
output=log.read_text()
declarations=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",output)
axioms={name:[v.strip() for v in values.split(',') if v.strip()] for name,values in declarations}
result={'version':version,'threads':1,'exit_code':proc.returncode,'seconds':round(time.monotonic()-start,3),'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'theorems':6,'general_group_theorems':4,'numeric_theorems':2,'axioms':axioms,'standard_axioms_only':len(axioms)==6 and all(set(v)<={'propext','Classical.choice','Quot.sound'} for v in axioms.values()),'scope':'Four abstract commutative-group odd-power lifting statements, including explicit odd subgroup-cardinality premise; two numeric facts. No formal quotient-character identity, square subgroup identification, prime/factor proof, full classification or universal existence.','dependency_head':'fc6ed0305974e2501721aefd73186907ed45d7f6','fresh_full_project_build_or_CI':False}
(run/'square-lean-results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
assert proc.returncode==0 and result['standard_axioms_only'] and 'error:' not in output and 'warning:' not in output,output
