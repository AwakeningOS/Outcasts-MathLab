import hashlib
import json
import os
import re
import subprocess
import time
from pathlib import Path
run=Path('/mnt/hdd1t/outcasts-reply-20261013-ks9Uhb')
repo=Path('/mnt/hdd1t/outcasts-obstruction-review-20261006-D3Hr7e/repo')
binpath=Path('/mnt/hdd1t/outcasts-replies-20261003-qS7H8a/toolchain/bin')
env=dict(os.environ,LEAN_NUM_THREADS='1'); env['PATH']=str(binpath)+':'+env['PATH']
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip()=='fc6ed0305974e2501721aefd73186907ed45d7f6'
version=subprocess.check_output(['lean','--version'],cwd=repo,env=env,text=True).strip()
env['LEAN_PATH']=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=repo,env=env,text=True).strip()
src=run/'ResidualAccounting20261013.lean'
assert not re.search(r'\b(sorry|admit|native_decide)\b',src.read_text())
log=run/'ResidualAccounting20261013.log'; start=time.monotonic()
try:
    with log.open('w') as out:
        p=subprocess.run(['lean','--root='+str(run),'-j','1','-o',str(run/'ResidualAccounting20261013.olean'),str(src)],cwd=repo,env=env,stdout=out,stderr=subprocess.STDOUT,timeout=60)
    code=p.returncode
except subprocess.TimeoutExpired: code='timeout'
out=log.read_text()
decl=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",out)
axioms={n:[a.strip() for a in ax.split(',') if a.strip()] for n,ax in decl}
record={'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'lean_version':version,'threads':1,'exit_code':code,'seconds':round(time.monotonic()-start,3),'selected_theorems':10,'generic_algebra_theorems':6,'scalar_or_box_numeric_theorems':4,'axioms':axioms,'standard_axioms_only':len(axioms)==10 and all(set(ax)<={'propext','Classical.choice','Quot.sound'} for ax in axioms.values()),'dependency_head':'fc6ed0305974e2501721aefd73186907ed45d7f6','finite_character_certificate_formula_or_factors_formalized':False,'full_project_build':False,'universal_existence_formalized':False}
(run/'residual-lean-results.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record),flush=True)
assert code==0 and len(axioms)==10 and record['standard_axioms_only'] and 'error:' not in out and 'warning:' not in out,out
