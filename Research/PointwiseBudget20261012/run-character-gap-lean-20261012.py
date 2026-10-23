import hashlib
import json
import os
import re
import subprocess
import time
from pathlib import Path
run=Path('/mnt/hdd1t/outcasts-reply-20261012-ZXux6H')
repo=Path('/mnt/hdd1t/outcasts-obstruction-review-20261006-D3Hr7e/repo')
binpath=Path('/mnt/hdd1t/outcasts-replies-20261003-qS7H8a/toolchain/bin')
env=dict(os.environ,LEAN_NUM_THREADS='1')
env['PATH']=str(binpath)+':'+env['PATH']
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip()=='fc6ed0305974e2501721aefd73186907ed45d7f6'
version=subprocess.check_output(['lean','--version'],cwd=repo,env=env,text=True).strip()
env['LEAN_PATH']=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=repo,env=env,text=True).strip()
src=run/'CharacterGap20261012.lean'
assert not re.search(r'\b(sorry|admit|native_decide)\b',src.read_text())
log=run/'CharacterGap20261012.log'
start=time.monotonic()
try:
    with log.open('w') as stream:
        p=subprocess.run(['lean','--root='+str(run),'-j','1','-o',str(run/'CharacterGap20261012.olean'),str(src)],cwd=repo,env=env,stdout=stream,stderr=subprocess.STDOUT,timeout=180)
    code=p.returncode
except subprocess.TimeoutExpired:
    code='timeout'
out=log.read_text()
decl=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",out)
axioms={name:[a.strip() for a in ax.split(',') if a.strip()] for name,ax in decl}
record={'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'lean_version':version,'threads':1,'exit_code':code,'seconds':round(time.monotonic()-start,3),'selected_numeric_theorems':5,'axioms':axioms,'standard_axioms_only':len(axioms)==5 and all(set(ax)<={'propext','Classical.choice','Quot.sound'} for ax in axioms.values()),'dependency_head':'fc6ed0305974e2501721aefd73186907ed45d7f6','general_character_theorem_or_prime_existence_formalized':False,'full_project_build':False}
(run/'character-gap-lean-results.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record),flush=True)
assert code==0 and len(axioms)==5 and record['standard_axioms_only'] and 'error:' not in out and 'warning:' not in out,out
