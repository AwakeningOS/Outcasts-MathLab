import hashlib
import json
import os
import re
import subprocess
import time
from pathlib import Path

run = Path('/mnt/hdd1t/outcasts-reply-20261010-DnoRad')
repo = Path('/mnt/hdd1t/outcasts-obstruction-review-20261006-D3Hr7e/repo')
toolchain = Path('/mnt/hdd1t/outcasts-replies-20261003-qS7H8a/toolchain/bin')
source = run / 'KneserGap20261010.lean'
head = subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip()
assert head=='fc6ed0305974e2501721aefd73186907ed45d7f6'
env = dict(os.environ)
env['PATH'] = str(toolchain)+':'+env['PATH']
lean_path = subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=repo,env=env,text=True).strip()
env['LEAN_PATH'] = lean_path
version=subprocess.check_output(['lean','--version'],env=env,text=True).strip()
assert '4.34.0' in version
assert not re.search(r'\b(sorry|native_decide|axiom)\b',source.read_text())
start=time.monotonic()
with (run/'KneserGap20261010-lean-v3.log').open('w') as output:
    try:
        result=subprocess.run(['lean','--root='+str(run),'-j','1','-o',str(run/'KneserGap20261010.olean'),str(source)],cwd=repo,env=env,text=True,stdout=output,stderr=subprocess.STDOUT,timeout=60)
    except subprocess.TimeoutExpired:
        (run/'KneserGap20261010-lean-result.json').write_text(json.dumps({'exit_code':None,'timeout_seconds':60,'Lean_verified':False})+'\n')
        raise
log=(run/'KneserGap20261010-lean-v3.log').read_text()
axioms=[]
for name, listed in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log,re.S):
    names=[z.strip() for z in listed.split(',') if z.strip()]
    assert set(names)<={'propext','Classical.choice','Quot.sound'}
    axioms.append({'theorem':name,'axioms':names})
report={'dependency_head':head,'lean_version':version,'source_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),
        'exit_code':result.returncode,'seconds':round(time.monotonic()-start,3),'axioms':axioms,'theorems':len(axioms),
        'full_67_row_negative_Lean_verified':False,'general_Kneser_theorem_Lean_verified':False,
        'prime_input_and_factors_Lean_verified':False,
        'first_attempt':{'timeout_seconds':180,'success':False,'cause_not_isolated':True,'retained_input':'KneserGap20261010-first-attempt.lean'},
        'second_attempt':{'timeout_seconds':60,'success':False,'retained_input':'KneserGap20261010-second-attempt.lean'},
        'selected_numeric_identity_Lean_verified':False,
        'universal_existence_proved':False,'scope':'Selected actual-hit/Kneser-gap pair, new candidate counterexample mechanism; not the full box or general sufficient criterion'}
(run/'KneserGap20261010-lean-result.json').write_text(json.dumps(report,indent=2)+'\n')
print(log)
print(json.dumps(report,indent=2))
assert result.returncode==0 and 'error:' not in log and 'warning:' not in log and len(axioms)==4
