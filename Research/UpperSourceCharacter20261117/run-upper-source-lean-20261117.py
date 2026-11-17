import json,os,signal,subprocess,sys,time
from pathlib import Path
run=Path(__file__).resolve().parent
repo=Path('/mnt/hdd1t/outcasts-obstruction-review-20261006-D3Hr7e/repo')
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip()
assert head=='fc6ed0305974e2501721aefd73186907ed45d7f6'
env=dict(os.environ)
env['PATH']='/mnt/hdd1t/outcasts-replies-20261003-qS7H8a/toolchain/bin:'+env['PATH']
env['LEAN_NUM_THREADS']='1'
version=subprocess.check_output(['lean','--version'],cwd=repo,env=env,text=True).strip()
attempt=sys.argv[1]
log=run/f'lean-{attempt}.log'
snapshot=run/f'UpperSourceCharacter20261117-{attempt}.lean'
snapshot.write_bytes((run/'UpperSourceCharacter20261117.lean').read_bytes())
t=time.monotonic()
with log.open('x') as out:
    proc=subprocess.Popen(['lake','env','lean','-j1',str(run/'UpperSourceCharacter20261117.lean')],cwd=repo,env=env,stdout=out,stderr=subprocess.STDOUT,start_new_session=True)
    try: code=proc.wait(timeout=240)
    except subprocess.TimeoutExpired:
        os.killpg(proc.pid,signal.SIGTERM);proc.wait(timeout=10);code=124
res=dict(exit=code,context_head=head,attempt=attempt,log=str(log),version=version,seconds=time.monotonic()-t)
(run/f'lean-status-{attempt}.json').write_text(json.dumps(res,indent=2)+'\n')
print(json.dumps(res));print(log.read_text())
