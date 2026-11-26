import json
import os
import subprocess
from pathlib import Path

run = Path('/mnt/hdd1t/outcasts-reply-20261007-3GsS6S')
repo = Path('/mnt/hdd1t/outcasts-obstruction-review-20261006-D3Hr7e/repo')
head = subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip()
if head != 'fc6ed0305974e2501721aefd73186907ed45d7f6':
    raise ValueError('context head changed')
env = dict(os.environ)
env['PATH'] = '/mnt/hdd1t/outcasts-replies-20261003-qS7H8a/toolchain/bin:' + env['PATH']
env['LEAN_NUM_THREADS'] = '1'
name = os.environ.get('OUTCASTS_LOG_NAME','lean-reply-initial.log')
with (run/name).open('w') as out:
    result = subprocess.run(['lake','env','lean',str(run/'Reply20261007.lean')],cwd=repo,
       env=env,stdout=out,stderr=subprocess.STDOUT,timeout=90)
lines = (run/name).read_text()
print(json.dumps({'exit':result.returncode,'context_head':head,'log':str(run/name)}))
print(lines)
