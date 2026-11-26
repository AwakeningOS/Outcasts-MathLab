import hashlib
import json
import os
import re
import subprocess
import time
from pathlib import Path

run = Path('/mnt/hdd1t/outcasts-reply-20261014-Dgn34n')
repo = Path('/mnt/hdd1t/outcasts-obstruction-review-20261006-D3Hr7e/repo')
toolchain = Path('/mnt/hdd1t/outcasts-replies-20261003-qS7H8a/toolchain/bin')
env = dict(os.environ, LEAN_NUM_THREADS='1')
env['PATH'] = str(toolchain) + ':' + env['PATH']
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=repo, text=True).strip() == 'fc6ed0305974e2501721aefd73186907ed45d7f6'
version = subprocess.check_output(['lean', '--version'], cwd=repo, env=env, text=True).strip()
env['LEAN_PATH'] = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=repo, env=env, text=True).strip()
source = run / 'CertificateSlack20261014.lean'
assert not re.search(r'\b(sorry|admit|native_decide)\b', source.read_text())
log = run / 'CertificateSlack20261014.log'
start = time.monotonic()
with log.open('w') as output:
    process = subprocess.run(['lean', '--root=' + str(run), '-j', '1', '-o', str(run / 'CertificateSlack20261014.olean'), str(source)], cwd=repo, env=env, stdout=output, stderr=subprocess.STDOUT, timeout=60)
text = log.read_text()
declarations = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", text)
axioms = {name: [item.strip() for item in values.split(',') if item.strip()] for name, values in declarations}
result = {'version': version, 'threads': 1, 'exit_code': process.returncode, 'seconds': round(time.monotonic() - start, 3), 'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(), 'selected_theorems': 6, 'axioms': axioms, 'standard_axioms_only': len(axioms) == 6 and all(set(values) <= {'propext', 'Classical.choice', 'Quot.sound'} for values in axioms.values()), 'dependency_head': 'fc6ed0305974e2501721aefd73186907ed45d7f6', 'scope': 'Rational min/max identities and conditional compatibility, no formalization of characters, Ramanujan traces, prime/factors, box completeness or universal existence', 'fresh_full_project_build_or_CI': False}
(run / 'slack-lean-results.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result))
assert process.returncode == 0 and result['standard_axioms_only'] and 'error:' not in text and 'warning:' not in text, text
