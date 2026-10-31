import hashlib
import json
import os
import re
import subprocess
import time
from pathlib import Path

run = Path('/mnt/hdd1t/outcasts-reply-20261009-eTMABt')
head = '4b5a002a02f5dc284681af4418eef73e984194de'
src = run / 'sources' / head
repo = Path('/mnt/hdd1t/outcasts-obstruction-review-20261006-D3Hr7e/repo')
toolchain = Path('/mnt/hdd1t/outcasts-replies-20261003-qS7H8a/toolchain/bin')
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=repo, text=True).strip() == 'fc6ed0305974e2501721aefd73186907ed45d7f6'
assert json.loads((repo / 'lake-manifest.json').read_text()) == json.loads((src / 'lake-manifest.json').read_text())
assert (repo / 'lean-toolchain').read_text() == (src / 'lean-toolchain').read_text()
expected = {'ESReduction': ('048810835c43ff5f01a308701d83f6f7b051fdea', 22), 'ESWitnessTarget': ('5876bb035c20bb80a4f84ee21256b9ce948d9b81', 17), 'ESSmallShifts': ('e87ff497eab487097ff57888121aca192d77bd7d', 18)}
env = dict(os.environ)
env['PATH'] = str(toolchain) + ':' + env['PATH']
env['LEAN_NUM_THREADS'] = '1'
env['LEAN_PATH'] = str(src) + ':' + subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=repo, env=env, text=True).strip()
version = subprocess.check_output(['lean', '--version'], cwd=repo, env=env, text=True).strip()
prior_failures = [
    {'stage': 'first invocation', 'cause': 'Explicit --root omitted for external source; Lean rejected before elaboration', 'log': str(run / 'ESReduction-lean.log')},
    {'stage': 'second harness', 'cause': 'ESReduction passed 22 theorems; the one-line axioms parser could not read wrapped output', 'log': str(run / 'ESReduction-lean-v2.log')},
]
results = []
for name, (blob_sha, count) in expected.items():
    path = src / 'OutcastsMathLab' / 'Research' / (name + '.lean')
    raw = path.read_bytes()
    assert hashlib.sha1(f'blob {len(raw)}\0'.encode() + raw).hexdigest() == blob_sha
    text = raw.decode()
    assert len(re.findall(r'^theorem\s+', text, flags=re.M)) == count
    assert len(re.findall(r'^#print axioms ', text, flags=re.M)) == count
    assert not re.search(r'\b(sorry|admit|native_decide|axiom)\b', '\n'.join(line for line in text.splitlines() if not line.startswith('#print axioms')))
    log = run / (name + '-lean-v3.log')
    start = time.monotonic()
    with log.open('w') as stream:
        result = subprocess.run(['lean', '--root=' + str(src), '-j', '1', '-o', str(path.with_suffix('.olean')), str(path)], cwd=repo, env=env, stdout=stream, stderr=subprocess.STDOUT, timeout=180)
    output = log.read_text()
    entry = {'module': name, 'exit_code': result.returncode, 'theorem_count': count, 'seconds': round(time.monotonic() - start, 2), 'source_sha256': hashlib.sha256(raw).hexdigest(), 'log': str(log)}
    results.append(entry)
    (run / 'pr7-lean-review.json').write_text(json.dumps({'head': head, 'lean_version': version, 'results': results}, indent=2) + '\n')
    print(json.dumps(entry), flush=True)
    assert result.returncode == 0, output
    assert 'warning:' not in output and 'error:' not in output
    declarations = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", output)
    assert len(declarations) == count
    for declaration, axioms in declarations:
        assert set(a.strip() for a in axioms.split(',') if a.strip()) <= {'propext', 'Classical.choice', 'Quot.sound'}
    entry['theorem_axioms'] = {decl: [a.strip() for a in axioms.split(',') if a.strip()] for decl, axioms in declarations}
    print(output, flush=True)
record = {'head': head, 'dependency_head': 'fc6ed0305974e2501721aefd73186907ed45d7f6', 'lean_version': version, 'dependency_manifests_exactly_equal': True, 'compiled_modules': 3, 'passed_theorems': 57, 'all_axioms_standard_subset': True, 'new_full_lake_build': False, 'source_modules_recompiled_into_new_directory': True, 'failed_harness_attempts': prior_failures, 'results': results}
(run / 'pr7-lean-review.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps({k: v for k, v in record.items() if k != 'results'}), flush=True)
