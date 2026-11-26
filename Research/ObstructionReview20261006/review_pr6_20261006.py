import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path

root = Path(sys.argv[1])
repo = root / 'repo'
expected_head = 'fc6ed0305974e2501721aefd73186907ed45d7f6'
toolbin = '/mnt/hdd1t/outcasts-replies-20261003-qS7H8a/toolchain/bin'
packages = Path('/mnt/hdd1t/outcasts-replies-20261003-qS7H8a/repo/.lake/packages')
env = dict(os.environ, PATH=toolbin + ':' + os.environ['PATH'], LEAN_NUM_THREADS='8')

def git(*args):
    return subprocess.check_output(['git', '-C', str(repo), *args], text=True).strip()

if git('rev-parse', 'HEAD') != expected_head:
    raise RuntimeError('PR head changed')
manifest = json.loads((repo / 'lake-manifest.json').read_text())
mathlib = next(x for x in manifest['packages'] if x['name'] == 'mathlib')
actual = subprocess.check_output(['git', '-C', str(packages / 'mathlib'), 'rev-parse', 'HEAD'], text=True).strip()
if actual != mathlib['rev']:
    raise RuntimeError('Dependency source mismatch')
if (repo / '.lake/build').exists():
    raise RuntimeError('Fresh project generated objects expected absent')
repo.joinpath('.lake').mkdir(exist_ok=True)
if not repo.joinpath('.lake/packages').exists():
    repo.joinpath('.lake/packages').symlink_to(packages, target_is_directory=True)
thread = json.loads((root / 'outcasts-thread-20261006.json').read_text())
previous = next(x for x in thread['posts'] if x['post_number'] == 28)
if previous['id'] != '4bd6ae5d-c986-4e98-8ca7-84f5fd645926':
    raise RuntimeError('Baseline id mismatch')
if previous['content_md'] != (root / 'reply-2026-10-05-validation.md').read_text().rstrip('\n'):
    raise RuntimeError('Baseline body mismatch')

sources = sorted(repo.joinpath('OutcastsMathLab/Research').glob('*.lean'))
theorems = []
for path in sources:
    source = path.read_text()
    namespace = re.search(r'^namespace (\S+)', source, re.M).group(1)
    theorems.extend(namespace + '.' + name for name in re.findall(r'^theorem (\S+?)(?:\s|:)', source, re.M))
    if re.search(r'\bnative_decide\b', source):
        raise RuntimeError('Unexpected native_decide')
summary = {
    'head_sha': expected_head,
    'baseline_post_28_exact_submitted_body_match': True,
    'project_generated_objects_initially_absent': True,
    'dependency_objects_reused': True,
    'mathlib_commit': actual,
    'lean_version': subprocess.check_output([toolbin + '/lean', '--version'], text=True).strip(),
    'source_sha256': {str(p.relative_to(repo)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sources},
    'declared_theorems': len(theorems),
    'no_native_decide_in_research_sources': True,
}

def run(name, command, timeout):
    print('START', name, flush=True)
    with root.joinpath(name + '.log').open('w') as log:
        try:
            code = subprocess.run(command, cwd=repo, env=env, stdout=log, stderr=subprocess.STDOUT, timeout=timeout).returncode
        except subprocess.TimeoutExpired:
            code = 124
    summary[name + '_exit'] = code
    root.joinpath('review-summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print('END', name, 'exit', code, flush=True)
    return code

run('policy', [sys.executable, 'scripts/check_policy.py'], 30)
os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:8])
if run('lean-build-retry', [toolbin + '/lake', 'build'], 900) != 0:
    raise SystemExit(1)
audit = root / 'AuditAllAxioms.lean'
audit.write_text('import OutcastsMathLab\n' + '\n'.join('#print axioms ' + x for x in theorems) + '\n')
if run('all-axioms', [toolbin + '/lake', 'env', 'lean', str(audit)], 180) != 0:
    raise SystemExit(1)
axiom_text = root.joinpath('all-axioms.log').read_text()
dependencies = re.findall(r'depends on axioms: \[([^\]]*)\]', axiom_text)
if len(dependencies) != len(theorems):
    raise RuntimeError('Incomplete axiom reports')
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
if any(set(x.strip() for x in row.split(',') if x.strip()) - allowed for row in dependencies):
    raise RuntimeError('Unexpected axiom dependency')
summary['all_theorem_axioms_checked'] = len(dependencies)
summary['axioms_within_standard_set'] = True
root.joinpath('review-summary.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps(summary, indent=2), flush=True)
