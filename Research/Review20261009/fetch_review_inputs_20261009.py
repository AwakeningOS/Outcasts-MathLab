import hashlib
import json
import urllib.request
from pathlib import Path

run = Path('/mnt/hdd1t/outcasts-reply-20261009-eTMABt')
repo = 'betyourluck/Outcasts-MathLab'
head = '4b5a002a02f5dc284681af4418eef73e984194de'
sources = [(head, p) for p in [
    'OutcastsMathLab/Research/ESReduction.lean',
    'OutcastsMathLab/Research/ESWitnessTarget.lean',
    'OutcastsMathLab/Research/ESSmallShifts.lean',
    'OutcastsMathLab.lean', 'Research/ESReduction/README.md',
    'lean-toolchain', 'lake-manifest.json', 'lakefile.toml',
]]
sources += [('3c6061ab4740c223cdb21847efdfe7a3206e1b6e', 'Research/Stratified20261008/' + p) for p in [
    'README.md', 'contract.md', 'SHA256SUMS', 'stratified_results.json', 'stratified_test.py',
]]
sources += [
    ('54316da2a0e5df3b1163eb9a32934c4ba0dd1e0a', 'Research/WitnessProgram20261008/README.md'),
    ('2fa24e490ee9cac65cdd4622c65fa41ada6ecae0', 'Research/JointFailure20261008/joint_test.py'),
]
manifest = []
for commit, path in sources:
    url = f'https://raw.githubusercontent.com/{repo}/{commit}/{path}'
    with urllib.request.urlopen(url, timeout=30) as response:
        raw = response.read()
    target = run / 'sources' / commit / path
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(raw)
    manifest.append({'commit': commit, 'path': path, 'url': url, 'file': str(target.relative_to(run)), 'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest(), 'git_blob_sha1': hashlib.sha1(f'blob {len(raw)}\0'.encode() + raw).hexdigest()})
(run / 'source-manifest.json').write_text(json.dumps({'repository': repo, 'files': manifest}, indent=2) + '\n')
print(json.dumps({'files_downloaded': len(manifest), 'PR7_head': head, 'manifest': str(run / 'source-manifest.json')}, indent=2))
