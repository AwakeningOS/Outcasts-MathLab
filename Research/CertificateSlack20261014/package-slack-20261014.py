import hashlib
import json
import re
from fractions import Fraction as Q
from pathlib import Path

run = Path('/mnt/hdd1t/outcasts-reply-20261014-Dgn34n')
previous = Path('/mnt/hdd1t/outcasts-reply-20261013-ks9Uhb')
participant = json.loads((run / 'participant-source-20261014.json').read_text())
mine = json.loads((previous / 'residual-audit-rows.json').read_text())
mine.append(json.loads((previous / 'residual-audit-results.json').read_text())['sharpness_pair'])
their = json.loads(participant['files']['check57_rows.json'])
mapping = {'U': 'U', 't': 't', 'V': 'V', 'W': 'W', 'rest': 'r', 'delta': 'delta', 'factor_only_K': 'K', 'factor_only_W_lower': 'lower', 'other_even_real': 'A', 'other_odd_real': 'B', 'signed_complex': 'C'}
indexed = {(r['p'], r['a'], r['u']): r for r in their}
assert len(mine) == len(their) == 113
for r in mine:
    partner = indexed[r['p'], r['a'], r['u']]
    assert all(Q(r[k]) == Q(partner[v]) for k, v in mapping.items())
audit = {'source_sha': participant['sha'], 'text_files_including_manifest': 11, 'payload_hashes_matched': 10, 'rows_compared': 113, 'fields_per_row': 11, 'all113_rows_match': True, 'axiom_log_byte_match': participant['files']['lean/ResidualAccounting20261013.luna.log'] == (previous / 'ResidualAccounting20261013.log').read_text(), 'participant_scripts_executed': False, 'participant_independent_execution_or_timing_reproduced': False, 'full_cohort_or_MC_replayed': False}
(run / 'participant-audit-20261014.json').write_text(json.dumps(audit, indent=2) + '\n')
rows = json.loads((run / 'slack-certificate-rows.json').read_text())
summary_rows = [{k: v for k, v in r.items() if k not in {'complex_pairs', 'real_terms'}} for r in rows]
assert len(summary_rows) == 498
(run / 'slack-certificate-rows-summary.json').write_text(json.dumps(summary_rows, separators=(',', ':')) + '\n')
selected = [r for r in rows if (r['p'], r['a'], r['u']) == (84525841, 1, 19)]
(run / 'selected-full-row.json').write_text(json.dumps(selected, separators=(',', ':')) + '\n')
files = {'README.md': (run / 'slack-research-readme-20261014.md').read_text(), 'character-helper-20261013.py': (previous / 'check-residual-20261013.py').read_text(), 'test-kneser-budget-20261010.py': Path('/mnt/hdd1t/outcasts-reply-20261010-DnoRad/test-kneser-budget-20261010.py').read_text()}
names = ['slack-certificate-contract-20261014.md', 'check-slack-certificate-20261014.py', 'slack-certificate-results.json', 'slack-certificate-rows-summary.json', 'selected-full-row.json', 'participant-audit-20261014.json', 'CertificateSlack20261014.lean', 'CertificateSlack20261014.log', 'run-slack-lean-20261014.py', 'slack-lean-results.json', 'package-slack-20261014.py']
for name in names:
    content = (run / name).read_text()
    if name.endswith('.json'):
        content = json.dumps(json.loads(content), ensure_ascii=False, separators=(',', ':')) + '\n'
    files[name] = content
assert all(not re.search(r'outcast_sk_[0-9a-f]{64}|Bearer [A-Za-z0-9_-]{24,}', c) for c in files.values())
hashes = {name: hashlib.sha256(content.encode()).hexdigest() for name, content in files.items()}
payload_bytes = sum(len(content.encode()) for content in files.values())
files['SHA256SUMS'] = ''.join(f'{digest}  {name}\n' for name, digest in sorted(hashes.items()))
entries = [{'path': 'Research/CertificateSlack20261014/' + name, 'mode': '100644', 'type': 'blob', 'content': content} for name, content in sorted(files.items())]
package = {'files': len(files), 'payload_files': len(files) - 1, 'payload_bytes': payload_bytes, 'hashes': hashes, 'entries': entries}
(run / 'slack-public-package.json').write_text(json.dumps(package, ensure_ascii=False) + '\n')
print(json.dumps({'files': len(files), 'payload_files': len(files) - 1, 'payload_bytes': payload_bytes, 'participant_audit': audit}))
