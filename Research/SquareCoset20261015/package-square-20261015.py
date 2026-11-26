import hashlib
import json
import re
from pathlib import Path

run=Path('/mnt/hdd1t/outcasts-reply-20261015-ACqg3d')
rows=json.loads((run/'square-coset-rows.json').read_text())
summary=[{k:v for k,v in r.items() if k not in {'odd_divisors','quotient_counts','residue_counts'}} for r in rows]
assert len(summary)==610
(run/'square-coset-rows-summary.json').write_text(json.dumps(summary,separators=(',',':'))+'\n')
files={'README.md':(run/'square-research-readme-20261015.md').read_text(),'test-kneser-budget-20261010.py':Path('/mnt/hdd1t/outcasts-reply-20261010-DnoRad/test-kneser-budget-20261010.py').read_text(),'character-helper-20261013.py':Path('/mnt/hdd1t/outcasts-reply-20261013-ks9Uhb/check-residual-20261013.py').read_text()}
names=['square-coset-contract-20261015.md','check-square-coset-20261015.py','square-coset-results.json','square-coset-rows-summary.json','analyze-square-support-20261015.py','square-support-results.json','analyze-odd-candidate-20261015.py','odd-candidate-discovery-check.json','verify-odd-counterexample-20261015.py','odd-candidate-counterexample.json','source61-replay.log','OddSquareLift20261015.lean','OddSquareLift20261015.log','run-square-lean-20261015.py','square-lean-results.json','OddSquareLift20261015-first-attempt.lean','OddSquareLift20261015-first-attempt.log','run-square-lean-20261015-first-attempt.py','square-lean-first-attempt.json','package-square-20261015.py']
for name in names:
    content=(run/name).read_text()
    if name.endswith('.json'):content=json.dumps(json.loads(content),ensure_ascii=False,separators=(',',':'))+'\n'
    files[name]=content
assert all(not re.search(r'outcast_sk_[0-9a-f]{64}|Bearer [A-Za-z0-9_-]{24,}',content) for content in files.values())
hashes={name:hashlib.sha256(content.encode()).hexdigest() for name,content in files.items()}
payload_bytes=sum(len(content.encode()) for content in files.values())
files['SHA256SUMS']=''.join(f'{digest}  {name}\n' for name,digest in sorted(hashes.items()))
entries=[{'path':'Research/SquareCoset20261015/'+name,'mode':'100644','type':'blob','content':content} for name,content in sorted(files.items())]
package={'files':len(files),'payload_files':len(files)-1,'payload_bytes':payload_bytes,'hashes':hashes,'entries':entries}
(run/'square-public-package.json').write_text(json.dumps(package,ensure_ascii=False)+'\n')
print(json.dumps({'files':len(files),'payload_files':len(files)-1,'payload_bytes':payload_bytes}))
