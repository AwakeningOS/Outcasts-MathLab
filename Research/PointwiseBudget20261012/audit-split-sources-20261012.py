import hashlib
import json
import math
from pathlib import Path
run=Path('/mnt/hdd1t/outcasts-reply-20261012-ZXux6H')
sources=json.loads((run/'split-error-sources-20261012.json').read_text())
root=run/'participant-split-error'
root.mkdir(exist_ok=True)
allowed={'README.md','SHA256SUMS','contract.md','run.log','split_error_results.json','split_error_test.py'}
assert {r['name'] for r in sources}==allowed
for r in sources:
    (root/r['name']).write_text(r['content'])
hashes=[]
for line in (root/'SHA256SUMS').read_text().splitlines():
    digest,name=line.split(maxsplit=1)
    name=name.removeprefix('*')
    assert name in allowed and hashlib.sha256((root/name).read_bytes()).hexdigest()==digest
    hashes.append({'name':name,'sha256':digest})
result=json.loads((root/'split_error_results.json').read_text())
p_low=result['V3_two_stage_bootstrap']['T2']['p_low']
reps=result['V3_two_stage_bootstrap']['reps']
se_two=2*math.sqrt(p_low*(1-p_low)/reps)
record={'source_commit':'ad0f8b67d2ad043618a4184d9f831999ee02c721','source_files_downloaded':6,'checksums_matched':len(hashes),'hashes':hashes,'script_and_contract_read':True,'full_V0_V2_V3_replayed':False,'source_generation_truth_fixed_at_original_fit':True,'source_test_center_reestimated_each_resample':True,'T2_two_sided_p_reported':result['V3_two_stage_bootstrap']['T2']['p_two_sided'],'T2_two_sided_p_MC_SE_approx':se_two,'T2_single_tail_p_MC_SE_approx':se_two/2,'note':'The approx0.004 is for one tail, not the doubled two-sided p; this does not change the non-rejection verdict. Initial checksum parser stopped on the standard binary-marker asterisk; parsing corrected, expected digests unchanged.'}
(run/'split-source-audit.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record))
