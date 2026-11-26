import hashlib
import importlib.util
import json
from fractions import Fraction as Q
from pathlib import Path
run=Path('/mnt/hdd1t/outcasts-reply-20261013-ks9Uhb')
helper=Path('/mnt/hdd1t/outcasts-reply-20261010-DnoRad/test-kneser-budget-20261010.py')
spec=importlib.util.spec_from_file_location('grouphelper',helper)
old=importlib.util.module_from_spec(spec); spec.loader.exec_module(old)
bundle=json.loads((run/'mainterm-sources-20261013.json').read_text())
files={r['name']:r['content'] for r in bundle['files']}
manifest={}
for line in files['SHA256SUMS'].splitlines():
    h,n=line.split(maxsplit=1); manifest[n.lstrip('*')]=h
verified=[]
source_dir=run/'participant-source'; source_dir.mkdir(exist_ok=True)
for n,c in files.items():
    (source_dir/n).write_text(c)
    if n!='SHA256SUMS':
        actual=hashlib.sha256(c.encode()).hexdigest()
        assert actual==manifest[n]
        verified.append({'name':n,'sha256':actual})
source_audit={'commit':bundle['commit'],'fetched_files':len(files),'payload_hashes_matched':len(verified),'matched':verified,'binary_or_unfetched_manifest_entries_verified':False,'full_cohort_or_K_statistics_replayed':False}
(run/'participant-source-audit.json').write_text(json.dumps(source_audit,indent=2)+'\n')
rows=json.loads((run/'residual-audit-rows.json').read_text())
results=json.loads((run/'residual-audit-results.json').read_text())
selection=[]
for p in [66529,18490201]:
    cohort=[r for r in rows if r['p']==p]
    worst=max(cohort,key=lambda r:Q(r['rest']))
    worst['generated_unit_group']=sorted(old.generated([q%worst['m'] for q,e in worst['factors'] if q!=2],worst['m']))
    worst['actual_unit_divisor_residues']=sorted({d%worst['m'] for d in old.divisors(worst['factors']) if __import__('math').gcd(d,worst['m'])==1})
    delta=[r for r in cohort if Q(r['delta'])>0]
    complex_adverse=[r for r in cohort if Q(r['rest'])>0 and Q(r['signed_complex'])<0]
    complex_adverse.sort(key=lambda r:Q(r['signed_complex']))
    selection.append({'p':p,'maximum_rest_row':worst,'nonzero_delta_rows':delta,'most_negative_complex_row_with_residual':complex_adverse[0] if complex_adverse else None})
out={'source_audit':source_audit,'selected_rows':selection,'box_certificates':[{'p':s['p'],'V_minus_K':str(Q(s['sums']['V'])-Q(s['sums']['factor_only_K'])),'sum_other_real_signed':str(Q(s['sums']['other_even_real'])-Q(s['sums']['other_odd_real'])),'sum_complex_signed':s['sums']['signed_complex']} for s in results['summaries']]}
(run/'residual-selected-analysis.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
