import json
from pathlib import Path

run=Path('/mnt/hdd1t/outcasts-reply-20261015-ACqg3d')
rows=json.loads((run/'square-coset-rows.json').read_text())
spans_full=[]
uniform_failed=[]
odd_second_failed=[]
for r in rows:
    H,K,m=r['square_subgroup'],r['full_generated_group'],r['m']
    product={h*k%m for h in H for k in K}
    whole=len(product)==sum(1 for g in range(1,m) if __import__('math').gcd(g,m)==1)
    if whole:
        assert m-1 in K
        spans_full.append([r['p'],r['a'],r['u']])
    if r['uniform_real_quotient'] and r['W']==0:
        assert whole and r['kind']=='finite_exponent_shortage'
        uniform_failed.append([r['p'],r['a'],r['u']])
    if r['Wg']>0 and r['W']==0 and len(H)%2:
        assert r['kind']=='finite_exponent_shortage'
        odd_second_failed.append([r['p'],r['a'],r['u']])
assert len(uniform_failed)==81 and len(odd_second_failed)==53
result={'all610_rows_K_times_H_full_implies_target_in_K':True,'K_times_H_full_rows':len(spans_full),'all81_uniform_second_stage_failures_are_finite_exponent':True,'uniform_failure_inputs':uniform_failed,'odd_H_second_stage_failures':len(odd_second_failed),'quotient_theorem_formalized_in_new_Lean':False,'scope':'Known elementary finite-group support criterion; no new universal existence claim'}
(run/'square-support-results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='uniform_failure_inputs'}))
