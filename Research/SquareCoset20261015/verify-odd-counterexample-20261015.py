import json
import math
from pathlib import Path

run=Path('/mnt/hdd1t/outcasts-reply-20261015-ACqg3d')
p=5843041
rows=[r for r in json.loads((run/'square-coset-rows.json').read_text()) if r['p']==p]
assert len(rows)==63 and (p-1).bit_length()==23
assert [(r['a'],r['u']) for r in rows]==[(a,u) for a in range(1,24) for u in range(1,23//a+1) if math.gcd(a,u)==1]
odd=[]
successful=[]
for r in rows:
    m,N=r['m'],r['N']
    units=[g for g in range(1,m) if math.gcd(g,m)==1]
    roots=sum(g*g%m==1 for g in units)
    cardinal=len(units)//roots
    assert cardinal==len(r['square_subgroup'])
    divisors=set()
    for d in range(1,math.isqrt(N)+1):
        if N%d==0: divisors.update((d,N//d))
    hits=sorted(s for s in divisors if s%m==m-1)
    assert len(hits)==r['W']
    if cardinal%2:
        assert hits==[]
        odd.append([r['a'],r['u'],cardinal])
    if hits:
        assert cardinal%2==0
        successful.append({'a':r['a'],'u':r['u'],'H_card':cardinal,'target_divisors':hits})
assert len(successful)==3 and sum(len(r['target_divisors']) for r in successful)==4
result={'p':p,'budget':23,'complete_coprime_pairs':63,'odd_H_pairs':len(odd),'all_odd_H_pairs':odd,'all_odd_H_witness_counts_zero':True,'actual_successful_pairs':successful,'Wtot':4,'cardinality_via_squaring_kernel_matches':True,'independent_direct_divisor_recheck':True,'Hoddlog_status':'Refuted','posthoc_candidate_test':True,'Hlog_or_ESC_refuted':False,'unrestricted_odd_H_existence_refuted':False,'new_prime_range_scan':False}
(run/'odd-candidate-counterexample.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
