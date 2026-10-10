import functools
import importlib.util
import json
import math
from pathlib import Path

RUN = Path('/mnt/hdd1t/outcasts-reply-20261010-DnoRad')
spec = importlib.util.spec_from_file_location('kb', RUN / 'test-kneser-budget-20261010.py')
kb = importlib.util.module_from_spec(spec)
spec.loader.exec_module(kb)
rows = json.loads((RUN / 'counterexample-kneser-all-rows.json').read_text())
p, B = 8615161, 24
assert kb.factor(p) == [(p,1)] and p%840 == 121 and (p-1).bit_length()==B

def brute_closure(gens,m):
    found={1}
    while True:
        enlarged=found|{x*y%m for x in found for y in gens}
        if enlarged==found:
            return frozenset(found)
        found=enlarged

@functools.lru_cache(None)
def unit_subgroups(m):
    units=frozenset(x for x in range(1,m) if math.gcd(x,m)==1)
    found={frozenset({1})}
    while True:
        enlarged=found|{brute_closure(list(H)+[g],m) for H in found for g in units-H}
        if enlarged==found:
            return found
        found=enlarged

def order_cosets(q,H,m):
    cosets=[frozenset(H)]
    current=frozenset(x*q%m for x in H)
    while current!=H:
        assert current not in cosets
        cosets.append(current)
        current=frozenset(x*q%m for x in current)
    return len(cosets)

audit_rows=[]
for r in rows:
    a,u,m,M=r['a'],r['u'],r['modulus'],r['M']
    assert m==4*a*u and M==a*p+u and math.gcd(a,u)==1 and a*u<=B
    ds=set()
    for d in range(1,math.isqrt(M)+1):
        if M%d==0:
            ds.update([d,M//d])
    prime_divisors = [q for q in sorted(ds) if q > 1 and not any(1 < d < q and q % d == 0 for d in ds)]
    independent_fs = []
    for q in prime_divisors:
        e, remainder = 0, M
        while remainder % q == 0:
            remainder //= q
            e += 1
        independent_fs.append([q,e])
    assert independent_fs == r['factorization']
    assert [z for z in independent_fs if math.gcd(z[0],m)==1] == r['unit_factorization']
    assert sorted(d for d in ds if d%m==m-1)==r['witnesses']
    assert sorted({d%m for d in ds if math.gcd(d,m)==1})==r['actual_divisor_residues']
    uf=r['unit_factorization']
    G=brute_closure([q%m for q,e in uf],m)
    assert sorted(G)==r['G']
    rec={'a':a,'u':u,'M':M,'m':m,'witnesses':r['witnesses'],'factorization':r['factorization'],'G':sorted(G)}
    if m-1 not in G:
        rec['kind']='group_obstruction'
        rec['certificate_G']=sorted(G)
    else:
        subs=sorted([H for H in unit_subgroups(m) if H<=G],key=lambda H:(len(H),sorted(H)))
        assert set(subs)==set(kb.subgroups(G,m))
        bad=[]
        for H in subs:
            if m-1 in H:
                continue
            orders=[order_cosets(q,H,m) for q,e in uf]
            admissible=all(q%m in H or order>e+1 for (q,e),order in zip(uf,orders))
            if not admissible:
                continue
            L=sum(e for (q,e),order in zip(uf,orders) if order>1)
            index=len(G)//len(H)
            if L<index-1:
                bad.append({'H':sorted(H),'orders':orders,'L':L,'index':index,'threshold':index-1,
                            'admissible':True,'factor_image_sizes':[min(e+1,o) for (q,e),o in zip(uf,orders)]})
        rec['kind']='admissible_Kneser_bound_failure' if bad else 'refined_Kneser_passes'
        rec['admissible_bad_quotient']=bad[0] if bad else None
    audit_rows.append(rec)

expected=sorted((a,u) for a in range(1,B+1) for u in range(1,B//a+1) if math.gcd(a,u)==1)
assert sorted((r['a'],r['u']) for r in audit_rows)==expected and len(expected)==67
successes=[r for r in audit_rows if r['witnesses']]
selected=next(r for r in successes if (r['a'],r['u'])==(4,1))
s=815
assert s in selected['witnesses']
alpha,v=(s+1)//16,(4*p+1)//s
xyz=sorted([alpha*v,4*alpha*p,4*alpha*v*p])
x,y,z=xyz
assert alpha==51 and v==42283 and 4*x*y*z==p*(x*y+x*z+y*z)
result={'p':p,'p_is_prime':True,'residue_mod840':p%840,'budget':B,'coprime_pairs':len(rows),
        'actual_success_pairs':len(successes),'all_divisor_integer_scans_match':True,
        'all_prime_factorizations_independently_recovered_from_divisors':True,
        'all_generated_groups_and_subgroups_match':True,
        'failure_counts':{k:sum(r['kind']==k for r in audit_rows) for k in ['group_obstruction','admissible_Kneser_bound_failure','refined_Kneser_passes']},
        'stronger_admissible_quotient_candidate_also_refuted':all(r['kind']!='refined_Kneser_passes' for r in audit_rows),
        'selected_actual_success':selected,'positive_ESC_denominators':xyz,
        'Hlog_refuted':False,'ESC_refuted':False,'Lean_verified':False,'rows':audit_rows}
(RUN/'kneser-counterexample-independent-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='rows'},indent=2))
