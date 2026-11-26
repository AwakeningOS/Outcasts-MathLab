import importlib.util
import json
import math
import time
from collections import Counter
from fractions import Fraction
from itertools import product
from pathlib import Path

run = Path('/mnt/hdd1t/outcasts-reply-20261011-xanKS3')
source = Path('/mnt/hdd1t/outcasts-reply-20261010-DnoRad/test-kneser-budget-20261010.py')
spec = importlib.util.spec_from_file_location('prior_kneser', source)
old = importlib.util.module_from_spec(spec)
spec.loader.exec_module(old)
start = time.monotonic()

def integer_divisors(n):
    out = set()
    for k in range(1, math.isqrt(n)+1):
        if n % k == 0:
            out.update((k, n//k))
    return sorted(out)

records = []
all_rows = []
for p in [8615161,53722321]:
    assert old.factor(p) == [(p,1)]
    B = (p-1).bit_length()
    rows = []
    for a in range(1,B+1):
        for u in range(1,B//a+1):
            if math.gcd(a,u) != 1:
                continue
            assert time.monotonic()-start < 120
            r = old.row(p,a,u)
            ds = integer_divisors(r['M'])
            assert ds == old.divisors(r['factorization'])
            assert [s for s in ds if (s+1) % r['modulus'] == 0] == r['witnesses']
            G, m, uf = frozenset(r['G']), r['modulus'], r['unit_factorization']
            bad = []
            if m-1 in G:
                for H in old.subgroups(G,m):
                    if m-1 in H:
                        continue
                    if any(q % m not in H and old.order_mod_subgroup(q,H,m) <= e+1 for q,e in uf):
                        continue
                    L = sum(e for q,e in uf if q % m not in H)
                    if L < len(G)//len(H)-1:
                        bad.append({'H':sorted(H),'L':L,'threshold':len(G)//len(H)-1})
            r['A'] = m-1 in G and not bad
            r['admissible_bad_quotients'] = bad
            assert not r['A'] or r['witnesses']
            rows.append(r)
    summary = {'p':p,'mod840':p%840,'budget':B,'pairs':len(rows),
       'K_passes':sum(r['K'] for r in rows),'A_passes':sum(r['A'] for r in rows),
       'failure_counts':dict(Counter('group_obstruction' if r['modulus']-1 not in r['G'] else 'admissible_bound' for r in rows)),
       'actual_successful_pairs':sum(bool(r['witnesses']) for r in rows),
       'actual_witnesses':sum(len(r['witnesses']) for r in rows),
       'all_divisor_methods_agree':True}
    if p == 8615161:
        participant = json.loads((run/'participants/KneserReview20261010/kneser_check_results.json').read_text())
        partner = {(r['a'],r['u']):r for r in participant['rows']}
        for r in rows:
            other = partner[(r['a'],r['u'])]
            assert r['M'] == other['M'] and r['modulus'] == other['m']
            assert dict((str(q),e) for q,e in r['factorization']) == other['factors']
            assert r['actual_divisor_residues'] == other['D']
            assert r['K'] == other['K'] and r['A'] == other['A']
            assert r['witnesses'] == other['witnesses']
        summary['all_67_partner_rows_matched'] = True
        assert (summary['pairs'],summary['actual_successful_pairs'],summary['actual_witnesses']) == (67,10,14)
    else:
        assert (summary['pairs'],summary['actual_successful_pairs'],summary['actual_witnesses']) == (73,6,8)
        assert summary['failure_counts'] == {'group_obstruction':58,'admissible_bound':15}
        selected = next(r for r in rows if (r['a'],r['u']) == (8,1))
        assert selected['factorization'] == [(3,1),(11,3),(37,1),(2909,1)]
        assert selected['witnesses'] == [31999]
        s = 31999
        t, v = selected['M']//s, (s+1)//selected['modulus']
        denominators = [v*t,8*v*p,8*v*t*p]
        assert Fraction(4,p) == sum((Fraction(1,d) for d in denominators),Fraction(0))
        summary['selected_a8_u1'] = {'s':s,'factors':selected['factorization'],'G_size':len(selected['G']),'D':selected['actual_divisor_residues'],'admissible_bad_quotients':selected['admissible_bad_quotients'],'denominators':denominators,'numeric_identity_exact':True}
    assert summary['K_passes'] == summary['A_passes'] == 0
    records.append(summary)
    all_rows += rows

toy_rows = []
observed_mean, bootstrap_mean = Fraction(0),Fraction(0)
for y1,y2 in product((0,1),repeat=2):
    ph = Fraction(y1+y2,2)
    conditional = Fraction(0)
    bootstrap = Fraction(0)
    for f1,f2 in product((0,1),repeat=2):
        residual = (f1-ph)*(f2-ph)
        conditional += Fraction(1,4)*residual
        prob = (ph if f1 else 1-ph)*(ph if f2 else 1-ph)
        bootstrap += prob*residual
        toy_rows.append({'training':[y1,y2],'test':[f1,f2],'estimated_probability':str(ph),'residual_product':str(residual),'true_joint_probability':'1/16'})
    assert conditional == (Fraction(1,2)-ph)**2
    assert bootstrap == 0
    observed_mean += Fraction(1,4)*conditional
    bootstrap_mean += Fraction(1,4)*bootstrap
assert observed_mean == Fraction(1,8) and bootstrap_mean == 0
result = {'fixed_inputs':records,'split_calibration_toy':{'independent_Bernoulli_half_training_and_test':True,'training_rows':2,'test_rows':2,'exact_outcomes':16,'true_unconditional_residual_product_mean':str(observed_mean),'plug_in_bootstrap_mean':str(bootstrap_mean),'same_sample_fit_used':False,'reported_D2_p_values_refuted':False,'rows':toy_rows},'seconds':round(time.monotonic()-start,3),'full_1e8_or_MC_replay':False,'universal_existence_proved':False}
(run/'reply-fixed-review-results.json').write_text(json.dumps(result,indent=2)+'\n')
(run/'kneser-two-fixed-boxes-all140.json').write_text(json.dumps(all_rows,indent=2)+'\n')
print(json.dumps({**result,'split_calibration_toy':{k:v for k,v in result['split_calibration_toy'].items() if k!='rows'}}))
