import hashlib
import importlib.util
import json
import math
import subprocess
import time
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path

run = Path('/mnt/hdd1t/outcasts-reply-20261015-ACqg3d')
helper = Path('/mnt/hdd1t/outcasts-reply-20261010-DnoRad/test-kneser-budget-20261010.py')
spec = importlib.util.spec_from_file_location('integer_helper', helper)
old = importlib.util.module_from_spec(spec)
spec.loader.exec_module(old)
start = time.monotonic()
inputs = [66529,345601,670849,1740481,3678481,5843041,8615161,18490201,53722321,84525841]
expected = {
    66529: [43,4,40,33,7,4,'-13/8','-5/4'],
    345601: [49,5,45,36,9,9,'-7/4','-857/180'],
    670849: [53,4,50,40,10,10,'1/4','-151/45'],
    1740481: [57,6,53,42,11,9,'-85/12','-1013/180'],
    3678481: [61,7,56,46,10,7,'47/60','-4'],
    5843041: [63,4,60,48,12,9,'-689/120','-581/60'],
    8615161: [67,14,57,43,14,8,'-17/72','-6239/990'],
    18490201: [69,3,66,53,13,7,'-259/120','-2881/660'],
    53722321: [73,8,67,58,9,8,'-127/120','-13/5'],
    84525841: [75,3,72,59,13,10,'-2309/720','-14437/3960']}
prior_rows = json.loads(Path('/mnt/hdd1t/outcasts-reply-20261013-ks9Uhb/residual-audit-rows.json').read_text()) + json.loads(Path('/mnt/hdd1t/outcasts-reply-20261014-Dgn34n/slack-certificate-rows.json').read_text())
prior = {(r['p'],r['a'],r['u']):r for r in prior_rows}
assert len(prior) == 610


def direct(n):
    out = set()
    for d in range(1,math.isqrt(n)+1):
        if n % d == 0:
            out.update((d,n//d))
    return sorted(out)


def bounded_residue_counts(fs,m):
    counts = {1:1}
    for q,e in fs:
        next_counts = Counter()
        for s,n in counts.items():
            for j in range(e+1):
                next_counts[s*pow(q,j,m)%m] += n
        counts = dict(next_counts)
    return counts


def serial(x):
    if isinstance(x,Q): return str(x)
    if isinstance(x,dict): return {str(k):serial(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)): return [serial(v) for v in x]
    return x


rows = []
summaries = []
for p in inputs:
    assert direct(p) == [1,p] and p%840 in {1,121,169,289,361,529}
    B = (p-1).bit_length()
    data = []
    for a in range(1,B+1):
        for u in range(1,B//a+1):
            if math.gcd(a,u) != 1: continue
            assert time.monotonic()-start < 180
            N,m = a*p+u,4*a*u
            fs = old.factor(N)
            assert math.prod(q**e for q,e in fs) == N
            odd = [(q,e) for q,e in fs if q != 2]
            assert all(math.gcd(q,m) == 1 for q,e in odd)
            ds = direct(N)
            assert ds == old.divisors(fs)
            ods = [s for s in ds if s%2]
            counts = Counter(s%m for s in ods)
            assert dict(counts) == bounded_residue_counts(odd,m)
            G = [g for g in range(1,m) if math.gcd(g,m) == 1]
            H = {g*g%m for g in G}
            minusH = {(-h)%m for h in H}
            assert m-1 not in H and len(G)%len(H) == 0
            cosets = {min(g*h%m for h in H):{g*h%m for h in H} for g in G}
            quotient_counts = {rep:sum(counts.get(g,0) for g in coset) for rep,coset in cosets.items()}
            Wg = sum(counts.get(g,0) for g in minusH)
            W = counts.get(m-1,0)
            span = set(H)
            for q,e in odd:
                span |= {g*q%m for g in span}
            assert (Wg>0) == (m-1 in span)
            K = old.generated([q%m for q,e in odd],m)
            assert all(s in K for s in counts)
            tau = len(ods)
            F0 = math.prod(sum((1 if pow(p%q,(q-1)//2,q) == 1 else -1)**j for j in range(e+1)) for q,e in odd)
            V = Q(tau-F0,len(G))
            R = Q(Wg,len(H))
            C = Q(W)-R
            existing = prior[p,a,u]
            assert W == existing['W'] and V == Q(existing['V'])
            assert R-V == Q(existing['other_even_real'])-Q(existing['other_odd_real']) and C == Q(existing['signed_complex'])
            uniform = len(set(quotient_counts.values())) == 1
            if W:
                kind = 'success'
            elif Wg == 0:
                kind = 'quadratic_obstruction'
                assert C == 0 and m-1 not in K
            elif m-1 not in K:
                kind = 'remaining_full_group_obstruction'
                assert C < 0
            else:
                kind = 'finite_exponent_shortage'
                assert C < 0
            lift = None
            if Wg and len(H)%2:
                assert m-1 in K
                s = next(s for s in ods if s%m in minusH)
                h = (-s)%m
                r = next(j for j in range(1,len(H)+1) if pow(h,j,m) == 1)
                assert len(H)%r == 0 and r%2 == 1 and pow(s,r,m) == m-1
                sfs = dict(old.factor(s))
                violation = [[q,r*sfs.get(q,0),e] for q,e in odd if r*sfs.get(q,0)>e]
                if not W: assert violation
                lift = {'s':s,'h':h,'odd_order':r,'s_power_target':True,'outside_exponent_budget':violation}
            row = {'p':p,'a':a,'u':u,'N':N,'m':m,'factors':fs,'odd_divisors':ods,'residue_counts':dict(counts),'square_subgroup':sorted(H),'negative_square_coset':sorted(minusH),'quotient_counts':quotient_counts,'Wg':Wg,'W':W,'V':V,'R':R,'C':C,'real_minus_V':R-V,'full_generated_group':sorted(K),'kind':kind,'uniform_real_quotient':uniform,'odd_square_lift':lift}
            data.append(row)
    failures = [r for r in data if r['W'] == 0]
    stage1 = sum(r['kind'] == 'quadratic_obstruction' for r in data)
    remaining_group = sum(r['kind'] == 'remaining_full_group_obstruction' for r in data)
    exponent = sum(r['kind'] == 'finite_exponent_shortage' for r in data)
    uniform_fail = sum(r['Wg']>0 and r['W']==0 and r['uniform_real_quotient'] for r in data)
    vector = [len(data),sum(r['W'] for r in data),len(failures),stage1,remaining_group+exponent,uniform_fail,str(sum((r['real_minus_V'] for r in data),Q(0))),str(sum((r['C'] for r in data),Q(0)))]
    assert vector == expected[p],(p,vector,expected[p])
    summaries.append({'p':p,'pairs':len(data),'Wtot':vector[1],'failed_pairs':len(failures),'quadratic_obstruction':stage1,'remaining_full_group_obstruction':remaining_group,'finite_exponent_shortage':exponent,'uniform_real_quotient_failures':uniform_fail,'sum_A_minus_B':vector[-2],'sum_C':vector[-1],'odd_H_second_stage_failures':sum(r['Wg']>0 and r['W']==0 and len(r['square_subgroup'])%2==1 for r in data)})
    rows.extend(data)
assert len(rows)==610
group_fail = next((r for r in rows if r['kind']=='remaining_full_group_obstruction'),None)
if group_fail:
    source=Path('/mnt/hdd1t/outcasts-reply-20261013-ks9Uhb/check-residual-20261013.py')
    ns={}
    exec(compile(source.read_text().split('\nrows=[]; summaries=[]')[0],str(source),'exec'),ns)
    L,chars=ns['character_data'](group_fail['m'])
    separating=next(c for c in chars if c['sign']==-1 and all(c['phases'][q%group_fail['m']]==0 for q,e in group_fail['factors'] if q!=2) and (L//math.gcd(L,*c['phases'].values()))&(L//math.gcd(L,*c['phases'].values())-1)==0)
    d=L//math.gcd(L,*separating['phases'].values())
    assert d>2
    group_fail['separating_2power_character']={'order':d,'root_order':L,'param':separating['param'],'target_phase':separating['phases'][group_fail['m']-1],'prime_phases':[[q,separating['phases'][q%group_fail['m']]] for q,e in group_fail['factors'] if q!=2]}
odd_fail = next(r for r in rows if r['kind']=='finite_exponent_shortage' and len(r['square_subgroup'])%2==1)
size_counts=Counter(len({g*g%(4*a*u) for g in range(1,4*a*u) if math.gcd(g,4*a*u)==1}) for a in range(1,28) for u in range(1,27//a+1) if math.gcd(a,u)==1)
assert sum(size_counts.values())==75 and sum(v for k,v in size_counts.items() if k<=4)==51
H20={g*g%20 for g in range(1,20) if math.gcd(g,20)==1}
assert H20=={1,9} and 11 in {(-h)%20 for h in H20} and old.generated([11],20)=={1,11} and 19 not in old.generated([11],20)
post=next(p for p in json.loads((run/'outcasts-heartbeat-20261015-response-3.json').read_text())['structuredContent']['posts'] if p['post_number']==61)
script=post['content_md'].split("python3 - <<'PY'\n",1)[1].split("\nPY\n```",1)[0]+'\n'
(run/'source61-original.py').write_text(script)
replayed=subprocess.run(['python3',str(run/'source61-original.py')],cwd=run,text=True,capture_output=True,timeout=60)
(run/'source61-replay.log').write_text(replayed.stdout+replayed.stderr)
assert replayed.returncode==0
for p,vector in expected.items():
    line=next(line for line in replayed.stdout.splitlines() if f'p={p:8d}' in line)
    assert f'rows={vector[0]:2d} W={vector[1]:2d}' in line and f'W_G2=0:{vector[3]:2d}' in line and f'W_G2>0:{vector[4]:2d}' in line
    assert f'[F_real=0:{vector[5]:2d}]' in line and f'sum(A-B)={vector[6]:>9s} sum(C)={vector[7]:>9s}' in line
result={'contract':'square-coset-contract-20261015.md','fixed_inputs':inputs,'summaries':summaries,'all610_previous_numeric_rows_and_independent_methods_match':True,'post61_table_all10_rows_match':True,'source61_replay_exit':replayed.returncode,'source61_original_sha256':hashlib.sha256(script.encode()).hexdigest(),'Qquad_counterexample':group_fail,'odd_H_exponent_example':odd_fail,'square_subgroup_size_distribution_through27':dict(size_counts),'totals':{kind:sum(r['kind']==kind for r in rows) for kind in ['success','quadratic_obstruction','remaining_full_group_obstruction','finite_exponent_shortage']},'odd_H_lifting_all_rows_pass':True,'abstract_even_H_control':{'N':11,'m':20,'H':[1,9],'minusH':[11,19],'generated':[1,11],'Wg':1,'W':0,'not_a_residual_prime_counterexample':True},'helper_sha256':hashlib.sha256(helper.read_bytes()).hexdigest(),'general_existence_proved':False,'Hlog_or_ESC_refuted':False,'seconds':round(time.monotonic()-start,3)}
(run/'square-coset-results.json').write_text(json.dumps(serial(result),indent=2)+'\n')
(run/'square-coset-rows.json').write_text(json.dumps(serial(rows),indent=2)+'\n')
print(json.dumps(serial(result),indent=2))
