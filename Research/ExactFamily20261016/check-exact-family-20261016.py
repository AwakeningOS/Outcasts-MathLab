import hashlib
import importlib.util
import json
import math
import time
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path

RUN = Path(__file__).resolve().parent
START = time.monotonic()
INPUTS = [66529,345601,670849,1740481,3678481,5843041,8615161,18490201,53722321,84525841]
PORTABLE = (RUN/'character_helper.py').exists()
HELPER = RUN/'integer_helper.py' if PORTABLE else Path('/mnt/hdd1t/outcasts-reply-20261010-DnoRad/test-kneser-budget-20261010.py')
CHARS = RUN/'character_helper.py' if PORTABLE else Path('/mnt/hdd1t/outcasts-reply-20261013-ks9Uhb/check-residual-20261013.py')
ROWS13 = RUN/'baseline-log-rows.json' if PORTABLE else Path('/mnt/hdd1t/outcasts-reply-20261013-ks9Uhb/residual-audit-rows.json')
ROWS14 = RUN/'empty-rows.json' if PORTABLE else Path('/mnt/hdd1t/outcasts-reply-20261014-Dgn34n/slack-certificate-rows.json')

def checktime():
    assert time.monotonic()-START < 90, '90second contract limit'

def serial(x):
    if isinstance(x,Q): return str(x)
    if isinstance(x,dict): return {str(k):serial(v) for k,v in x.items()}
    if isinstance(x,(tuple,list)): return [serial(v) for v in x]
    return x

spec=importlib.util.spec_from_file_location('integer_helper',HELPER)
old=importlib.util.module_from_spec(spec)
spec.loader.exec_module(old)
ns={'__file__':str(CHARS)}
prefix=CHARS.read_text().split('\nrows=[]; summaries=[]')[0]
exec(compile(prefix,str(CHARS),'exec'),ns)

def lam(n):
    return math.lcm(*(2**(e-2) if q==2 and e>=3 else (q-1)*q**(e-1) for q,e in old.factor(n)))

def direct(n):
    out=set()
    for d in range(1,math.isqrt(n)+1):
        if n%d==0: out.update((d,n//d))
    return sorted(out)

def counts(fs,m):
    out={1:1}
    for q,e in fs:
        if q==2: continue
        nxt=Counter()
        for r,c in out.items():
            for j in range(e+1): nxt[r*pow(q,j,m)%m]+=c
        out=dict(nxt)
    return out

E=sorted({d for n in [60,126] for d in old.divisors(old.factor(n))})
assert len(E)==20
finite_lambda_checks=[]
for k in range(1,127):
    checktime()
    m=4*k
    L=lam(m)
    assert (L in (1,2,3,4,6)) == (k in E)
    assert (4%L==0) == (240%m==0)
    assert (6%L==0) == (504%m==0)
    units=[r for r in range(1,m) if math.gcd(r,m)==1]
    actual=math.lcm(*(next(j for j in range(1,len(units)+1) if pow(r,j,m)==1) for r in units))
    assert L==actual
    finite_lambda_checks.append({'k':k,'lambda':L,'in_E':k in E})

previous=json.loads(ROWS13.read_text())+json.loads(ROWS14.read_text())
assert len(previous)==610
rows=[]
for prev in sorted(previous,key=lambda r:(r['p'],r['a']*r['u'],r['a'])):
    checktime()
    p,a,u=prev['p'],prev['a'],prev['u']
    r=ns['factor_certificate'](p,a,u)
    assert r['root_order']==lam(r['m'])
    for key in ['W','V','signed_complex','complex_triangle_lower','factor_only_W_lower']:
        now=r['factor_character_count'] if key=='W' else r[key]
        assert now==Q(prev[key]),(p,a,u,key)
    W=r['factor_character_count']
    assert W==counts(r['factors'],r['m']).get(r['m']-1,0)
    eta=r['signed_complex']-r['complex_triangle_lower']
    c=max(Q(0),Q(W)-eta)
    assert c==r['factor_only_W_lower']
    forced=a*u in E
    assert not forced or eta==0
    all_constant=all(len(cp['signed_pair_poly'])==1 for cp in r['complex_pairs'])
    assert (eta==0)==all_constant
    rows.append({'p':p,'a':a,'u':u,'m':r['m'],'L':r['root_order'],'W':W,'eta':eta,'c':c,
                 'forced_E':forced,'all_pairs_constant':all_constant})

box=[]
for p in INPUTS:
    rs=[r for r in rows if r['p']==p]
    box.append({'p':p,'B':(p-1).bit_length(),'pairs':len(rs),'Wtot':sum(r['W'] for r in rs),
        'positive_rows':sum(r['c']>0 for r in rs),'positive_eta_zero':sum(r['c']>0 and r['eta']==0 for r in rs),
        'E_pairs':sum(r['forced_E'] for r in rs),'E_Wtot':sum(r['W'] for r in rs if r['forced_E']),
        'outside_E_zero_eta_rows':sum(not r['forced_E'] and r['eta']==0 for r in rs),
        'outside_E_zero_eta_Wtot':sum(r['W'] for r in rs if not r['forced_E'] and r['eta']==0),
        'Cert':sum((r['c'] for r in rs),Q(0)),
        'Cert0':sum((r['c'] for r in rs if r['eta']==0),Q(0)),
        'Certplus':sum((r['c'] for r in rs if r['eta']>0),Q(0))})
log_counter=[r for r in box if r['E_Wtot']==0]

extended=[]
for p in INPUTS:
    assert direct(p)==[1,p] and p%840 in {1,121,169,289,361,529}
    for k in E:
        for a in old.divisors(old.factor(k)):
            u=k//a
            if math.gcd(a,u)!=1: continue
            checktime()
            N,m=a*p+u,4*k
            fs=old.factor(N)
            assert math.prod(q**e for q,e in fs)==N
            assert all(direct(q)==[1,q] for q,e in fs)
            ds=direct(N)
            assert ds==old.divisors(fs)
            hits=[d for d in ds if d%m==m-1]
            assert len(hits)==counts(fs,m).get(m-1,0)
            extended.append({'p':p,'a':a,'u':u,'k':k,'N':N,'m':m,'L':lam(m),'factors':fs,
                             'W':len(hits),'witnesses':hits,'within_log_budget':k<=(p-1).bit_length()})
extsummary=[{'p':p,'pairs':sum(r['p']==p for r in extended),
             'successes':[r for r in extended if r['p']==p and r['W']>0]} for p in INPUTS]
totals={'positive_rows':sum(r['c']>0 for r in rows),
        'positive_eta_zero':sum(r['c']>0 and r['eta']==0 for r in rows),
        'positive_eta_nonzero':[r for r in rows if r['c']>0 and r['eta']>0],
        'E_rows':sum(r['forced_E'] for r in rows),
        'E_success_rows':sum(r['forced_E'] and r['W']>0 for r in rows),
        'outside_E_eta_zero_successes':[r for r in rows if not r['forced_E'] and r['eta']==0 and r['W']>0]}
result={'E':E,'E_pairs_per_prime':extsummary[0]['pairs'],'finite_lambda_checks':len(finite_lambda_checks),
        'prior_rows_recomputed_and_match':len(rows),'discovery_set_only':True,'box_summary':box,'totals':totals,
        'H_Elog':{'status':'Refuted' if log_counter else 'Unproved; all10 fixed discovery inputs pass',
                  'counterexample_inputs':[r['p'] for r in log_counter]},
        'H_E':{'status':'Refuted' if any(not r['successes'] for r in extsummary) else 'Unproved; all10 fixed discovery inputs pass',
               'counterexample_inputs':[r['p'] for r in extsummary if not r['successes']]},
        'full_E_summary':extsummary,'extended_rows':len(extended),'seconds':round(time.monotonic()-START,3),
        'new_ESC_prime_range_or5625_or_MC':False,'Lean_executed':False,'general_existence_proved':False,
        'source_hashes':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in [HELPER,CHARS,ROWS13,ROWS14]}}
(RUN/'exact-family-results.json').write_text(json.dumps(serial(result),indent=2)+'\n')
(RUN/'exact-family-log-rows.json').write_text(json.dumps(serial(rows),indent=2)+'\n')
(RUN/'exact-family-extended-rows.json').write_text(json.dumps(serial(extended),indent=2)+'\n')
(RUN/'exact-family-lambda-checks.json').write_text(json.dumps(finite_lambda_checks,indent=2)+'\n')
print(json.dumps(serial({k:v for k,v in result.items() if k not in ['full_E_summary','source_hashes']}),indent=2))
