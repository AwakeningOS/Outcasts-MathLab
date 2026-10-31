import hashlib
import importlib.util
import json
import math
import time
from fractions import Fraction
from pathlib import Path

run=Path('/mnt/hdd1t/outcasts-reply-20261012-ZXux6H')
helper=Path('/mnt/hdd1t/outcasts-reply-20261010-DnoRad/test-kneser-budget-20261010.py')
spec=importlib.util.spec_from_file_location('old',helper)
old=importlib.util.module_from_spec(spec)
spec.loader.exec_module(old)
previous=json.loads(Path('/mnt/hdd1t/outcasts-reply-20261011-xanKS3/kneser-two-fixed-boxes-all140.json').read_text())
prior={(r['p'],r['a'],r['u']):r for r in previous}
def divisors(n):
    out=set()
    for i in range(1,math.isqrt(n)+1):
        if n%i==0: out.update((i,n//i))
    return sorted(out)
def phi(n):
    out=n
    for q,e in old.factor(n): out=out//q*(q-1)
    return out
start=time.monotonic()
tables=[]
summaries=[]
for p in [8615161,53722321]:
    assert divisors(p)==[1,p]
    B=(p-1).bit_length()
    rows=[]
    for a in range(1,B+1):
        for u in range(1,B//a+1):
            if math.gcd(a,u)!=1: continue
            assert time.monotonic()-start<60
            N=a*p+u
            m=4*a*u
            assert math.gcd(N,a*u)==1
            ds=divisors(N)
            fac=old.factor(N)
            assert math.prod(q**e for q,e in fac)==N
            assert ds==old.divisors(fac)
            odd=sum(d%2==1 for d in ds)
            assert odd==math.prod(e+1 for q,e in fac if q!=2)
            assert odd==sum(math.gcd(d,m)==1 for d in ds)
            witnesses=[d for d in ds if (d+1)%m==0]
            assert witnesses==prior[(p,a,u)]['witnesses']
            W=len(witnesses)
            main=Fraction(odd,phi(m))
            error=W-main
            rows.append({'p':p,'a':a,'u':u,'N':N,'m':m,'tau_odd':odd,'phi':phi(m),'main':main,'error':error,'W':W})
    main=sum((r['main'] for r in rows),Fraction(0))
    plus=sum((max(Fraction(0),r['error']) for r in rows),Fraction(0))
    minus=sum((max(Fraction(0),-r['error']) for r in rows),Fraction(0))
    radius=plus+minus
    W=sum(r['W'] for r in rows)
    assert W==main+plus-minus
    assert W>=main-radius
    summaries.append({'p':p,'B':B,'pairs':len(rows),'M':str(main),'R':str(radius),'Eplus':str(plus),'Eminus':str(minus),'Wtotal':W,'W_over_M':str(Fraction(W)/main),'M_minus_R':str(main-radius),'Habslog_pass':main>radius,'Hlog_witness_present':W>0,'positive_errors':sum(r['error']>0 for r in rows),'negative_errors':sum(r['error']<0 for r in rows),'zero_errors':sum(r['error']==0 for r in rows),'all_divisor_and_prior_methods_match':True})
    tables.extend({k:str(v) if isinstance(v,Fraction) else v for k,v in r.items()} for r in rows)
result={'contract':'character-budget-contract-20261012.md','candidate':'Habslog','known_identity_not_new_theorem':True,'summaries':summaries,'new_ESC_range_scan':False,'general_existence_proved':False,'seconds':round(time.monotonic()-start,3),'helper_sha256':hashlib.sha256(helper.read_bytes()).hexdigest()}
(run/'character-budget-results.json').write_text(json.dumps(result,indent=2)+'\n')
(run/'character-budget-all140.json').write_text(json.dumps(tables,indent=2)+'\n')
print(json.dumps(result))
