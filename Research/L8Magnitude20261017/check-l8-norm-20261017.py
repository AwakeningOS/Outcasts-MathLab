import argparse
import csv
import gzip
import hashlib
import importlib.util
import json
import math
import time
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path

RUN=Path(__file__).resolve().parent
START=time.monotonic()
parser=argparse.ArgumentParser()
parser.add_argument('--development-file',type=Path)
args=parser.parse_args()
HELPER=RUN/'character_helper.py'
if not HELPER.exists(): HELPER=Path('/mnt/hdd1t/outcasts-reply-20261016-Szuygm/public/character_helper.py')
spec=importlib.util.spec_from_file_location('characters',HELPER)
ch=importlib.util.module_from_spec(spec); spec.loader.exec_module(ch)
old=ch.old
P=38296729
INPUTS=[66529,345601,670849,1740481,3678481,5843041,8615161,18490201,53722321,84525841,P]
E=sorted(set(old.divisors(old.factor(60)))|set(old.divisors(old.factor(126))))
EXPECTED_SHA='2851fb4611be7461ddc92d63d94ba9939b071c2fba236d9f353c01b44a43b8b1'

def checktime(): assert time.monotonic()-START<180,'180second contract limit'
def serial(x):
    if isinstance(x,Q):return str(x)
    if isinstance(x,dict):return {str(k):serial(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)):return [serial(v) for v in x]
    return x
def lam(n):return math.lcm(*(2**(e-2) if q==2 and e>=3 else (q-1)*q**(e-1) for q,e in old.factor(n)))
def legendre(n,p):
    v=pow(n%p,(p-1)//2,p)
    return -1 if v==p-1 else v
def counts(fs,m):
    out={1:1}
    for q,e in fs:
        if q==2:continue
        nxt=Counter()
        for r,n in out.items():
            for j in range(e+1):nxt[r*pow(q,j,m)%m]+=n
        out=dict(nxt)
    return out
def local_norm(h,e):
    g,d=e+1,0
    for j in range(1,e+1):
        w=e+1-j; t=h*j%8
        if t==0:g+=2*w
        elif t==4:g-=2*w
        elif t in (1,7):d+=w
        elif t in (3,5):d-=w
    return g,d
def multiply(x,y):return x[0]*y[0]+2*x[1]*y[1],x[0]*y[1]+x[1]*y[0]
def sqrt_upper(u):
    assert u>=0
    numerator=u.numerator*1024**2; denominator=u.denominator
    t=math.isqrt(numerator//denominator)
    if t*t*denominator<numerator:t+=1
    assert t*t*denominator>=numerator
    return Q(t,1024)
def gaussian_local(h,e):
    assert h%2==0
    vals=[(1,0),(0,1),(-1,0),(0,-1)]
    return tuple(sum(vals[(h//2*j)%4][i] for j in range(e+1)) for i in range(2))
def gaussian_mul(x,y):return x[0]*y[0]-x[1]*y[1],x[0]*y[1]+x[1]*y[0]

def magnitude_certificate(fs,m):
    # Only the order4 phase is retained. No order8 F or argument is computed here.
    L,chars=ch.character_data(m); assert L==8
    # Square-coset baseline from real characters only, not a full residue DP.
    real_numerator=0
    for c in chars:
        if not c['real']:continue
        f=1
        for q,e in fs:
            if q!=2:
                h=c['phases'][q%m]
                assert h in (0,4)
                f*=e+1 if h==0 else (1 if e%2==0 else 0)
        real_numerator+=c['sign']*f
    R=Q(real_numerator,ch.phi(m)); assert R>=0
    units=sorted(chars[0]['phases'])
    index={tuple(c['phases'][g] for g in units):i for i,c in enumerate(chars)}
    T4=0; terms=[]
    for i,c in enumerate(chars):
        if c['real']:continue
        other=index[tuple((-c['phases'][g])%8 for g in units)]
        if i>other:continue
        d=8//math.gcd(8,*c['phases'].values())
        if d==4:
            f=(1,0)
            for q,e in fs:
                if q!=2:f=gaussian_mul(f,gaussian_local(c['phases'][q%m],e))
            T4+=2*c['sign']*f[0]
        else:
            assert d==8
            norm=(1,0)
            for q,e in fs:
                if q!=2:norm=multiply(norm,local_norm(c['phases'][q%m],e))
            g,d=norm
            u=Q(g)+(Q(3,2) if d>=0 else Q(7,5))*d
            rho=sqrt_upper(u)
            terms.append({'param':c['param'],'gamma':g,'delta':d,'norm_squared_upper':u,'rho':rho})
    raw=R+Q(T4, ch.phi(m))-Q(2,ch.phi(m))*sum((t['rho'] for t in terms),Q(0))
    return {'T4':T4,'order8_magnitude_terms':terms,'raw_lower':raw,'c_mag':max(Q(0),raw)}

norm_validation_rows=0
def independent_norm_check(fs,m,mag):
    global norm_validation_rows
    L,chars=ch.character_data(m)
    assert L==8
    lookup={c['param']:c for c in chars}
    for term in mag['order8_magnitude_terms']:
        c=lookup[term['param']]
        f=[1]+[0]*7
        conjugate=[1]+[0]*7
        for q,e in fs:
            if q==2:continue
            local=[0]*8; other=[0]*8
            for j in range(e+1):
                local[j*c['phases'][q%m]%8]+=1
                other[-j*c['phases'][q%m]%8]+=1
            f=ch.cyclic_mul(f,local,8)
            conjugate=ch.cyclic_mul(conjugate,other,8)
        actual=ch.reduce(ch.cyclic_mul(f,conjugate,8),8)
        expected=ch.trim([term['gamma'],term['delta'],0,-term['delta']])
        assert actual==expected
    norm_validation_rows+=1

def row(p,a,u,direct=False):
    checktime()
    N,m=a*p+u,4*a*u
    fs=old.factor(N)
    assert math.prod(q**e for q,e in fs)==N
    ds=old.divisors(fs)
    rc=counts(fs,m)
    W=rc.get(m-1,0)
    hits=[d for d in ds if d%m==m-1]
    assert W==len(hits)
    if direct:assert ch.direct(N)==ds and all(ch.direct(q)==[1,q] for q,e in fs)
    cert=ch.factor_certificate(p,a,u)
    assert cert['factor_character_count']==W
    G=[g for g in range(1,m) if math.gcd(g,m)==1]
    H={g*g%m for g in G}
    WH=sum(n for r,n in rc.items() if (-r)%m in H)
    R=Q(WH,len(H))
    C=cert['signed_complex']; eta=C-cert['complex_triangle_lower']
    assert R==cert['V']+cert['other_even_real']-cert['other_odd_real'] and R+C==W
    K=old.generated([q%m for q,e in fs if q!=2],m)
    nr=[(q,e) for q,e in fs if legendre(q,p)==-1]
    nonres=sum(e for q,e in nr)
    data={'p':p,'a':a,'u':u,'N':N,'m':m,'L':cert['root_order'],'factors':fs,'W':W,'witnesses':hits,
          'R':R,'C':C,'ell_over_phi':cert['complex_triangle_lower'],'eta':eta,'old_c':cert['factor_only_W_lower'],
          'b':min(cert['V'],cert['factor_only_W_lower']),'nonresidue_factors':nr,'nonresidue_multiplicity':nonres,
          'target_in_K':m-1 in K,'W_H':WH,'H_card':len(H),'u_legendre':legendre(u,p)}
    if cert['root_order']==8:
        assert legendre(u,p)==1
        assert nonres%2==0 and (W==0 or nonres>=2)
        for s in hits:assert legendre(s,p)==legendre(N//s,p)==-1
        # Prove this execution cannot accidentally use W/divisor reconstruction.
        saved=(ch.factor_certificate,ch.direct,old.divisors)
        def forbidden(*a,**kw):raise AssertionError('W/divisor oracle called by magnitude certificate')
        try:
            ch.factor_certificate=ch.direct=old.divisors=forbidden
            mag=magnitude_certificate(fs,m)
        finally:
            ch.factor_certificate,ch.direct,old.divisors=saved
        assert 0<=mag['c_mag']<=W
        assert nonres>=2 or mag['c_mag']==0
        if direct or mag['c_mag']>0:independent_norm_check(fs,m,mag)
        data.update(mag)
        data['rescues_old_zero']=data['old_c']==0 and mag['c_mag']>0
        data['loses_old_positive']=data['old_c']>0 and mag['c_mag']==0
        data['Qmag_counterexample']=W>0 and nonres>=2 and m-1 in K and mag['c_mag']==0
    return data

assert ch.direct(P)==[1,P] and P%840==289
full=[row(P,a,u,True) for a in range(1,27) for u in range(1,26//a+1) if math.gcd(a,u)==1]
assert len(full)==73
positive=[r for r in full if r['W']]
assert [(r['a'],r['u']) for r in positive]==[(1,25),(3,8),(8,1),(11,1)]
expected={(1,25):(1,'1/10','9/10','-9/5','27/10','0'),(3,8):(2,'1','1','-3','4','0'),(8,1):(2,'5/2','-1/2','-3/2','1','1'),(11,1):(1,'4/5','1/5','-2','11/5','0')}
for r in positive:
    assert tuple(str(r[k]) if k!='W' else r[k] for k in ['W','R','C','ell_over_phi','eta','old_c'])==expected[r['a'],r['u']]
assert sum(r['old_c'] for r in full if r['eta']==0)==0
assert sum(r['old_c'] for r in full if r['eta']>0)==1
assert sum(r['W'] for r in full if r['a']*r['u'] in E)==0
Erows=[]
layers=Counter()
for k in E:
    for a in old.divisors(old.factor(k)):
        u=k//a
        if math.gcd(a,u)!=1:continue
        checktime();layers[lam(4*k)//2]+=1
        N,m=a*P+u,4*k
        fs=old.factor(N);ds=old.divisors(fs)
        assert ch.direct(N)==ds and math.prod(q**e for q,e in fs)==N
        assert all(ch.direct(q)==[1,q] for q,e in fs)
        hits=[s for s in ds if s%m==m-1]
        assert len(hits)==counts(fs,m).get(m-1,0)
        Erows.append({'p':P,'a':a,'u':u,'N':N,'m':m,'factors':fs,'W':len(hits),'witnesses':hits})
assert len(Erows)==81 and dict(layers)=={1:9,2:36,3:36}
assert [(r['a'],r['u'],r['witnesses']) for r in Erows if r['W']]==[(14,9,[544319])]

fixed=[]
for p in INPUTS:
    B=(p-1).bit_length()
    for a in range(1,B+1):
        for u in range(1,B//a+1):
            if math.gcd(a,u)==1 and lam(4*a*u)==8:fixed.append(row(p,a,u,True))

dev=[]; total_missed=0; sha=None; cohort_rows=0
if args.development_file:
    sha=hashlib.sha256(args.development_file.read_bytes()).hexdigest();assert sha==EXPECTED_SHA
    with gzip.open(args.development_file,'rt',newline='') as f:
        for record in csv.DictReader(f):
            cohort_rows+=1
            if int(record['in_budget']) and int(record['W'])>0 and Q(record['c'])==0:
                total_missed+=1
                if int(record['L'])!=8:continue
                r=row(int(record['p']),int(record['a']),int(record['u']),len(dev)<20)
                assert r['W']==int(record['W']) and r['eta']==Q(record['eta']) and r['old_c']==0
                dev.append(r)
    assert total_missed==16809 and cohort_rows==587689

def summary(rows):
    return {'rows':len(rows),'W_positive':sum(r['W']>0 for r in rows),'old_positive':sum(r['old_c']>0 for r in rows),
            'new_positive':sum(r['c_mag']>0 for r in rows),'rescued_old_zero':sum(r['rescues_old_zero'] for r in rows),
            'lost_old_positive':sum(r['loses_old_positive'] for r in rows),'fewer_than_two_nonresidue':sum(r['nonresidue_multiplicity']<2 for r in rows),
            'Qmag_counterexamples':sum(r['Qmag_counterexample'] for r in rows)}
counter=next((r for r in fixed+dev if r['Qmag_counterexample']),None)
if counter:
    checked=row(counter['p'],counter['a'],counter['u'],True)
    assert checked==counter
result={'input_counterexample':P,'budget':26,'complete_log_pairs':73,'log_Wtot':sum(r['W'] for r in full),
        'log_successes':positive,'Cert0':'0','Certplus':'1','E_log_Wtot':0,'complete_E_pairs':81,
        'E_all_Wtot':sum(r['W'] for r in Erows),'E_all_successes':[r for r in Erows if r['W']],
        'correct_layer_pair_counts':dict(layers),'fixed_L8_pilot':summary(fixed),'development_L8_old_misses':summary(dev),
        'download_sha256':sha,'development_original_cohort_rows_read':cohort_rows,'development_old_misses_all_L':total_missed,
        'Qmag_status':'Refuted' if counter else 'Unproved','Qmag_counterexample':counter,
        'H_Elog_status':'Refuted at38296729','eta0_only_log_candidate_status':'Refuted at38296729',
        'H_E_unrestricted_status':'Unproved; do not rerun or claim independently reproduced179468 scan',
        'Hlog_or_ESC_proved_or_refuted':False,'independent_holdout':False,'new_prime_range_or_MC_or_Lean':False,
        'norm_validation_rows':norm_validation_rows,'certificate_inputs_only_factors_and_modulus':True,
        'full_W_and_divisor_oracles_forbidden_during_certificate_call':True,
        'seconds':round(time.monotonic()-START,3)}
(RUN/'l8-norm-results.json').write_text(json.dumps(serial(result),indent=2)+'\n')
(RUN/'counterexample73-rows.json').write_text(json.dumps(serial(full),indent=2)+'\n')
(RUN/'counterexample81-E-rows.json').write_text(json.dumps(serial(Erows),indent=2)+'\n')
(RUN/'l8-fixed-rows.json').write_text(json.dumps(serial(fixed),indent=2)+'\n')
fields=['p','a','u','W','R','eta','old_c','T4','raw_lower','c_mag','nonresidue_multiplicity','rescues_old_zero']
with (RUN/'l8-development-results.csv').open('w',newline='') as f:
    writer=csv.DictWriter(f,fieldnames=fields);writer.writeheader()
    for r in dev:writer.writerow({k:str(r[k]) for k in fields})
print(json.dumps(serial({k:v for k,v in result.items() if k not in ['log_successes','Qmag_counterexample']}),indent=2))
print(json.dumps(serial({'Qmag_counterexample':counter,'p38296729_L8_successes':[r for r in fixed if r['p']==P and r['W']>0]}),indent=2))
