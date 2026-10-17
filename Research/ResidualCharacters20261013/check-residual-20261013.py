import functools
import hashlib
import importlib.util
import itertools
import json
import math
import time
from fractions import Fraction as Q
from pathlib import Path

run=Path('/mnt/hdd1t/outcasts-reply-20261013-ks9Uhb')
helper=Path('/mnt/hdd1t/outcasts-reply-20261010-DnoRad/test-kneser-budget-20261010.py')
spec=importlib.util.spec_from_file_location('old',helper)
old=importlib.util.module_from_spec(spec); spec.loader.exec_module(old)
start=time.monotonic()
def checktime(): assert time.monotonic()-start<120
def phi(n):
    r=n
    for q,e in old.factor(n): r=r//q*(q-1)
    return r
def jacobi(a,n):
    assert n>0 and n%2==1
    a%=n; sign=1
    while a:
        while a%2==0:
            a//=2
            if n%8 in (3,5): sign=-sign
        a,n=n,a
        if a%4==n%4==3: sign=-sign
        a%=n
    return sign if n==1 else 0
def direct(n):
    out=set()
    for k in range(1,math.isqrt(n)+1):
        if n%k==0: out.update((k,n//k))
    return sorted(out)
def trim(p):
    p=list(p)
    while len(p)>1 and p[-1]==0: p.pop()
    return p
def divide(p,q):
    p=trim(p); q=trim(q); out=[0]*max(1,len(p)-len(q)+1)
    while len(p)>=len(q) and p!=[0]:
        assert p[-1]%q[-1]==0
        c=p[-1]//q[-1]; k=len(p)-len(q); out[k]+=c
        for j,x in enumerate(q): p[j+k]-=c*x
        p=trim(p)
    return trim(out),p
@functools.lru_cache(None)
def cyclo(n):
    p=[-1]+[0]*(n-1)+[1]
    for d in range(1,n):
        if n%d==0:
            p,rem=divide(p,cyclo(d)); assert rem==[0]
    return tuple(p)
def reduce(p,L): return divide(p,cyclo(L))[1]
def cyclic_mul(p,q,L):
    out=[0]*L
    for i,x in enumerate(p):
        if x:
            for j,y in enumerate(q):
                if y: out[(i+j)%L]+=x*y
    return out
def add(p,q):
    out=[0]*max(len(p),len(q))
    for i,x in enumerate(p): out[i]+=x
    for i,x in enumerate(q): out[i]+=x
    return trim(out)
@functools.lru_cache(None)
def character_data(m):
    blocks=[]; orders=[]
    for q,e in old.factor(m):
        n=q**e
        if q==2:
            if e==1: blocks.append((n,{1:()},0))
            elif e==2:
                blocks.append((n,{1:(0,),3:(1,)},1)); orders.append(2)
            else:
                k=2**(e-2)
                coords={((-1)**b*pow(5,j,n))%n:(b,j) for b in range(2) for j in range(k)}
                assert len(coords)==phi(n)
                blocks.append((n,coords,2)); orders.extend((2,k))
        else:
            ph=phi(n); primes=[r for r,e2 in old.factor(ph)]
            g=next(g for g in range(2,n) if math.gcd(g,n)==1 and all(pow(g,ph//r,n)!=1 for r in primes))
            coords={pow(g,j,n):(j,) for j in range(ph)}
            assert len(coords)==ph
            blocks.append((n,coords,1)); orders.append(ph)
    units=[r for r in range(1,m) if math.gcd(r,m)==1]
    coords={r:sum((b[1][r%b[0]] for b in blocks),()) for r in units}
    assert len(set(coords.values()))==phi(m)==math.prod(orders)
    L=math.lcm(*orders)
    chars=[]
    for param in itertools.product(*(range(o) for o in orders)):
        phases={r:sum(t*j*(L//o) for t,j,o in zip(param,coords[r],orders))%L for r in units}
        target=phases[m-1]
        assert target in (0,L//2)
        real=all(k in (0,L//2) for k in phases.values())
        # Check the constructed functions, not just their count.
        assert all(phases[r*s%m]==(phases[r]+phases[s])%L for r in units for s in units)
        chars.append({'param':param,'phases':phases,'sign':1 if target==0 else -1,'real':real})
    assert len(chars)==phi(m)
    assert len({tuple(c['phases'][r] for r in units) for c in chars})==phi(m)
    return L,tuple(chars)
def factor_certificate(p,a,u):
    N=a*p+u; m=4*a*u; ph=phi(m); fs=old.factor(N)
    assert math.prod(q**e for q,e in fs)==N and math.gcd(N,a*u)==1
    odd=[(q,e) for q,e in fs if q!=2]; tau=math.prod(e+1 for q,e in odd)
    L,chars=character_data(m)
    distinguished=next(c['param'] for c in chars if all((1 if c['phases'][r]==0 else -1 if c['phases'][r]==L//2 else 0)==jacobi(-a*u,r) for r in range(1,m) if math.gcd(r,m)==1))
    assert next(c['sign'] for c in chars if c['param']==distinguished)==-1
    terms=[]
    for c in chars:
        poly=[1]+[0]*(L-1)
        for q,e in odd:
            exponent=c['phases'][q%m]
            local=[0]*L
            for j in range(e+1): local[j*exponent%L]+=1
            poly=cyclic_mul(poly,local,L)
        term=dict(c); term['poly']=reduce(poly,L); terms.append(term)
    principal=tuple(0 for x in distinguished)
    lookup={t['param']:t for t in terms}
    assert lookup[principal]['poly']==[tau]
    tnum=lookup[distinguished]['poly'][0]
    assert lookup[distinguished]['poly']==[tnum] and 0<=tnum<=tau
    for q,e in odd:
        leg=1 if pow(p%q,(q-1)//2,q)==1 else -1
        assert leg==jacobi(-a*u,q)
    even=sum(t['poly'][0] for t in terms if t['real'] and t['sign']==1 and t['param']!=principal)
    oddrest=sum(t['poly'][0] for t in terms if t['real'] and t['sign']==-1 and t['param']!=distinguished)
    assert all(len(t['poly'])==1 and t['poly'][0]>=0 for t in terms if t['real'])
    seen=set(); cp=[]; complexpoly=[0]; complexlower=0
    for t in terms:
        if t['real'] or t['param'] in seen: continue
        other=next(z for z in terms if all(z['phases'][r]==(-t['phases'][r])%L for r in t['phases']))
        seen.update((t['param'],other['param']))
        pair=reduce(add(t['poly'],other['poly']),L)
        pair=[t['sign']*k for k in pair]
        low=pair[0] if len(pair)==1 else -sum(abs(k) for k in pair)
        complexlower+=low; complexpoly=add(complexpoly,pair)
        cp.append({'param':t['param'],'conjugate':other['param'],'target_sign':t['sign'],'signed_pair_poly':pair,'certified_lower_numerator':low})
    complexpoly=reduce(complexpoly,L)
    assert len(complexpoly)==1
    U=Q(tau,ph); t=Q(tnum,ph); V=U-t
    signedreal=Q(even-oddrest,ph); signedcomplex=Q(complexpoly[0],ph)
    lower_remainder=signedreal+Q(complexlower,ph)
    # W-free upper bound, including nonnegative W only as a universal fact.
    K=min(V,max(Q(0),-lower_remainder))
    lower=max(Q(0),V+lower_remainder)
    assert K>=0 and lower>=V-K
    character_count=Q(tau-tnum+even-oddrest+complexpoly[0],ph)
    assert character_count.denominator==1
    info={'p':p,'a':a,'u':u,'N':N,'m':m,'phi':ph,'factors':fs,'root_order':L,'tau_odd':tau,'distinguished_param':distinguished,'U':U,'t':t,'V':V,'other_even_real':Q(even,ph),'other_odd_real':Q(oddrest,ph),'signed_complex':signedcomplex,'complex_triangle_lower':Q(complexlower,ph),'factor_only_K':K,'factor_only_W_lower':lower,'factor_character_count':int(character_count),'complex_pairs':cp,'real_terms':[{'param':z['param'],'sign':z['sign'],'F':z['poly'][0],'distinguished':z['param']==distinguished,'prime_phases':[[q,z['phases'][q%m],e] for q,e in odd]} for z in terms if z['real']]}
    return info
def audit_pair(p,a,u):
    r=factor_certificate(p,a,u)
    ds=direct(r['N']); assert ds==old.divisors(r['factors'])
    witnesses=[s for s in ds if (s+1)%r['m']==0]
    W=len(witnesses); assert W==r['factor_character_count']
    U,t,V=r['U'],r['t'],r['V']
    negative=max(Q(0),U-W); plus=max(Q(0),W-U)
    clipped=min(t,negative); rest=negative-clipped; delta=t-clipped
    assert rest==max(Q(0),V-W)
    assert 0<=rest<=r['factor_only_K']<=V
    correct=U-t-rest+plus+delta
    wrong=U-t-rest+plus
    assert correct==W and W>=wrong
    r.update({'W':W,'witnesses':witnesses,'Eplus':plus,'Eminus':negative,'clipped_character':clipped,'rest':rest,'delta':delta,'stated_without_delta':wrong,'stated_equality_holds':wrong==W,'correct_equality_holds':True})
    return r
rows=[]; summaries=[]
for p in [66529,18490201]:
    assert direct(p)==[1,p] and p%840 in {1,121,169,289,361,529}
    B=(p-1).bit_length(); data=[]
    for a in range(1,B+1):
        for u in range(1,B//a+1):
            if math.gcd(a,u)!=1: continue
            checktime(); data.append(audit_pair(p,a,u))
    sums={k:sum((r[k] for r in data),Q(0)) for k in ['U','t','V','W','Eplus','Eminus','clipped_character','rest','delta','stated_without_delta','factor_only_K','factor_only_W_lower','other_even_real','other_odd_real','signed_complex']}
    assert sums['W']==sums['V']-sums['rest']+sums['Eplus']+sums['delta']
    summaries.append({'p':p,'B':B,'pairs':len(data),'sums':sums,'without_delta_equal':sums['delta']==0,'factor_certificate_positive':sums['factor_only_W_lower']>0,'positive_certificate_pairs':[[r['a'],r['u']] for r in data if r['factor_only_W_lower']>0],'actual_success_pairs':sum(r['W']>0 for r in data),'nonzero_delta_pairs':sum(r['delta']>0 for r in data),'max_rest_pair':[max(data,key=lambda r:r['rest'])['a'],max(data,key=lambda r:r['rest'])['u']]})
    rows.extend(data)
sharp=audit_pair(1201,3,1)
assert sharp['W']==0 and sharp['t']==0 and sharp['rest']==sharp['V']==1
result={'contract':'residual-audit-contract-20261013.md','fixed_complete_inputs':[66529,18490201],'summaries':summaries,'sharpness_pair':sharp,'all_divisor_and_exact_character_methods_match':True,'factor_certificate_uses_W_as_input':False,'general_existence_proved':False,'new_ESC_range_scan':False,'full28802_census_replayed':False,'seconds':round(time.monotonic()-start,3),'helper_sha256':hashlib.sha256(helper.read_bytes()).hexdigest()}
def serial(x):
    if isinstance(x,Q): return str(x)
    if isinstance(x,dict): return {k:serial(v) for k,v in x.items()}
    if isinstance(x,(list,tuple)): return [serial(v) for v in x]
    return x
(run/'residual-audit-results.json').write_text(json.dumps(serial(result),indent=2)+'\n')
(run/'residual-audit-rows.json').write_text(json.dumps(serial(rows),indent=2)+'\n')
print(json.dumps(serial({k:v for k,v in result.items() if k!='sharpness_pair'}),indent=2))
print(json.dumps(serial({'sharpness_pair':sharp}),indent=2))
