"""Independent fixed-input audit; no imports from participant implementations."""
import hashlib
import json
import math
import time
from pathlib import Path

r=Path(__file__).resolve().parent
start=time.monotonic()
def budget():
    assert time.monotonic()-start<30
def factors(n):
    out=[]
    q=2
    while q*q<=n:
        e=0
        while n%q==0:
            n//=q;e+=1
        if e:out.append((q,e))
        q=3 if q==2 else q+2
    if n>1:out.append((n,1))
    return out
def divs(f):
    out=[(1,[])]
    for g,e in f:
        out=[(d*g**j,ks+[j-e]) for d,ks in out for j in range(2*e+1)]
    return sorted(out)
def group(f,m):
    K={1};todo=[1]
    for a in todo:
        budget()
        for g,e in f:
            b=a*g%m
            if b not in K:K.add(b);todo.append(b)
    return K
def source(p,q,tau):
    c=3*q*tau*tau
    assert (p+c)%4==0 and c<3*p
    x=(p+c)//4
    assert 0<x<p and math.gcd(x,c)==1
    f=factors(x)
    assert math.prod(g**e for g,e in f)==x
    R=math.prod(g for g,e in factors(c))
    return c,x,f,R

for p,q in [(42698041,41),(8615161,17)]:
    assert factors(p)==[(p,1)] and factors(q)==[(q,1)]
    assert p%24==1 and pow(q,(p-1)//2,p)==p-1

vary=[]
for tau in (3,27):
    p=42698041;q=41
    c,x,f,R=source(p,q,tau)
    kr=group(f,R);kc=group(f,c)
    assert ((-1)%R in kr)==((-1)%c in kc)
    ds=divs(f)
    vary.append(dict(p=p,q=q,tau=tau,rad_tau=math.prod(g for g,e in factors(tau)),c=c,x=x,
                     factors=f,R=R,K_R_size=len(kr),K_c_size=len(kc),
                     TypeII_group_pass=(-x)%c in kc,TypeI_group_pass=(-p*x)%c in kc,
                     actual_TypeI_rad=[d for d,z in ds if (d+p*x)%R==0],
                     actual_TypeI_full=[d for d,z in ds if (d+p*x)%c==0]))
assert vary[0]['rad_tau']==vary[1]['rad_tau']==3
assert not vary[0]['TypeII_group_pass'] and vary[1]['TypeII_group_pass']

p=8615161;q=17;examined=0;worked=None
for tau in range(1,1000,2):
    budget()
    c=3*q*tau*tau
    if 3*c>p+4:break
    c,x,f,R=source(p,q,tau);examined+=1
    ds=divs(f)
    radical_hits=[(d,z) for d,z in ds if (d+x)%R==0]
    full_hits=[d for d,z in ds if (d+x)%c==0]
    if not radical_hits or full_hits:continue
    lifts=[]
    for d,z in radical_hits:
        a=d*pow(x,-1,c)%c
        b=(-a)%c
        assert b%R==1
        h=c//R
        assert h%2==1 and pow(b,h,c)==1
        s=1;v=b
        while v!=1:
            v=v*b%c;s+=1;budget()
            assert s<=h
        assert s%2==1 and h%s==0 and pow(a,s,c)==c-1
        proposed=[e+s*k for (g,e),k in zip(f,z)]
        within=all(0<=j<=2*e for (g,e),j in zip(f,proposed))
        assert not within
        lifts.append(dict(d=d,z=z,a=a,kernel_element=b,s=s,h=h,
                          exponent_budget=[e for g,e in f],proposed_exponents=proposed,within_budget=within))
    worked=dict(p=p,q=q,tau=tau,c=c,x=x,factors=f,R=R,all_divisors_count=len(ds),
                full_hits=full_hits,radical_hits=lifts,divisors=[d for d,z in ds])
    break
assert worked is not None

p=1201;x=306;c=23;d=108
g=math.gcd(d,x)
assert x*x%d==0 and (d+x)%c==0
assert (d+x)>x+1 and (d+x)//g<=x+1
size=dict(p=p,x=x,c=c,d=d,gcd=g,unreduced=(d+x)//c,reduced=(d+x)//(c*g),bound_numerator=x+1,bound_denominator=c)
result=dict(varying_tau=vary,worked_lift=worked,source_candidates_examined=examined,size_parameter=size,
            seconds=time.monotonic()-start,code_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            peer_code_executed=False,Lean_executed=False,new_prime_scan=False)
(r/'radical-lift-audit-results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
