"""Algebraically constructed projection-gap test, separate from fixed280009 audit.

Set r73, x'=145h and p580h-219; use h=43mod438 so r has fixed character
and all square-divisor residue pairs mod(3,73) are fixed if h is prime.
Exact trial candidates already selected algebraically:43,2671,3109.
43 gives composite p24721;2671 is the first tested admissible prime pair.
Audit p1548961 only in detail, with incoming least-root11 source tau3.
No assertion that the whole root11 fails; audit only that incoming source.
"""
import hashlib,itertools,json,math,time
from pathlib import Path
run=Path(__file__).resolve().parent
start=time.perf_counter()
def factor(n):
    out=[];d=2
    while d*d<=n:
        e=0
        while n%d==0:n//=d;e+=1
        if e:out.append((d,e))
        d=3 if d==2 else d+2
    if n>1:out.append((n,1))
    return out
def source(p,q,t):
    c=(1 if q%4==3 else 3)*q*t*t;x=(p+c)//4
    assert c<3*p and t%2 and (p+c)%4==0 and math.gcd(x,c)==1
    f=factor(x);ds=[1]
    for g,e in f:ds=[d*g**k for d in ds for k in range(2*e+1)]
    ds=sorted(ds)
    return dict(q=q,tau=t,c=c,x=x,factors=f,divisors=ds,
                hitsI=[d for d in ds if (d+p*x)%c==0],
                hitsII=[d for d in ds if (d+x)%c==0])
trials=[dict(h=h,h_factors=factor(h),p=580*h-219,p_factors=factor(580*h-219))
        for h in (43,2671,3109)]
assert trials[0]['p_factors']==[(59,1),(419,1)]
h=2671;p=580*h-219;r=73
assert p==1548961 and p%840==1
assert factor(p)==[(p,1)] and factor(h)==[(h,1)]
assert h%438==43 and pow(r,(p-1)//2,p)==p-1
assert all(pow(g,(p-1)//2,p)==1 for g in (2,3,5,7))
assert pow(11,(p-1)//2,p)==p-1
parent=source(p,11,3);child=source(p,r,1)
assert parent['x']%r==0 and not child['x']%r==0
assert child['x']==145*h and child['factors']==[(5,1),(29,1),(2671,1)]
assert not parent['hitsI'] and not parent['hitsII']
assert not child['hitsI'] and not child['hitsII']
modr=[d for d in child['divisors'] if (d+child['x'])%r==0]
mod3=[d for d in child['divisors'] if (d+child['x'])%3==0]
assert len(modr)==2 and len(mod3)==12 and not set(modr)&set(mod3)
assert modr==[h,h*145**2] and all(d%3==1 for d in modr)
for src in (parent,child):
    x=src['x'];direct=[]
    for d in range(1,x+1):
        if x*x%d==0:
            direct.append(d)
            if d!=x:direct.append(x*x//d)
    assert sorted(direct)==src['divisors']
    src['independent_divisor_comparison']=True
    src['nonresidue_factors']=[(g,e) for g,e in src['factors'] if pow(g,(p-1)//2,p)==p-1]
assert parent['c']*pow(4,-1,r)%r==(-child['x'])%r
residue_rows=[dict(exponents=[a,b,c],d=5**a*29**b*h**c,
                   mod73=(5**a*29**b*h**c)%73,mod3=(5**a*29**b*h**c)%3)
              for a,b,c in itertools.product(range(3),repeat=3)]
result=dict(p=p,h=h,r=r,trials=trials,parent=parent,child=child,
            target_mod73=(-child['x'])%73,target_mod3=(-child['x'])%3,
            target_fullII=(-child['x'])%219,target_fullI=(-p*child['x'])%219,
            hits_mod73=modr,hits_mod3=mod3,residue_rows=residue_rows,
            gcd_parent_child=math.gcd(parent['x'],child['x']),
            refuted_candidate='for an incoming edge from a both-failed source, separate TypeII divisor hits modr and mod3 imply a full hit mod3r',
            all_parent_sources_failed_claimed=False,original_root_failed_shortcut_refuted=False,
            seconds=time.perf_counter()-start,CPU_host='mini',CPU_processes=1,
            Lean_executed=False,global_proof=False,prime_range_scan=False,
            code_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
(run/'constructed-transfer-results-20261104.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='residue_rows'},indent=2))
