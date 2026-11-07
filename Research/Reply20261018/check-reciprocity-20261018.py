import json
import math
import time
from pathlib import Path

ROOT=Path(__file__).resolve().parent
PS=[2521,66529,345601,670849,1740481,3678481,5843041,8615161,18490201,38296729,53722321,84525841]
start=time.monotonic()

def fac(n):
    out=[]
    r=2
    while r*r<=n:
        e=0
        while n%r==0:
            n//=r; e+=1
        if e: out.append((r,e))
        r=3 if r==2 else r+2
    if n>1: out.append((n,1))
    return out

def leg(a,p):
    v=pow(a%p,(p-1)//2,p)
    return -1 if v==p-1 else v

def krprime(a,r):
    if r!=2: return leg(a,r)
    if a%2==0: return 0
    return 1 if a%8 in (1,7) else -1

def divisors(fs,scale=1):
    out=[1]
    for r,e in fs:
        out=[d*r**j for d in out for j in range(scale*e+1)]
    return out

def group(gens,q):
    seen={1}; todo=[1]
    for v in todo:
        for g in gens:
            w=v*g%q
            if w not in seen: seen.add(w); todo.append(w)
    return seen

rows=[]; checks=0; two_checks=0; group_rows=[]
for p in PS:
    assert fac(p)==[(p,1)] and p%840 in (1,121,169,289,361,529)
    for q in range(11,400):
        if fac(q)!=[(q,1)] or leg(q,p)!=-1: continue
        sigma=1 if q%4==3 else 3
        for t in range(1,16,2):
            if time.monotonic()-start>300: raise TimeoutError('300-second contract')
            c=sigma*q*t*t
            if c>=3*p: continue
            x=(p+c)//4
            assert 4*x==p+c and math.gcd(p*x,c)==1 and leg(x,p)==-1
            fs=fac(x)
            for r,e in fs:
                assert leg(r,p)==krprime(-sigma*q,r)
                checks+=1; two_checks+=r==2
            ds=divisors(fs); ds2=divisors(fs,2)
            S={d%c for d in ds}; D2={d%c for d in ds2}
            hitII=(-x)%c in D2; hitI=(-p*x)%c in D2
            assert hitII==bool(S & {(-s)%c for s in S})
            assert hitI==bool(S & {(-p*s)%c for s in S})
            # Second finite-exponent implementation: bounded modular DP.
            dp={1}
            for r,e in fs:
                nxt=set()
                for v in dp:
                    for _ in range(2*e+1):
                        nxt.add(v); v=v*r%c
                dp=nxt
            assert dp==D2
            rec={'p':p,'q':q,'t':t,'sigma':sigma,'c':c,'x':x,'factors':fs,'S':sorted(S),'hit_I':hitI,'hit_II':hitII}
            if sigma==1 and t==1:
                K=group([r%q for r,e in fs],q)
                order_lcm=1
                for r,e in fs:
                    k=1; v=r%q
                    while v!=1: v=v*r%q; k+=1
                    order_lcm=math.lcm(order_lcm,k)
                assert order_lcm==len(K)
                assert leg(x,q)==-1 and (q-1)//2%2==1
                assert (-x)%q in K and q-1 in K
                assert ((-p*x)%q in K) == (4 in K) == (2 in K)
                assert (q-1)//len(K)%2==1
                H2={a*a%q for a in range(1,q)}
                KH2={a*b%q for a in K for b in H2}
                assert (-x)%q in KH2 and (-p*x)%q in KH2
                assert len(S)%2==0 and {x*pow(s,-1,q)%q for s in S}==S
                if not hitII: assert 2*len(S)<=len(K)-2
                rec.update(K=sorted(K),group_I=(-p*x)%q in K,group_II=True,quadratic_I=True,quadratic_II=True)
                group_rows.append(rec)
            rows.append(rec)

summary={'inputs':PS,'sources':len(rows),'factorwise_checks':checks,'factor_two_checks':two_checks,'reciprocity_violations':0,'selector_intersections_and_DP_all_agree':True,'canonical_sigma1_sources':len(group_rows),'canonical_TypeII_failure':sum(not r['hit_II'] for r in group_rows),'canonical_TypeII_group_failure':0,'canonical_TypeI_group_failure':sum(not r['group_I'] for r in group_rows),'canonical_TypeI_group_pass_iff_2_in_K':True,'canonical_quadratic_failure_both_branches':0,'group_BFS_and_order_LCM_agree':True,'failure_cardinality_bound_all_agree':True,'seconds':time.monotonic()-start,'Lean_executed':False}
result={'contract':'reciprocity-contract-20261018.md','summary':summary,'group_I_obstruction_rows':[r for r in group_rows if not r['group_I']],'rows':rows}
(ROOT/'reciprocity-results-20261018.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(summary,ensure_ascii=False))
print(json.dumps({'group_I_obstructions':[{k:r[k] for k in ('p','q','x','factors','S','K')} for r in group_rows if not r['group_I']]},ensure_ascii=False))
