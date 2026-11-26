"""Bounded independent audit of Outcasts #85. Standard library only.

Inputs: eight stated exponent-shortage rows for p=100687129; two graph
examples p=100687129,2521. No prime-range expansion or universal inference.
Every factorization is trial division, every equation is exact integer arithmetic.
Exponent minimum DP considers 0 <= f_q < ord_m(q); reducing by the order
preserves residue and cannot increase max(0,f_q-e_q). A second enumeration
over 0 <= f_q <= e_q+delta independently verifies the minimum and ALL minimizers.
Graph: full square sources and all NR factor edges, stop at first actual hit;
queue exhaustion alone is reported as a closed failure set, never a proof of ESC.
"""
import itertools, json, math, time
from collections import deque
from pathlib import Path

P=100687129
ROWS=[(1,15,1,{251:1,1223:2}), (2,7,1,{5:1,17:2,4363:1}),
      (4,5,1,{7:2,191:1}), (19,1,1,{173:2,223:1}),
      (1,13,2,{179:3}), (22,1,2,{13:3,505619:1}),
      (13,2,3,{3:3,53:1,8232281:2}), (20,1,3,{3:3,10357:1,64811:2})]

def factor(n):
    out={}; q=2
    while q*q<=n:
        while n%q==0:
            out[q]=out.get(q,0)+1; n//=q
        q=3 if q==2 else q+2
    if n>1: out[n]=out.get(n,0)+1
    return out

def divisors_from(f):
    ds=[1]
    for q,e in f.items(): ds=[d*q**j for d in ds for j in range(e+1)]
    return sorted(ds)

def chi(a,p):
    k=pow(a%p,(p-1)//2,p)
    assert k in (0,1,p-1)
    return -1 if k==p-1 else k

def order(q,m):
    assert math.gcd(q,m)==1
    r=q%m; k=1
    while r!=1: r=r*q%m; k+=1
    return k

def residue_minimum(f,m):
    dp={1:0}
    for q,e in f.items():
        nd={}
        for r,c in dp.items():
            for k in range(order(q,m)):
                v=r*pow(q,k,m)%m; cost=c+max(0,k-e)
                nd[v]=min(nd.get(v,10**9),cost)
        dp=nd
    return dp.get(m-1),len(dp)

def audit_row(a,u,expected,word):
    N=a*P+u; m=4*a*u; full=factor(N)
    f={q:e for q,e in full.items() if math.gcd(q,m)==1}
    delta,K=residue_minimum(f,m); assert delta==expected
    assert all(q in f for q in word)
    w=math.prod(q**e for q,e in word.items())
    assert w%m==m-1 and sum(max(0,e-f[q]) for q,e in word.items())==delta
    actual=divisors_from(f); S={d%m for d in actual}
    assert m-1 not in S
    qs=list(f); mins=[]; better=[]
    for es in itertools.product(*(range(f[q]+delta+1) for q in qs)):
        cost=sum(max(0,e-f[q]) for q,e in zip(qs,es))
        if cost>delta: continue
        r=math.prod(pow(q,e,m) for q,e in zip(qs,es))%m
        if r!=m-1: continue
        if cost<delta: better.append(es)
        mins.append({'exponents':dict(zip(qs,es)),
                     'extra':{q:e-f[q] for q,e in zip(qs,es) if e>f[q]}})
    assert not better and mins
    return dict(a=a,u=u,N=N,m=m,factors=full,unit_factors=f,K_size=K,S_size=len(S),
                delta=delta,quoted_word=word,all_minimizers=mins)

def square_hit(p,q,t):
    sigma=1 if q%4==3 else 3
    c=sigma*q*t*t
    assert c<3*p and (p+c)%4==0
    x=(p+c)//4; f=factor(x); ds=divisors_from({r:2*e for r,e in f.items()})
    hits=[]
    for branch,target in [('II',-x),('I',-p*x)]:
        for d in ds:
            if (d-target)%c: continue
            if branch=='II': y=p*(d+x)//c; z=p*(x*x//d+x)//c
            else: y=(d+p*x)//c; z=(p*p*(x*x//d)+p*x)//c
            assert min(x,y,z)>0 and 4*x*y*z==p*(x*y+x*z+y*z)
            hits.append(dict(branch=branch,d=d,x=x,y=y,z=z,c=c,q=q,t_square=t))
    return hits,f

def reachable(p):
    assert factor(p)=={p:1}
    ell=next(q for q in range(2,p) if factor(q)=={q:1} and chi(q,p)==-1)
    queue=deque([ell]); seen={ell}; parent={}; checked=[]
    while queue:
        q=queue.popleft(); sigma=1 if q%4==3 else 3
        limit=math.isqrt((3*p-1)//(sigma*q))
        for t in range(1,limit+1,2):
            hits,f=square_hit(p,q,t)
            checked.append([q,t])
            if hits:
                path=[]; r=q
                while r!=ell:
                    prev,tt=parent[r]; path.append([prev,tt,r]); r=prev
                return dict(p=p,least_nonresidue=ell,status='hit_NOT_closed_set',
                            checked_sources=len(checked),source_order=checked,
                            discovered_vertices=sorted(seen),path=list(reversed(path)),hit=hits[0])
            for r in f:
                if chi(r,p)==-1 and r not in seen:
                    assert r<p
                    seen.add(r); parent[r]=(q,t); queue.append(r)
    return dict(p=p,least_nonresidue=ell,status='exhausted_closed_failure_set',
                vertices=sorted(seen),source_order=checked)

def main():
    start=time.monotonic()
    rows=[audit_row(*r) for r in ROWS]
    x=25171795; c=51; d=275; f=factor(x)
    signs=[dict(q=q,e=e,mod_17=chi(q,17),mod_p=chi(q,P)) for q,e in f.items()]
    omega=sum(e for q,e in f.items() if chi(q,P)==-1)
    assert omega==1 and f=={5:1,11:1,457669:1}
    assert x*x%d==0 and (x+d)%c==0 and 4*x==P+c and math.gcd(c,x)==1
    g=math.gcd(x,d); u=d//g; t=x//g; v=g//u
    assert g%u==0 and (u+t)%c==0
    a=(u+t)//c; s=4*a*u*v-1
    assert s*t==a*P+u and (a,u,t,v,s)==(8974,5,457669,11,1974279)
    y=P*(d+x)//c; z=P*(x*x//d+x)//c
    assert (x,y,z)==(25171795,49696146260530,4548877112582100914)
    assert 4*x*y*z==P*(x*y+x*z+y*z)
    # The quoted determinant implication is false without cancellation.
    p,q,a1,u1,a2,u2=2521,3,3,3,1,3
    N1=a1*p+u1; N2=a2*p+u2; D=a2*u1-a1*u2
    assert N1%q==D%q==0 and N2%q!=0
    graph=[reachable(p) for p in (100687129,2521)]
    assert graph[1]['status']=='hit_NOT_closed_set'
    result=dict(scope='two named primes and eight named rows; not a universal theorem',
        rows=rows,square_source=dict(p=P,x=x,c=c,d=d,factors=f,signs=signs,omega_minus_mod_p=omega,
        a=a,u=u,t_cofactor=t,v=v,s=s,au=a*u,y=y,z=z),
        missing_cancellation_counterexample=dict(p=p,q=q,a1=a1,u1=u1,a2=a2,u2=u2,N1=N1,N2=N2,determinant=D),
        graph_replay=graph,seconds=time.monotonic()-start)
    Path('audit-results.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps(result,ensure_ascii=False))

if __name__=='__main__': main()
