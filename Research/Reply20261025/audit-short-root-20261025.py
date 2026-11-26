"""Fixed p=2521 falsification of the sufficient-bound-only child strategy.

Contract fixed before this execution: no target-prime range scan. Compute all
root sources, all their distinct nonresidue-prime children, and all allowed
sources at those children, retaining every divisor of x^2. Independently
characterize root edges by the least positive odd modular root. Refute the
restricted existence claim iff the root fails, some full child succeeds, but
every child guaranteed by A*(r-2)^2 < 3*p fails at all its allowed sources.
Validate the 12 published success certificates, not their complete BFS runs.
"""
import json,math,time
from pathlib import Path

def factor(n):
    f={};q=2
    while q*q<=n:
        while n%q==0:f[q]=f.get(q,0)+1;n//=q
        q=3 if q==2 else q+2
    if n>1:f[n]=f.get(n,0)+1
    return f
def divisors(f):
    d=[1]
    for q,e in f.items():d=[a*q**j for a in d for j in range(e+1)]
    return sorted(d)
def chi(a,p):
    k=pow(a%p,(p-1)//2,p)
    assert k in (0,1,p-1)
    return -1 if k==p-1 else k
def sigma(q):return 1 if q%4==3 else 3
def source(p,q,t):
    c=sigma(q)*q*t*t;assert c<3*p and (p+c)%4==0
    x=(p+c)//4;f=factor(x)
    assert math.prod(r**e for r,e in f.items())==x and math.gcd(c,x)==1
    ds=divisors({r:2*e for r,e in f.items()})
    hits={b:[d for d in ds if (d+k*x)%c==0] for b,k in [('I',p),('II',1)]}
    # Separate modular DP retaining exponents, not subgroup closure.
    residues={1%c}
    for r,e in f.items():residues={a*pow(r,j,c)%c for a in residues for j in range(2*e+1)}
    assert set(d%c for d in ds)==residues
    assert bool(hits['I'])==((-p*x)%c in residues)
    assert bool(hits['II'])==((-x)%c in residues)
    return dict(q=q,tau=t,c=c,x=x,factors=f,divisor_count=len(ds),residues=sorted(residues),hits=hits,children=sorted(r for r in f if chi(r,p)==-1))
def sources(p,q):return [source(p,q,t) for t in range(1,math.isqrt((3*p-1)//(sigma(q)*q))+1,2)]
def success(row):return bool(row['hits']['I'] or row['hits']['II'])

def main():
    start=time.monotonic();outdir=Path(__file__).resolve().parent
    p=2521;q=11;A=11;assert factor(p)=={p:1}
    root=sources(p,q);assert len(root)==13 and not any(map(success,root))
    children=sorted({r for row in root for r in row['children']})
    all_child_rows={r:sources(p,r) for r in children}
    good=[r for r,rows in all_child_rows.items() if any(map(success,rows))]
    forced=[r for r in children if A*(r-2)**2<3*p]
    prime_rows=[]
    for r in range(3,p,2):
        if factor(r)!={r:1} or chi(r,p)!=-1 or A%r==0:continue
        roots=[t for t in range(1,r) if (p+A*t*t)%r==0]
        # QR reciprocity predicts root existence exactly under NR(r|p).
        assert bool(roots)==(chi(-A,r)==-1)
        odd=[t for t in roots if t%2==1]
        assert len(odd)==int(bool(roots))
        beta=odd[0] if odd else None
        exact=bool(odd) and A*beta*beta<3*p
        assert exact==(r in children)
        sufficient=bool(odd) and A*(r-2)**2<3*p
        assert not sufficient or exact
        prime_rows.append(dict(r=r,legendre_minus_A=chi(-A,r),roots=roots,beta=beta,exact_edge=exact,sufficient_edge=sufficient))
    assert sorted(z['r'] for z in prime_rows if z['sufficient_edge'])==forced
    assert good==[29] and forced==[17,19]
    assert not any(success(row) for r in forced for row in all_child_rows[r])
    only=next(z for z in prime_rows if z['r']==29)
    assert only['roots']==[4,25] and only['beta']==25
    assert A*25*25==6875<3*p==7563<A*(29-2)**2==8019
    # Read published certificates only after the independently generated result.
    participant=json.loads((outdir/'participant-evidence/bfs12_results.json').read_text())
    certificate_checks=[]
    for v in participant['inputs']:
        n=v['p'];h=v['bfs']['hit'];x,y,z=h['x'],h['y'],h['z'];c,d=h['c'],h['d']
        assert factor(n)=={n:1} and n%840 in {1,121,169,289,361,529}
        assert c==sigma(h['q'])*h['q']*h['tau']**2==4*x-n and 0<c<3*n
        assert min(x,y,z)>0 and x*x%d==0 and math.gcd(c,x)==1
        if h['branch']=='I':
            assert (d+n*x)%c==0 and y==(d+n*x)//c and z==(n*n*(x*x//d)+n*x)//c
        else:
            assert h['branch']=='II' and (d+x)%c==0 and y==n*((d+x)//c) and z==n*((x*x//d+x)//c)
        assert 4*x*y*z==n*(x*y+x*z+y*z)
        certificate_checks.append(dict(p=n,certificate_valid=True,bfs_depth_reported=v['bfs']['D'],BFS_reexecuted=False))
    result=dict(p=p,root_q=q,A=A,root_rows=root,children=children,child_rows=all_child_rows,good_children=good,
        sufficient_bound_children=forced,sufficient_bound_successes=[],prime_root_checks=prime_rows,
        restricted_candidate_refuted=True,E1_refuted=False,Qleast_square_refuted=False,
        twelve_certificate_checks=certificate_checks,Lean_executed=False,new_prime_range_scan=False,seconds=time.monotonic()-start)
    (outdir/'short-root-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['p','root_q','children','good_children','sufficient_bound_children','restricted_candidate_refuted','E1_refuted','seconds']}))
    print(json.dumps({'root_count':len(root),'child_source_counts':{r:len(rows) for r,rows in all_child_rows.items()},'prime_root_checks':len(prime_rows),'certificate_checks':len(certificate_checks),'good_child_hits':[row for row in all_child_rows[29] if success(row)]}))
if __name__=='__main__':main()
