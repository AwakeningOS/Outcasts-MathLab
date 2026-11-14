"""Fixed p30241 audit of #135 and its explicitly uncomputed terminal restriction.

Rebuild all nonresidue-prime vertices and sources, without using the saved
closure as input. Audit both distance tables. Then retain canonical parent
edges AND canonical success terminals, removing vertex367 from the terminal
set. Stop when the finite graph and all three fixed points are exhausted.
No additional prime, search-range extension or universal inference.
"""
from collections import Counter, deque
from fractions import Fraction
from math import isqrt, prod
import json


def prime(n):
    return n>=2 and all(n%d for d in range(2,isqrt(n)+1))


def factors(n):
    fs=[];d=2
    while d*d<=n:
        e=0
        while n%d==0:n//=d;e+=1
        if e:fs.append((d,e))
        d+=1
    if n>1:fs.append((n,1))
    return fs


def divisors(fs):
    ds=[1]
    for r,e in fs:ds=[a*r**b for a in ds for b in range(2*e+1)]
    return sorted(ds)


def analyze(vertices,edges,terminals):
    rev={q:set() for q in vertices}
    for q in vertices:
        for r in edges[q]:rev[r].add(q)
    dist={q:0 for q in terminals};todo=deque(sorted(terminals));next_hop={}
    while todo:
        r=todo.popleft()
        for q in sorted(rev[r]):
            if q not in dist:dist[q]=dist[r]+1;next_hop[q]=r;todo.append(q)
    keep=set(vertices)-set(terminals);rounds=[]
    while True:
        remove={q for q in keep if edges[q]-keep}
        if not remove:break
        rounds.append(sorted(remove));keep-=remove
    assert keep==set(vertices)-set(dist)
    counts=Counter(dist.values())
    assert [len(z) for z in rounds]==[counts[i] for i in range(1,max(counts)+1)]
    def path(q):
        z=[q]
        while z[-1] in next_hop:z.append(next_hop[z[-1]])
        return z
    return dict(terminals=sorted(terminals),unreachable=sorted(keep),
                distances=dict(sorted(dist.items())),counts=dict(sorted(counts.items())),
                max_distance=max(counts),farthest=sorted(q for q,d in dist.items() if d==max(counts)),
                paths={q:path(q) for q in [881,367,23431,24697]})


def main():
    p=30241;assert prime(p) and p%840 in {1,121,169,289,361,529}
    vs=[q for q in range(3,p) if prime(q) and pow(q,(p-1)//2,p)==p-1]
    nr=set(vs);full={q:set() for q in vs};canon={q:set() for q in vs};good=set();good1=set();rows={}
    for q in vs:
        sigma=1 if q%4==3 else 3;rows[q]=[];t=1
        while sigma*q*t*t<3*p:
            c=sigma*q*t*t;x=(p+c)//4;assert 4*x==p+c
            fs=factors(x);assert prod(r**e for r,e in fs)==x
            children={r for r,e in fs if r in nr};assert children and q not in children
            full[q]|=children
            if t==1:canon[q]|=children
            ds=divisors(fs);hits={b:[d for d in ds if (d+k*x)%c==0] for b,k in [('I',p),('II',1)]}
            cert=[]
            for b,ks in hits.items():
                for d in ks:
                    D=d if b=='I' else p*d;S=(p*x)**2//D
                    assert D*S==(p*x)**2 and (D+p*x)%c==0 and (S+p*x)%c==0
                    den=[x,(D+p*x)//c,(S+p*x)//c]
                    assert all(z>0 for z in den) and sum(Fraction(1,z) for z in den)==Fraction(4,p)
                    cert.append(dict(branch=b,d=d,denominators=den))
            if cert:
                good.add(q)
                if t==1:good1.add(q)
            rows[q].append(dict(tau=t,c=c,x=x,factors=fs,children=sorted(children),certificates=cert));t+=2
    a=analyze(vs,full,good);b=analyze(vs,canon,good);z=analyze(vs,canon,good1)
    assert len(vs)==1623 and sum(map(len,rows.values()))==2721
    assert a['counts']=={0:11,1:377,2:804,3:334,4:74,5:22,6:1}
    assert a['farthest']==[24697] and b['max_distance']==16 and b['farthest']==[23431]
    assert {i:b['counts'][i] for i in range(7)}=={0:11,1:284,2:206,3:161,4:266,5:162,6:159}
    assert sum(n for k,n in b['counts'].items() if 7<=k<=16)==374
    assert good-good1=={367}
    print(json.dumps(dict(p=p,vertices=len(vs),sources=sum(map(len,rows.values())),
                         full_edges_all_terminals=a,canonical_edges_all_terminals=b,
                         canonical_edges_canonical_terminals=z,all_sources=rows),indent=2))


if __name__=='__main__':main()
