"""Audit the p=30241 claim in Outcasts #126 and locate integer-ratio terminals.

Fixed input p=30241 only. Enumerate the full square-source closure from the
least prime nonresidue; stop at queue exhaustion. At canonical sources classify
integer-ratio Type I, general Type I, and Type II using actual divisors. Then
test integer-ratio terminals among ALL prime-nonresidue vertices r<p, to separate
an empty terminal family from a reachability obstruction. No prime-range scan.
"""
from collections import Counter, deque
from fractions import Fraction
from math import gcd, isqrt, prod
import json


def factor(n):
    fs = []
    r = 2
    while r*r <= n:
        e = 0
        while n % r == 0:
            n //= r
            e += 1
        if e:
            fs.append((r,e))
        r = 3 if r == 2 else r+2
    if n > 1:
        fs.append((n,1))
    return fs


def divisors(fs, multiple=1):
    ds = [1]
    for r,e in fs:
        ds = [d*r**j for d in ds for j in range(multiple*e+1)]
    return sorted(ds)


def primes_below(n):
    sieve=bytearray(b'\x01')*n
    sieve[0:2]=b'\x00\x00'
    for q in range(2,isqrt(n-1)+1):
        if sieve[q]:
            sieve[q*q:n:q]=b'\x00'*len(range(q*q,n,q))
    return [q for q in range(2,n) if sieve[q]]


def nr(p,q):
    return pow(q,(p-1)//2,p)==p-1


def sigma(q):
    return 1 if q%4==3 else 3


def canonical(p,r):
    c=sigma(r)*r
    y=(p+c)//4
    fs=factor(y)
    assert 4*y==p+c and gcd(c,y)==gcd(c,p)==1
    hs=[h for h in divisors(fs) if (p+h)%c==0]
    # A separate finite enumeration through a congruence progression.
    congruence_hs=[h for h in range((-p)%c,y+1,c) if h>0 and y%h==0]
    assert hs==congruence_hs
    hits={b:[d for d in divisors(fs,2) if (d+k*y)%c==0]
          for b,k in [('I',p),('II',1)]}
    cert=[]
    for b,ds in hits.items():
        for d in ds:
            # Original factor-pair test, with both divisibilities retained.
            D=d if b=='I' else p*d
            S=(p*y)**2//D
            assert D*S==(p*y)**2 and (D+p*y)%c==0 and (S+p*y)%c==0
            den=[y,(D+p*y)//c,(S+p*y)//c]
            assert sum(Fraction(1,z) for z in den)==Fraction(4,p)
            g=gcd(d,y)
            cert.append(dict(branch=b,d=d,h=d//g,m=y//g,denominators=den))
    assert hs==[z['h'] for z in cert if z['branch']=='I' and z['m']==1]
    return dict(r=r,c=c,y=y,factors=fs,integer_h=hs,hits=hits,certificates=cert)


def source_rows(p,q):
    A=sigma(q)*q
    upper=isqrt((3*p-1)//A)
    for t in range(1,upper+1,2):
        c=A*t*t;x=(p+c)//4;fs=factor(x)
        assert 4*x==p+c and c<3*p and x<p and nr(p,x)
        assert prod(r**e for r,e in fs)==x
        children=[r for r,e in fs if nr(p,r)]
        assert children and q not in children
        yield dict(q=q,tau=t,c=c,x=x,factors=fs,children=children)


def main():
    p=30241
    assert factor(p)==[(p,1)] and p%840 in [1,121,169,289,361,529]
    vertices=[r for r in primes_below(p) if nr(p,r)]
    root=min(vertices);assert root==11
    queue=deque([root]);depth={root:0};parent={root:None};rows={}
    while queue:
        q=queue.popleft()
        rows[q]=list(source_rows(p,q))
        for s in rows[q]:
            for r in s['children']:
                if r not in depth:
                    depth[r]=depth[q]+1
                    parent[r]=dict(q=q,tau=s['tau'])
                    queue.append(r)
    assert all(r in depth for group in rows.values() for s in group for r in s['children'])
    records={r:canonical(p,r) for r in vertices}
    layers=[]
    for level in range(max(depth.values())+1):
        vs=sorted(r for r,d in depth.items() if d==level)
        layers.append(dict(depth=level,vertices=vs,source_count=sum(len(rows[r]) for r in vs),
                           integer_terminals=[r for r in vs if records[r]['integer_h']],
                           type_I_terminals=[r for r in vs if records[r]['hits']['I']],
                           type_II_terminals=[r for r in vs if records[r]['hits']['II']]))
    whole_integer=[r for r in vertices if records[r]['integer_h']]
    # Independent parameter direction: h rather than vertex r.
    # If y=h*z and p+h=k*c, then h(4z+1)=(k+1)c.
    # gcd(h,c)=1 implies k+1=h*s and c*s=4z+1. Since c=3 mod4,
    # s=3 mod4 and s>=3. Thus h<=(p+c)/(3c-1)<=(p+11)/32.
    h_bound=(p+11)//32
    shifted_hits=[]
    shifted_checks=[]
    for h in range(1,h_bound+1):
        fs=factor(p+h)
        candidates=[]
        for r,e in fs:
            if r>=p or not nr(p,r):
                continue
            c=sigma(r)*r
            if (p+h)%c==0:
                candidates.append(dict(r=r,c=c,p_plus_c_mod_4h=(p+c)%(4*h)))
                if (p+c)%(4*h)==0:
                    shifted_hits.append(dict(r=r,h=h))
        shifted_checks.append(dict(h=h,factors_p_plus_h=fs,candidates=candidates))
    assert sorted((t['r'],t['h']) for t in shifted_hits)==sorted(
        (r,h) for r in whole_integer for h in records[r]['integer_h'])
    out=dict(p=p,root=root,all_nonresidue_vertices=vertices,
             total_nonresidue_vertices=len(vertices),reachable_vertices=len(depth),
             reachable_sources=sum(map(len,rows.values())),max_first_arrival_depth=max(depth.values()),
             layers=layers,parents=parent,sources=rows,
             canonical_reachable={r:records[r] for r in sorted(depth)},
             whole_graph_integer_terminals=[records[r] for r in whole_integer],
             reached_integer_terminals=[r for r in whole_integer if r in depth],
             unreachable_integer_terminals=[r for r in whole_integer if r not in depth],
             shifted_parameter_check=dict(h_bound=h_bound,hits=shifted_hits,rows=shifted_checks))
    print(json.dumps(out,indent=2))


if __name__=='__main__':
    main()
