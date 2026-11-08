"""Fixed-input audit of post 124: rational witnesses and depth-two reachability.

Scope: p=280009 only for the graph. Exhaust all root sources and all 59
direct-child canonical integer-ratio tests. Then visit parents in ascending
order, odd tau ascending, factors ascending; stop at the first *new* depth-two
vertex with a canonical integer-ratio Type I witness, or exhaust that layer.
Also check the canonical source at (p,r)=(1548961,11). No universal inference.
Standard-library integer arithmetic; Fraction checks the final decompositions.
"""
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


def divisors(fs, multiplier=1):
    out = [1]
    for r,e in fs:
        out = [d*r**j for d in out for j in range(multiplier*e+1)]
    return sorted(out)


def nr(p,r):
    return pow(r,(p-1)//2,p) == p-1


def sigma(r):
    return 1 if r % 4 == 3 else 3


def source(p,q,tau):
    c = sigma(q)*q*tau*tau
    assert tau > 0 and tau % 2 == 1 and c < 3*p
    assert (p+c) % 4 == 0
    x = (p+c)//4
    fs = factor(x)
    assert prod(r**e for r,e in fs) == x
    children = [r for r,_ in fs if nr(p,r)]
    assert nr(p,x) and children
    return dict(q=q,tau=tau,c=c,x=x,factors=fs,children=children)


def sources(p,q):
    bound = isqrt((3*p-1)//(sigma(q)*q))
    for tau in range(1,bound+1,2):
        yield source(p,q,tau)


def canonical(p,r):
    s = source(p,r,1)
    y,c = s['x'],s['c']
    assert gcd(c,y) == 1 and gcd(c,p) == 1
    integer_h = [h for h in divisors(s['factors']) if (p+h) % c == 0]
    hits = [d for d in divisors(s['factors'],2) if (d+p*y) % c == 0]
    pairs = []
    for d in hits:
        g = gcd(d,y)
        h,m = d//g,y//g
        assert gcd(h,m) == 1 and y % m == 0 and (y//m) % h == 0
        assert (h+p*m) % c == 0 and gcd(m,r) == 1
        # All actual witness pairs at this child have exactly one slope mod r.
        assert (h*pow(m,-1,r)) % r == (-p) % r
        k = (h+p*m)//c
        den = [y,g*k,p*m*(g//h)*k]
        assert all(z > 0 for z in den)
        assert sum(Fraction(1,z) for z in den) == Fraction(4,p)
        pairs.append(dict(d=d,h=h,m=m,k=k,denominators=den))
    assert integer_h == sorted(z['h'] for z in pairs if z['m'] == 1)
    return dict(r=r,c=c,y=y,factors=s['factors'],integer_h=integer_h,
                reduced_type_I_pairs=pairs)


def main():
    p,root = 280009,13
    assert factor(p) == [(p,1)] and p % 840 in [1,121,169,289,361,529]
    assert nr(p,root) and all(not nr(p,r) for r in (2,3,5,7,11))
    roots = list(sources(p,root))
    root_canonical = canonical(p,root)
    assert not root_canonical['integer_h']
    incoming = {}
    for s in roots:
        for r in s['children']:
            incoming.setdefault(r,s)
    children = sorted(incoming)
    assert len(children) == 59 and root not in children
    canon = [canonical(p,r) for r in children]
    assert not any(z['integer_h'] for z in canon)
    child23 = next(z for z in canon if z['r'] == 23)
    assert any((z['d'],z['h'],z['m']) == (46672,2,3)
               for z in child23['reduced_type_I_pairs'])
    # Evaluate a refutable *one-input* depth-two question, not a new theorem:
    # does this direct-layer miss disappear at some newly reached depth-two r?
    seen = {root,*children}
    checked = []
    edges_examined = 0
    source_count = 0
    found = None
    for q in children:
        for s in sources(p,q):
            source_count += 1
            for r in s['children']:
                edges_examined += 1
                if r in seen:
                    continue
                seen.add(r)
                z = canonical(p,r)
                checked.append(dict(r=r,integer_h=z['integer_h']))
                if z['integer_h']:
                    found = dict(path=[dict(**incoming[q],target=q),
                                       dict(**s,target=r)],terminal=z)
                    break
            if found:
                break
        if found:
            break
    other = canonical(1548961,11)
    assert factor(1548961) == [(1548961,1)] and nr(1548961,11)
    assert not other['integer_h']
    assert {(z['h'],z['m']) for z in other['reduced_type_I_pairs']} == {
        (1,7593),(1,3),(2531,3)}
    out = dict(scope='Fixed inputs only; stop at first depth-two integer terminal or layer exhaustion',
               p=p,root=root,root_canonical=root_canonical,
               root_source_count=len(roots),root_sources=roots,
               direct_children=children,canonical_direct_child_audit=canon,
               direct_integer_terminal_count=sum(bool(z['integer_h']) for z in canon),
               direct_type_I_terminal_count=sum(bool(z['reduced_type_I_pairs']) for z in canon),
               depth_two_sources_examined=source_count,depth_two_edges_examined=edges_examined,
               depth_two_new_vertices_checked=checked,depth_two_found=found,
               depth_two_exhausted=found is None,other_fixed_canonical=other)
    print(json.dumps(out,ensure_ascii=False,indent=2))


if __name__ == '__main__':
    main()
