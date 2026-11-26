"""Audit the two fixed cohorts of post 122, and test direct copying of a divisor.

Use the saved 42698041 rows and reconstruct only the specified root and children
for 280009. Count both branches, with exact divisors; stop after these cohorts.
Separately use only the saved p=2521 graph. Starting at its least nonresidue,
look at reachable parents whose every source fails but which have a canonical
success among their direct children. Test whether *some* such success admits
a child witness d that also divides the square of the source on its incoming
edge. Document the first failing parent (in increasing order), or exhaustion.
No inference from passing the fixed graph to a universal theorem.

Usage: python3 reply122-audit-20261107.py E1_REPLAY_JSON GRAPH_DEPTH_JSON
"""
from collections import Counter
from fractions import Fraction
import json
from math import gcd, isqrt, lcm, prod
from pathlib import Path
import sys


def factor(n):
    factors = []
    prime = 2
    while prime * prime <= n:
        exponent = 0
        while n % prime == 0:
            n //= prime
            exponent += 1
        if exponent:
            factors.append((prime, exponent))
        prime = 3 if prime == 2 else prime + 2
    if n > 1:
        factors.append((n, 1))
    return factors


def square_divisors(factors):
    values = [1]
    for prime, exponent in factors:
        values = [d * prime**k for d in values for k in range(2 * exponent + 1)]
    return values


def sources(p, q):
    base = q * (1 if q % 4 == 3 else 3)
    for tau in range(1, isqrt((3*p - 1) // base) + 1, 2):
        c = base * tau**2
        x = (p + c) // 4
        yield dict(q=q, tau=tau, c=c, x=x, factors=factor(x))


def fixed_cohort(rows, p):
    counts = Counter()
    details = []
    for row in rows:
        q, tau, c, x = (row[key] for key in ('q', 'tau', 'c', 'x'))
        factors = row['factors']
        assert prod(a**b for a,b in factors) == x and 4*x == p+c
        divisors = square_divisors(factors)
        components = [q, tau**2] + ([3] if q % 4 == 1 else [])
        assert prod(components) == c
        m = lcm(*components)
        counts['sources'] += 1
        for branch, offset in [('II', x), ('I', p*x)]:
            terms = [d + offset for d in divisors]
            if any(n % c == 0 for n in terms):
                continue
            if not all(any(n % k == 0 for n in terms) for k in components):
                continue
            witnesses = [d for d in divisors if (d + offset) % m == 0]
            counts['JOINT'] += 1
            counts['overlapping'] += int(m < c)
            counts['lcm_nonempty'] += bool(witnesses)
            if m < c:
                details.append(dict(q=q,tau=tau,c=c,lcm=m,branch=branch,
                                    lcm_hits=witnesses))
    return dict(counts=dict(counts), overlapping_rows=details)


def direct_copy(graph):
    p = graph['p']
    vertices = {int(q): rows for q,rows in graph['sources'].items()}
    root = min(vertices)
    path = {root: []}
    todo = [root]
    for q in todo:
        for source in vertices[q]:
            for child in source['children']:
                if child not in path:
                    path[child] = path[q] + [(q, source['tau'], child)]
                    todo.append(child)
    for q in sorted(path):
        parents = vertices[q]
        if any(any(s['hits'].values()) for s in parents):
            continue
        edges = []
        for s in parents:
            for r in s['children']:
                y = next(z for z in vertices[r] if z['tau'] == 1)
                hits = {b:[d for d in y['divisors_x_squared']
                           if (d + k*y['x']) % y['c'] == 0]
                        for b,k in [('I',p),('II',1)]}
                assert all(sorted(hits[b]) == sorted(y['hits'][b]) for b in hits)
                if any(hits.values()):
                    common = gcd(s['x'],y['x'])
                    copies = [d for ds in hits.values() for d in ds if common**2 % d == 0]
                    edges.append(dict(tau=s['tau'],parent_x=s['x'],child=r,child_x=y['x'],
                                      child_c=y['c'],common=common,hits=hits,copies=copies))
        if edges and not any(e['copies'] for e in edges):
            return dict(p=p,root=root,parent=q,path_from_root=path[q],
                        sources=[(s['tau'],s['x'],s['children']) for s in parents],
                        eligible_edges=edges)
    return None


def check_shift_example(p=1009):
    def nonresidue(r):
        return pow(r, (p - 1) // 2, p) == p - 1

    assert factor(p) == [(p, 1)] and p % 840 == 169
    prime_factors = {h: [r for r, _ in factor(p+h)] for h in (1, 2, 3)}
    vertices = {h: [r for r in primes if r < p and nonresidue(r)]
                for h, primes in prime_factors.items()}
    assert vertices == {1: [], 2: [], 3: [11, 23]}
    assert not any(nonresidue(r) for r in (2, 3, 5, 7))
    h, r = 3, 11
    c = r
    assert (p + c) % (4*h) == 0 and (p+h) % c == 0
    y, k = (p+c)//4, (p+h)//c
    denominators = [y, y*k, p*(y//h)*k]
    assert sum(Fraction(1,n) for n in denominators) == Fraction(4,p)
    return dict(p=p, factors=prime_factors, nonresidue_vertices=vertices,
                r=r, h=h, y=y, d=h*y, denominators=denominators)


def main():
    e1 = json.loads(Path(sys.argv[1]).read_text())
    graph = json.loads(Path(sys.argv[2]).read_text())['runs'][0]
    assert graph['p'] == 2521 and e1['summary']['p'] == 42698041
    p = 280009
    roots = list(sources(p,13))
    children = sorted({r for s in roots for r,_ in s['factors'] if pow(r,(p-1)//2,p) == p-1})
    assert len(children) == 59 and 13 not in children
    small = roots + [s for q in children for s in sources(p,q)]
    large = e1['root_sources'] + [s for rows in e1['child_sources'].values() for s in rows]
    result = {'280009':fixed_cohort(small,p), '42698041':fixed_cohort(large,42698041),
              'direct_copy':direct_copy(graph), 'shift_example':check_shift_example()}
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()
