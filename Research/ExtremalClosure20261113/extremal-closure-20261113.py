"""Fixed-input falsification of an extremal-terminal sufficient route.

Exploration first inspected the saved p30241 graph. This independent arithmetic
rebuild is confirmatory, not preregistered or blind. Candidate: every inclusion-
minimal nonempty full-square closed set has a successful source at its minimum
or maximum vertex. Input p30241 only; stop after its least-root closure, reverse
reachability and complete endpoint divisor checks. No ESC range extension.
"""
from collections import deque, Counter
import argparse
from fractions import Fraction
from math import isqrt, prod
from pathlib import Path
import hashlib
import json

P = 30241


def factors(n):
    ans = []
    r = 2
    while r*r <= n:
        e = 0
        while n % r == 0:
            n //= r
            e += 1
        if e:
            ans.append((r, e))
        r += 1
    if n > 1:
        ans.append((n, 1))
    return ans


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n)+1))


def nr(q):
    return pow(q, (P-1)//2, P) == P-1


def source(q, t):
    c = (1 if q % 4 == 3 else 3)*q*t*t
    assert t % 2 == 1 and 0 < c < 3*P
    assert (P+c) % 4 == 0
    x = (P+c)//4
    fs = factors(x)
    assert prod(r**e for r, e in fs) == x
    assert all(prime(r) for r, _ in fs)
    children = [r for r, _ in fs if nr(r)]
    assert children and q not in children
    assert nr(x) and x < P
    return dict(q=q, tau=t, c=c, x=x, factors=fs, children=children)


def all_sources(q):
    t = 1
    ans = []
    while (1 if q % 4 == 3 else 3)*q*t*t < 3*P:
        ans.append(source(q, t))
        t += 2
    return ans


def check_divisors(s):
    x, c = s['x'], s['c']
    ds = [1]
    for r, e in s['factors']:
        ds = [d*r**j for d in ds for j in range(2*e+1)]
    direct = set()
    for d in range(1, x+1):
        if x*x % d == 0:
            direct.update((d, x*x//d))
    assert sorted(ds) == sorted(direct)
    hits = {b: [d for d in ds if (d+k*x) % c == 0]
            for b, k in [('I', P), ('II', 1)]}
    s.update(divisors=sorted(ds), hits=hits)
    return hits


def reach(root, edges):
    seen = {root}
    todo = deque([root])
    parent = {}
    while todo:
        q = todo.popleft()
        for r in sorted(edges[q]):
            if r not in seen:
                seen.add(r)
                parent[r] = q
                todo.append(r)
    return seen, parent


def peer_distance_check(old_path):
    raw = Path(old_path).read_bytes()
    j = json.loads(raw)
    ce = {int(q): set(rows[0]['children']) for q, rows in j['all_sources'].items()}
    fe = {int(q): {r for row in rows for r in row['children']}
          for q, rows in j['all_sources'].items()}
    s0 = set(j['canonical_edges_canonical_terminals']['terminals'])

    def dist(edges, terminals, omit=None):
        rev = {q: set() for q in edges if q != omit}
        for q, rs in edges.items():
            for r in rs:
                if q != omit and r != omit:
                    rev[r].add(q)
        d = {q: 0 for q in terminals if q != omit}
        todo = deque(d)
        while todo:
            r = todo.popleft()
            for q in rev[r]:
                if q not in d:
                    d[q] = d[r]+1
                    todo.append(q)
        return d

    a = dist(fe, s0)
    b, c = dist(ce, s0 | {367}), dist(ce, s0)
    removed = dist(ce, s0, omit=367)
    changed = [q for q in b if b[q] != c[q]]
    assert [Counter(a.values())[i] for i in range(7)] == [10,371,807,336,76,22,1]
    assert len(changed) == 115 and {c[q]-b[q] for q in changed} == {6}
    assert 21821 not in removed and 28657 not in removed and removed[23431] == 16
    return dict(input_sha256=hashlib.sha256(raw).hexdigest(),
                reused_saved_arithmetic=True, fourth_table=dict(Counter(a.values())),
                changed_vertices=len(changed), all_increases=6,
                removing_367_as_vertex_blocks=[21821,28657],
                p2521_107_vertex_claim_recomputed=False)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--peer-results', help='Optional saved Nov12 full arithmetic JSON')
    args = parser.parse_args()
    assert prime(P) and P % 840 in {1,121,169,289,361,529}
    assert all(not nr(q) for q in [2,3,5,7]) and nr(11)
    root = 11
    seen = {root}
    todo = deque([root])
    rows = {}
    discovery = {}
    while todo:
        q = todo.popleft()
        assert prime(q) and nr(q) and q < P
        rows[q] = all_sources(q)
        for s in rows[q]:
            for r in s['children']:
                if r not in seen:
                    seen.add(r)
                    discovery[r] = dict(parent=q, tau=s['tau'])
                    todo.append(r)
    edges = {q: {r for s in ss for r in s['children']} for q, ss in rows.items()}
    assert all(edges[q] <= seen for q in seen)
    reverse = {q: set() for q in seen}
    for q, rs in edges.items():
        for r in rs:
            reverse[r].add(q)
    forward, _ = reach(root, edges)
    backward, return_tree = reach(root, reverse)
    assert seen == forward == backward
    endpoints = [min(seen), max(seen)]
    endpoints_data = {}
    for q in endpoints:
        for s in rows[q]:
            assert not any(check_divisors(s).values())
        endpoints_data[q] = rows[q]
    # A positive interior endpoint distinguishes the counterexample's premise
    # from the hypothetical assumption that EVERY vertex in C fails.
    s = next(s for s in rows[19] if s['tau'] == 1)
    hits = check_divisors(s)
    d = min(hits['I'])
    x, c = s['x'], s['c']
    D = d
    S = (P*x)**2//D
    assert D*S == (P*x)**2 and (D+P*x) % c == 0 and (S+P*x) % c == 0
    den = [x,(D+P*x)//c,(S+P*x)//c]
    assert sum(Fraction(1,z) for z in den) == Fraction(4,P)
    result = dict(p=P, root=root, vertices=sorted(seen), vertex_count=len(seen),
                  sources=sum(map(len,rows.values())), all_sources=rows,
                  discovery_tree=discovery, return_tree=return_tree,
                  closed=True, strongly_connected=True,
                  endpoint_failure=endpoints_data,
                  interior_success=dict(q=19,tau=1,d=d,denominators=den))
    out = Path('extremal-closure-results.json')
    out.write_text(json.dumps(result,ensure_ascii=False,sort_keys=True,indent=2)+'\n')
    summary = {k: result[k] for k in ['p','root','vertex_count','sources','closed',
                                     'strongly_connected','interior_success']}
    if args.peer_results:
        summary['peer137'] = peer_distance_check(args.peer_results)
    summary['endpoints'] = {q:dict(sources=len(ss),divisors=sum(len(s['divisors']) for s in ss),
                                    all_branches_failed=True) for q,ss in endpoints_data.items()}
    summary['full_result_sha256'] = hashlib.sha256(out.read_bytes()).hexdigest()
    Path('extremal-closure-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))


if __name__ == '__main__':
    main()
