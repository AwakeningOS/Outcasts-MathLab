"""Audit new fixed-case facts in Outcasts139, not an ES existence experiment.

Input: saved and already arithmetic-verified Nov12 p30241 graph, plus the
known successful vertex p2521,q1583 named in139 and96. Stop after SCC/reverse
reachability and the single source's complete divisor audit. The19-input
extension in139 is not rerun. No new range or universal inference.
"""
import argparse
from collections import deque, Counter
from fractions import Fraction
from math import isqrt, prod
from pathlib import Path
import hashlib
import json


def distances(edges, roots, omit=None):
    rev = {q: set() for q in edges if q != omit}
    for q, rs in edges.items():
        for r in rs:
            if q != omit and r != omit:
                rev[r].add(q)
    dist = {q:0 for q in roots if q != omit}
    todo = deque(dist)
    while todo:
        r = todo.popleft()
        for q in sorted(rev[r]):
            if q not in dist:
                dist[q] = dist[r]+1
                todo.append(q)
    return dist


def components(edges):
    seen = set()
    order = []
    for root in sorted(edges):
        if root in seen:
            continue
        stack = [(root,False)]
        while stack:
            q,finished = stack.pop()
            if finished:
                order.append(q)
            elif q not in seen:
                seen.add(q)
                stack.append((q,True))
                stack.extend((r,False) for r in sorted(edges[q],reverse=True) if r not in seen)
    rev = {q:set() for q in edges}
    for q,rs in edges.items():
        for r in rs:
            rev[r].add(q)
    seen = set()
    out = []
    for root in reversed(order):
        if root in seen:
            continue
        seen.add(root)
        comp = {root}
        todo = [root]
        while todo:
            for q in rev[todo.pop()]:
                if q not in seen:
                    seen.add(q)
                    comp.add(q)
                    todo.append(q)
        out.append(comp)
    return out


def one_source_witness():
    p,q = 2521,1583
    assert all(n % d for n in [p,q] for d in range(2,isqrt(n)+1))
    assert p%840 in {1,121,169,289,361,529}
    assert pow(q,(p-1)//2,p) == p-1
    c=q
    assert q%4 == 3 and c<3*p<=9*c
    x=(p+c)//4
    fs=[(2,1),(3,3),(19,1)]
    assert prod(r**e for r,e in fs) == x
    ds=[1]
    for r,e in fs:
        ds=[d*r**j for d in ds for j in range(2*e+1)]
    direct=set()
    for d in range(1,x+1):
        if x*x%d == 0:
            direct.update((d,x*x//d))
    assert sorted(ds)==sorted(direct)
    hits={b:sorted(d for d in ds if (d+k*x)%c==0) for b,k in [('I',p),('II',1)]}
    witnesses=[]
    for branch,dd in hits.items():
        for d in dd:
            D=d if branch=='I' else p*d
            S=(p*x)**2//D
            assert D*S==(p*x)**2 and (D+p*x)%c==0 and (S+p*x)%c==0
            den=[x,(D+p*x)//c,(S+p*x)//c]
            assert sum(Fraction(1,n) for n in den)==Fraction(4,p)
            witnesses.append(dict(branch=branch,d=d,denominators=den))
    assert witnesses
    return dict(p=p,q=q,c=c,x=x,factors=fs,valid_tau=[1],divisors=sorted(ds),
                hits=hits,witnesses=witnesses,role='Known successful vertex; clarifies that a single valid source does not imply failure')


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('saved_graph')
    args=ap.parse_args()
    raw=Path(args.saved_graph).read_bytes()
    j=json.loads(raw)
    assert j['p']==30241
    full={int(q):{r for s in rows for r in s['children']} for q,rows in j['all_sources'].items()}
    canon={int(q):set(rows[0]['children']) for q,rows in j['all_sources'].items()}
    terminal=set(j['canonical_edges_canonical_terminals']['terminals'])
    old=distances(canon,terminal|{367});new=distances(canon,terminal)
    removed=distances(canon,terminal,omit=367)
    missing=set(full)-{367}-set(removed)
    changed={q for q in full if old[q]!=new[q]}
    assert len(missing)==114 and missing==changed-{367}
    cc=components(full)
    closed=[s for s in cc if all(full[q]<=s for q in s)]
    root_component=next(s for s in cc if 11 in s)
    assert len(cc)==1115 and Counter(map(len,cc))=={1:1114,509:1}
    assert closed==[root_component] and set(j['full_edges_all_terminals']['terminals'])<=root_component
    to_root=distances(full,{11})
    assert set(to_root)==set(full)
    result=dict(p=30241,reused_saved_arithmetic=True,input_sha256=hashlib.sha256(raw).hexdigest(),
                vertices=len(full),component_count=len(cc),component_sizes=dict(Counter(map(len,cc))),
                closed_component_count=len(closed),root_component=sorted(root_component),
                all_vertices_reach_11=True,distances_to_11=to_root,
                deleted_367_unreachable_vertices=sorted(missing),
                success_vertices=sorted(j['full_edges_all_terminals']['terminals']),
                known_one_source_success=one_source_witness(),
                nineteen_input_extension_recomputed=False)
    Path('reply139-results.json').write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    summary={k:v for k,v in result.items() if k not in ['root_component','distances_to_11','deleted_367_unreachable_vertices']}
    summary['deleted_367_unreachable_count']=len(missing)
    summary['root_component_size']=len(root_component)
    summary['full_result_sha256']=hashlib.sha256(Path('reply139-results.json').read_bytes()).hexdigest()
    Path('reply139-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))


if __name__=='__main__':
    main()
