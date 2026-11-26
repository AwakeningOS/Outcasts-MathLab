"""Audit the explicitly reported fixed counts in Outcasts #132 and #133.

No new prime range, proposed existence theorem, or Lean claim. The #133
cohorts are exactly the four ranges stated by the participant. Stop after
these finite tables and their exact certificate checks are complete.
"""
import hashlib
import json
import sys
from fractions import Fraction
from math import isqrt, prod
from pathlib import Path


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))


def divs(fs):
    ds = [1]
    for r, e in fs:
        ds = [d * r**j for d in ds for j in range(2 * e + 1)]
    return ds


def main():
    raw = Path(sys.argv[1]).read_bytes()
    assert hashlib.sha256(raw).hexdigest() == 'd9289671ad7d6564d573b8015d05cad8631414f8b119bd0e57fd18ab044b8e1e'
    data = json.loads(raw)
    p = data['p']
    assert p == 30241
    rows = {int(q): ss for q, ss in data['sources'].items()}
    success = set()
    for q, ss in rows.items():
        for s in ss:
            x, c = s['x'], s['c']
            assert 4*x == p+c and prod(r**e for r, e in s['factors']) == x
            if any((d+x) % c == 0 or (d+p*x) % c == 0 for d in divs(s['factors'])):
                success.add(q)
    failed = set(rows) - success
    canonical = set()
    full = set()
    for q in failed:
        for s in rows[q]:
            actual = {r for r, _ in s['factors'] if pow(r, (p-1)//2, p) == p-1}
            assert actual == set(s['children']) and actual <= set(rows)
            full.update((q, r) for r in actual)
            if s['tau'] == 1:
                canonical.update((q, r) for r in actual)
    def summarize(edges):
        z = {}
        for sigma in [1, 3]:
            es = {(q,r) for q,r in edges if (1 if r%4 == 3 else 3) == sigma}
            z[str(sigma)] = dict(pairs=len(es), failed_children=sum(r in failed for q,r in es),
                                  successful_children=sum(r in success for q,r in es),
                                  distinct_success_vertices=sorted({r for q,r in es if r in success}))
        return z
    edge_result = dict(p=p, failed_vertices=len(failed), canonical=summarize(canonical), full=summarize(full))
    assert [(edge_result['canonical'][s]['pairs'],edge_result['canonical'][s]['failed_children']) for s in ['1','3']] == [(314,236),(190,179)]
    assert (edge_result['full']['1']['pairs'],edge_result['full']['1']['failed_children']) == (759,578)
    # Distinct pairs are not a probability model; hash the exact pair lists.
    assert edge_result['canonical']['1']['distinct_success_vertices'] == [19,23,59,79,191,263,367,383]
    assert edge_result['full']['1']['distinct_success_vertices'] == [19,23,59,79,191,263,367,383,1039]
    incoming = [dict(q=q,tau=s['tau'],c=s['c'],x=s['x'],factors=s['factors'])
                for q,ss in sorted(rows.items()) for s in ss if any(r==1039 for r,e in s['factors'])]
    assert len(incoming)==1 and incoming[0]['q']==881 and incoming[0]['tau']==3
    assert 881 in failed and len(rows[881])==3 and 1039 in success
    assert incoming[0]['c']==23787 and incoming[0]['x']==13*1039==13507
    edge_result['vertex1039_incoming_sources']=incoming
    edge_result['canonical_pairs_sha256'] = hashlib.sha256(json.dumps(sorted(canonical)).encode()).hexdigest()
    edge_result['full_pairs_sha256'] = hashlib.sha256(json.dumps(sorted(full)).encode()).hexdigest()

    primes = [p for p in range(1001,20000) if prime(p)]
    rs = [r for r in range(3,60) if prime(r)]
    residual = {1,121,169,289,361,529}
    specs = [('p1mod24_nonresidue',lambda p:p%24==1,True),
             ('all_primes_nonresidue',lambda p:True,True),
             ('all_primes_all_r',lambda p:True,False),
             ('six_classes_nonresidue',lambda p:p%840 in residual,True)]
    cohorts = {}
    for name, accept, require_nr in specs:
        selected = [p for p in primes if accept(p)]
        hits = []
        for p in selected:
            for r in rs:
                if require_nr and pow(r,(p-1)//2,p) != p-1:
                    continue
                c = (1 if r%4==3 else 3)*r
                for h in range(1,12):
                    if (p+c)%(4*h) or (p+h)%c:
                        continue
                    y = (p+c)//4
                    k = (p+h)//c
                    den = (y,y*k,p*(y//h)*k)
                    assert y%h==0 and (y*y)%(h*y)==0 and (h*y+p*y)%c==0
                    assert all(z>0 for z in den)
                    assert sum(Fraction(1,z) for z in den)==Fraction(4,p)
                    hits.append([p,r,h])
        cohorts[name] = dict(input_primes=len(selected),triples=len(hits),hit_primes=len({p for p,r,h in hits}),
                             ordered_triples_sha256=hashlib.sha256(json.dumps(hits).encode()).hexdigest())
    assert [(v['triples'],v['hit_primes']) for v in cohorts.values()] == [(524,232),(2138,931),(3586,1033),(73,41)]
    assert cohorts['p1mod24_nonresidue']['input_primes']==253
    print(json.dumps(dict(edge_audit=edge_result,cohort_audit=cohorts,
                         scope='Participant-specified finite tables only; no new existence result or Lean run.'),indent=2))


if __name__ == '__main__':
    main()
