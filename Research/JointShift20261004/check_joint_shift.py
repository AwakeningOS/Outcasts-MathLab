"""Exact all-depth fixed-u falsification, preregistered 2026-10-04.

H12: every target prime has an actual divisor witness at u in {1, 2}.
Inputs: 2521 and 66529, whose all-depth u=1 failures were already
reported (Lopez 2024; independently audited in Reply20261003).
New question: does u=2 rescue these failures at any a?
If u=2 fails, audit u=3,4 to characterize that simultaneous failure.
Stop: finish this finite input set or external 180s timeout; no range sweep.
Every fixed-u witness obeys 4*u*a <= p+4*u*u+1, so no arbitrary a cutoff.
All positive a are retained, including noncoprime pairs; no Omega cutoff.
Two independent checks: factor expansion and integer divisor traversal.
"""
import argparse
import hashlib
import json
import math
import os
import platform
import time
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path

def factor(n):
    out = []
    q = 2
    while q*q <= n:
        e = 0
        while n % q == 0:
            n //= q
            e += 1
        if e:
            out.append([q,e])
        q = 3 if q == 2 else q+2
    if n > 1:
        out.append([n,1])
    return out

def divisors(fs):
    ds = [1]
    for q,e in fs:
        ds = [d * q**j for d in ds for j in range(e+1)]
    return sorted(ds)

def check(inp):
    p,u,a = inp
    m = a*p+u
    mod = 4*a*u
    fs = factor(m)
    ds = divisors(fs)
    scan = []
    for d in range(1, math.isqrt(m)+1):
        if m%d == 0:
            scan.append(d)
            if d*d != m:
                scan.append(m//d)
    assert ds == sorted(scan), (p,u,a)
    assert math.prod(q**e for q,e in fs) == m
    hits = [s for s in ds if (s+1)%mod == 0]
    ws = []
    for s in hits:
        alpha = (s+1)//mod
        v = m//s
        xyz = [alpha*u*v, a*alpha*u*p, a*alpha*v*p]
        x,y,z = xyz
        assert all(t>0 for t in xyz)
        assert 4*x*y*z == p*(x*y+x*z+y*z)
        assert 4*u*a <= p+4*u*u+1
        ws.append(dict(s=s,alpha=alpha,v=v,xyz=xyz))
    return dict(p=p,u=u,a=a,M=m,modulus=mod,factorization=fs,
                divisors=ds,witnesses=ws,integer_traversal_agrees=True)

def fixed_u(pool,p,u):
    cap = (p+4*u*u+1)//(4*u)
    rows = list(pool.map(check, ((p,u,a) for a in range(1,cap+1)), chunksize=32))
    hits = [dict(a=r['a'], **w) for r in rows for w in r['witnesses']]
    return dict(p=p,u=u,max_a=cap,checked_positive_a=len(rows),
                all_depth_failure=not hits, witnesses=hits, rows=rows)

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--u1-source',type=Path,
        default=Path(__file__).resolve().parent.parent/'Reply20261003'/'results.json')
    args = parser.parse_args()
    started = time.monotonic()
    prior = json.loads(args.u1_source.read_text())
    prior_sha = hashlib.sha256(json.dumps(prior['rows'],sort_keys=True,separators=(',',':')).encode()).hexdigest()
    assert prior_sha == prior['rows_sha256'] == '94aa08e0e654310770992861cdd31aca58bdd2176ce30e56452a92463272ffa4'
    for p in [2521,66529]:
        oldrows = [r for r in prior['rows'] if r['p']==p]
        assert [r['a'] for r in oldrows] == list(range(1,(p+5)//4+1))
        assert all(r['u']==1 and not r['hits'] and r['independent_divisor_scan_matches'] for r in oldrows)
    runs = []
    with ProcessPoolExecutor(max_workers=8) as pool:
        for p in [2521,66529]:
            r = fixed_u(pool,p,2)
            runs.append(r)
            print(json.dumps({k:v for k,v in r.items() if k!='rows'}),flush=True)
            if r['all_depth_failure']:
                for u in [3,4]:
                    r = fixed_u(pool,p,u)
                    runs.append(r)
                    print(json.dumps({k:v for k,v in r.items() if k!='rows'}),flush=True)
    rows = [row for r in runs for row in r['rows']]
    rows_sha = hashlib.sha256(json.dumps(rows,sort_keys=True,separators=(',',':')).encode()).hexdigest()
    result = dict(hypothesis='H12: forall target primes, exists actual witness with u in {1,2}, unrestricted a',
                  existing_u1_source='Reply20261003/results.json and Lopez arXiv:2404.01508v3',
                  verified_prior_u1_rows_sha256=prior_sha,
                  preregistered_inputs=[2521,66529], target_classes_mod840=[1,121,169,289,361,529],
                  hypothesis_refuted=any(r['u']==2 and r['all_depth_failure'] for r in runs),
                  python=platform.python_version(),workers=8,randomness=False,
                  elapsed_seconds=time.monotonic()-started,hostname=os.uname().nodename,
                  rows_sha256=rows_sha,runs=runs)
    Path('results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='runs'}),flush=True)

if __name__ == '__main__':
    main()
