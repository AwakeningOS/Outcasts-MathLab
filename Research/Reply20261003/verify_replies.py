"""Verify Outcasts #22/#24, not search for counterexamples to ESC.

Fixed contract: p=2521,66529; every 1<=a<=floor((p+5)/4), u=1.
Full prime factorization/divisor enumeration AND integer 1..sqrt(M) replay.
8 CPU workers, stdlib, no randomness; external timeout 180 seconds.
All rows are retained; no early stopping on witness/failure.
"""
import concurrent.futures
import hashlib
import json
import math
import platform
import time
from pathlib import Path

PRIMES = []


def prime_sieve(n):
    flags = bytearray(b'\x01')*(n+1)
    flags[:2] = b'\x00\x00'
    for q in range(2, math.isqrt(n)+1):
        if flags[q]:
            flags[q*q:n+1:q] = b'\x00'*((n-q*q)//q+1)
    return [q for q in range(2, n+1) if flags[q]]


def initialize(primes):
    global PRIMES
    PRIMES = primes


def factors(M):
    n, fs = M, []
    for q in PRIMES:
        if q*q > n:
            break
        e = 0
        while n % q == 0:
            n //= q
            e += 1
        if e:
            fs.append((q,e))
    if n > 1:
        fs.append((n,1))
    if math.prod(q**e for q,e in fs) != M:
        raise ValueError('Factor product mismatch')
    return fs


def factor_divisors(fs):
    ds = [1]
    for q,e in fs:
        old = ds[:]
        power = 1
        for _ in range(e):
            power *= q
            ds.extend(d*power for d in old)
    return sorted(ds)


def integer_divisors(M):
    ds = set()
    for s in range(1, math.isqrt(M)+1):
        if M%s == 0:
            ds.add(s)
            ds.add(M//s)
    return sorted(ds)


def check_one(pa):
    p,a = pa
    M,mod = a*p+1,4*a
    fs = factors(M)
    ds = factor_divisors(fs)
    direct = integer_divisors(M)
    if ds != direct:
        raise ValueError(f'Divisor algorithm mismatch at {p},{a}')
    hits = [s for s in ds if (s+1)%mod == 0]
    return dict(p=p,a=a,u=1,M=M,modulus=mod,factorization=fs,
                divisor_residues=sorted({s%mod for s in ds}),hits=hits,
                independent_divisor_scan_matches=True)


def check_witness(p,a,u,s):
    if min(a,u,s)<=0 or (a*p+u)%s or (s+1)%(4*a*u):
        raise ValueError('Invalid actual witness')
    alpha,v = (s+1)//(4*a*u),(a*p+u)//s
    xyz = [alpha*u*v,a*alpha*u*p,a*alpha*v*p]
    x,y,z = xyz
    if min(xyz)<=0 or 4*x*y*z != p*(x*y+x*z+y*z):
        raise ValueError('Integer identity failure')
    return dict(p=p,a=a,u=u,s=s,alpha=alpha,v=v,xyz=xyz)


def main():
    start = time.monotonic()
    inputs = [2521,66529]
    bounds = {p:(p+5)//4 for p in inputs}
    maxM = max(p*bounds[p]+1 for p in inputs)
    primes = prime_sieve(math.isqrt(maxM))
    rows_input = [(p,a) for p in inputs for a in range(1,bounds[p]+1)]
    with concurrent.futures.ProcessPoolExecutor(max_workers=8,
            initializer=initialize,initargs=(primes,)) as pool:
        rows = list(pool.map(check_one,rows_input,chunksize=32))
    initialize(primes)
    box = []
    for a,u,s in [(10,9,578519),(3,14,116087)]:
        fs = factors(s)
        if sum(e for q,e in fs) != 2:
            raise ValueError('Box witness does not have exactly two prime factors')
        hit = check_witness(5843041,a,u,s)
        hit['factorization'] = fs
        hit['is_prime'] = False
        hit['Omega'] = 2
        hit['cost'] = a*u
        hit['inside_box23'] = a<=23 and u<=23
        hit['outside_product23'] = a*u>23
        box.append(hit)
    summary = [dict(p=p,bound=bounds[p],pairs_tested=bounds[p],
                    all_witnesses=[r for r in rows if r['p']==p and r['hits']],
                    independent_divisor_scan_all=True) for p in inputs]
    data = dict(contract='fixed #22/#24 response validation',python=platform.python_version(),
                cpu_workers=8,randomness=False,timeout_seconds=180,
                elapsed_seconds=time.monotonic()-start,summary=summary,
                box_semiprime_witnesses=box,
                unrestricted_witnesses=[check_witness(2521,1,2,87),
                                        check_witness(66529,1,5,39)],
                finite_rows_lean_verified=False,rows=rows)
    canonical = json.dumps(rows,sort_keys=True,separators=(',',':')).encode()
    data['rows_sha256'] = hashlib.sha256(canonical).hexdigest()
    Path('results.json').write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps({k:v for k,v in data.items() if k!='rows'},indent=2))
    if any(item['all_witnesses'] for item in summary):
        raise ValueError('Claimed u=1 obstruction has an actual witness')


if __name__ == '__main__':
    main()
