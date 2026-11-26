"""Exact bounded structural test specified in the adjacent contract."""
import json
import math
import time
from pathlib import Path
from itertools import product

def isprime(n):
    # Exact trial division; in this experiment n < 4**18.
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    if n % 3 == 0:
        return n == 3
    for d in range(5, math.isqrt(n)+1, 6):
        if n % d == 0 or n % (d+2) == 0:
            return False
    return True

def composite_factor(n):
    for d in range(2, math.isqrt(n)+1):
        if n % d == 0:
            return d
    raise AssertionError(('not composite', n))

def primitive_necklace(w):
    return all(w < w[i:] + w[:i] for i in range(1, len(w)))

def reconstruct(w):
    nums = []
    for i in range(len(w)):
        d, t = 1, 0
        for s in w[i:] + w[:i]:
            d, t = 4*d, s*t+d
        nums.append(t)
    n = 4**len(w) - math.prod(w)
    g = math.gcd(*nums)
    if n % g:
        return None
    return n//g, [t//g for t in nums], g

def main():
    started = time.monotonic()
    counts = []
    hard_candidates = []
    witness = None
    for m in range(6, 19):
        ct = dict(length=m, primitive_necklaces=0, integral=0, hard_class=0,
                  prime_p=0, all_prime_q=0, typed=0, nonresidue=0)
        for w in product((1,3), repeat=m):
            if not primitive_necklace(w):
                continue
            ct['primitive_necklaces'] += 1
            z = reconstruct(w)
            if z is None:
                continue
            ct['integral'] += 1
            p, qs, g = z
            assert all(p+s*q == 4*qs[(i+1)%m] for i,(q,s) in enumerate(zip(qs,w)))
            if p % 840 not in (1,121,169,289,361,529):
                continue
            ct['hard_class'] += 1
            if not isprime(p):
                factor = composite_factor(p)
                assert 1 < factor < p and p % factor == 0
                hard_candidates.append(dict(length=m, sigmas=w, p=p, g=g,
                                            factor=factor, cofactor=p//factor))
                continue
            ct['prime_p'] += 1
            if len(set(qs)) != m or not all(2<q<p and isprime(q) for q in qs):
                continue
            ct['all_prime_q'] += 1
            if not all(s == (1 if q%4 == 3 else 3) for q,s in zip(qs,w)):
                continue
            ct['typed'] += 1
            assert all(p+s*q == 4*qs[(i+1)%m] for i,(q,s) in enumerate(zip(qs,w)))
            if not all(pow(q,(p-1)//2,p)==p-1 for q in qs):
                continue
            ct['nonresidue'] += 1
            assert all(3*q > p for q in qs)
            rows=[]
            for i,(q,s) in enumerate(zip(qs,w)):
                c=s*q
                x=qs[(i+1)%m]
                assert c<3*p and 9*c>=3*p
                ds=[1,x,x*x]
                rows.append(dict(q=q,c=c,x=x,divisors=ds,
                                 type_I=[d for d in ds if (d+p*x)%c==0],
                                 type_II=[d for d in ds if (d+x)%c==0]))
            witness=dict(p=p,qs=qs,sigmas=w,g=g,sources=rows)
            break
        counts.append(ct)
        print(json.dumps(ct),flush=True)
        if witness:
            break
    result=dict(counts=counts,hard_composite_candidates=hard_candidates,
                witness=witness,seconds=time.monotonic()-started,
                complete_through=counts[-1]['length'] if witness is None else None)
    Path('prime-source-cycle-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result),flush=True)

if __name__ == '__main__':
    main()
