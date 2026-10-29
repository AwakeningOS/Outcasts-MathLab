"""Independent fixed-input E1 counterexample replay. See pre-run contract.

No participant code/data, third-party packages, random tests, or prime-range scan.
Run on mini: python3 e1-replay-20261029.py
"""
import hashlib
import json
import math
import platform
import sys
import time
from fractions import Fraction
from pathlib import Path

P = 42698041
ROOT = Path(__file__).resolve().parent
START = time.monotonic()

def is_prime(n):
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    return all(n % d for d in range(3, math.isqrt(n) + 1, 2))

def chi(a, p=P):
    v = pow(a % p, (p - 1) // 2, p)
    assert v in (0, 1, p - 1)
    return -1 if v == p - 1 else v

PRIMES = [n for n in range(2, math.isqrt(P) + 1) if is_prime(n)]

def factor(n):
    rem, ans = n, []
    for r in PRIMES:
        if r*r > rem:
            break
        e = 0
        while rem % r == 0:
            rem //= r
            e += 1
        if e:
            ans.append((r,e))
    if rem > 1:
        assert is_prime(rem)
        ans.append((rem,1))
    assert math.prod(r**e for r,e in ans) == n
    return ans

def divisors_square(factors):
    ans = [1]
    for r,e in factors:
        ans = [a * r**k for a in ans for k in range(2*e + 1)]
    return ans

def divisors_scan(n):
    ans = []
    for a in range(1, math.isqrt(n) + 1):
        if n % a == 0:
            ans.append(a)
            if a*a != n:
                ans.append(n//a)
    return ans

def sigma(q):
    return 1 if q % 4 == 3 else 3

def source(q,tau,need_children=False):
    assert is_prime(q) and chi(q) == -1 and q < P
    c = sigma(q)*q*tau*tau
    assert tau > 0 and tau % 2 and c < 3*P
    assert (P+c) % 4 == 0
    x = (P+c)//4
    assert 0 < x < P and math.gcd(x,c) == 1
    fac = factor(x)
    divs2 = divisors_square(fac)
    hitA = {'II': sorted(d for d in divs2 if (d+x) % c == 0),
            'I': sorted(d for d in divs2 if (d+P*x) % c == 0)}
    divs1 = divisors_scan(x)
    assert len(divs1) == math.prod(e+1 for _,e in fac)
    residues = {a % c for a in divs1}
    hitB = {label: any((target*pow(a,-1,c)) % c in residues for a in residues)
            for label,target in [('II',-x),('I',-P*x)]}
    assert hitB == {k:bool(v) for k,v in hitA.items()}, (q,tau,'A/B mismatch')
    children = sorted(r for r,e in fac if chi(r) == -1)
    if need_children:
        from_scan = sorted(a for a in divs1 if is_prime(a) and chi(a) == -1)
        assert from_scan == children, (q,tau,'child mismatch')
    assert time.monotonic()-START < 300, '300-second contract limit'
    return dict(q=q,tau=tau,c=c,x=x,factors=fac,hits=hitA,
                divisors_x_squared=len(divs2),divisors_x=len(divs1),
                independent_residue_product_match=True,children=children)

def all_sources(q,need_children=False):
    tau = 1
    rows = []
    while sigma(q)*q*tau*tau < 3*P:
        row = source(q,tau,need_children)
        assert not row['hits']['I'] and not row['hits']['II'], ('unexpected success',row)
        rows.append(row)
        tau += 2
    assert rows[-1]['tau'] == tau-2
    return rows

assert is_prime(P) and P % 840 == 1
smaller = {str(r):chi(r) for r in PRIMES if r < 41}
assert set(smaller.values()) == {1} and chi(41) == -1
roots = all_sources(41,True)
assert len(roots) == 510
children = sorted({r for row in roots for r in row['children']})
assert len(children) == 437
print('root_verified:510 sources,437 children',flush=True)
childrows = {str(q):all_sources(q) for q in children}
assert sum(map(len,childrows.values())) == 16372
path = [source(41,1),source(727,117),source(277,3)]
assert 727 in path[0]['children'] and 277 in path[1]['children']
assert 277 not in children
assert [row['x'] for row in path] == [10674541,13162486,10676380]
d = 18590
final = path[-1]
c,x = final['c'],final['x']
assert c == 7479 and d in final['hits']['II']
assert (x*x) % d == 0 and (d+x) % c == 0
assert (x*x//d+x) % c == 0
y,z = P*((d+x)//c),P*((x*x//d+x)//c)
assert (x,y,z) == (10676380,61058198630,35066193151660)
assert 4*x*y*z == P*(x*y+x*z+y*z)
assert Fraction(4,P) == Fraction(1,x)+Fraction(1,y)+Fraction(1,z)
modroots = {str(q):[t for t in range(277) if (P+sigma(q)*q*t*t)%277 == 0]
            for q in (41,727)}
diagnostic = dict(root_to_277_legendre=chi(-123,277),
                  second_to_277_legendre=chi(-727,277),
                  p_mod_277=chi(P,277),all_roots_mod_277=modroots,
                  root_window_bound=123*(277-2)**2 < 3*P)
allrows = roots+[row for rows in childrows.values() for row in rows]
summary = dict(p=P,p_prime=True,p_mod_840=P%840,least_nonresidue=41,
               smaller_prime_symbols=smaller,root_sources=len(roots),
               child_vertices=len(children),child_sources=sum(map(len,childrows.values())),
               all_failed_sources=len(allrows),all_failed_both_branches=True,
               divisor_tests=sum(r['divisors_x_squared'] for r in allrows),
               independent_divisor_scan_product_checks=len(allrows),
               children_independently_reconstructed=True,
               all_exponents_preserved=True,D_root=2,path=path,
               denominators=[x,y,z],path_d=d,diagnostic=diagnostic,
               E1_refuted=True,Qleast_square_refuted=False,ESC_refuted=False,
               Lean_executed=False,prime_range_scan=False,
               seconds=time.monotonic()-START,python=sys.version,
               platform=platform.platform(),cpu_processes=1,
               script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
result = dict(summary=summary,children=children,root_sources=roots,child_sources=childrows)
(ROOT/'e1-replay-results.json').write_text(json.dumps(result,ensure_ascii=False,separators=(',',':'))+'\n')
(ROOT/'e1-replay-summary.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(summary,ensure_ascii=False,indent=2))
