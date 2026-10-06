import hashlib
import json
import re
import sys
from math import gcd, isqrt, prod
from pathlib import Path

root = Path(sys.argv[1])
repo = root / 'repo'
box = [(a, u) for a in range(1, 7) for u in range(1, 7) if gcd(a, u) == 1]
box += [(a, u) for u in (11, 13, 17, 19, 23) for a in range(1, 7)]

def factor(n):
    result = []
    q = 2
    while q * q <= n:
        count = 0
        while n % q == 0:
            count += 1
            n //= q
        if count:
            result.append((q, count))
        q += 1
    if n > 1:
        result.append((n, 1))
    return result

def expand(factors):
    ds = [1]
    for q, e in factors:
        ds = [d * q ** k for d in ds for k in range(e + 1)]
    return sorted(ds)

def traverse(n):
    ds = []
    for d in range(1, isqrt(n) + 1):
        if n % d == 0:
            ds.append(d)
            if d * d != n:
                ds.append(n // d)
    return sorted(ds)

def legendre(n, q):
    r = pow(n % q, (q - 1) // 2, q)
    return -1 if r == q - 1 else r

def subgroup(gens, modulus):
    reached = {1}
    queue = [1]
    for x in queue:
        for g in gens:
            y = x * g % modulus
            if y not in reached:
                reached.add(y)
                queue.append(y)
    return reached

source = (repo / 'OutcastsMathLab/Research/HardPrimes20261005.lean').read_text()
certificate_rows = {}
pattern = r'theorem p(\d+)_a(\d+)_u(\d+) :.*?\(L := \[(.*?)\]\)'
for p, a, u, text in re.findall(pattern, source, re.S):
    fs = [(int(q), int(e)) for q, e in re.findall(r'\((\d+), (\d+)\)', text)]
    certificate_rows[int(p), int(a), int(u)] = fs
if len(certificate_rows) != 106:
    raise RuntimeError('Missing certificates')
rows = []
for p in (345601, 670849):
    if factor(p) != [(p, 1)]:
        raise RuntimeError('Input not prime')
    for a, u in box:
        M, modulus = a * p + u, 4 * a * u
        fs = factor(M)
        if fs != certificate_rows[p, a, u]:
            raise RuntimeError('Certificate factor mismatch')
        ds = expand(fs)
        if ds != traverse(M):
            raise RuntimeError('Full divisor methods disagree')
        hits = [d for d in ds if (d + 1) % modulus == 0]
        if hits:
            raise RuntimeError('False negative certificate')
        units = [q % modulus for q, e in fs if gcd(q, modulus) == 1]
        H = subgroup(units, modulus)
        squares = {r * r % modulus for r in range(1, modulus) if gcd(r, modulus) == 1}
        H_squares = {h * t % modulus for h in H for t in squares}
        kind = 'exponent' if modulus - 1 in H else ('nonquadratic_subgroup' if modulus - 1 in H_squares else 'quadratic_character')
        rows.append({'p': p, 'a': a, 'u': u, 'M': M, 'modulus': modulus,
                     'factorization': fs, 'all_divisors': ds, 'T': sorted(set(units)),
                     'group': sorted(H), 'group_contains_neg_one': modulus - 1 in H,
                     'legendre_u_p': legendre(u, p), 'failure_type': kind,
                     'odd_prime_jacobi_p_values': [[q, legendre(p, q)] for q, e in fs if q != 2],
                     'actual_witnesses': hits, 'full_divisor_sets_agree': True})
summary = {'rows': len(rows), 'box_pairs_per_p': len(box), 'primes': [345601, 670849],
           'all_certificates_match': True, 'all_full_divisor_sets_agree': True,
           'randomness': False, 'classification_definition': 'QR iff -1 outside H*G^2; subgroup iff outside H but inside H*G^2; exponent iff inside H but not actual divisors',
           'nonresidue_failed_rows': sum(r['legendre_u_p'] == -1 for r in rows),
           'nonresidue_with_group_escape_but_failure': sum(r['legendre_u_p'] == -1 and r['group_contains_neg_one'] for r in rows),
           'counts': {kind: sum(r['failure_type'] == kind for r in rows) for kind in ('quadratic_character', 'nonquadratic_subgroup', 'exponent')},
           'examples': [r for r in rows if r['legendre_u_p'] == -1 and r['group_contains_neg_one']][:4]}
root.joinpath('box-audit.json').write_text(json.dumps({'summary': summary, 'rows': rows}, indent=2) + '\n')
print(json.dumps(summary, indent=2))
