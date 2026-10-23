import json
import math
from fractions import Fraction
from itertools import product
from pathlib import Path

run = Path('/mnt/hdd1t/outcasts-reply-20261009-eTMABt')

def factor(n):
    assert n > 0
    out = {}
    q = 2
    while q * q <= n:
        while n % q == 0:
            out[q] = out.get(q, 0) + 1
            n //= q
        q = 3 if q == 2 else q + 2
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out

def divisors(fs):
    out = [1]
    for q, e in fs.items():
        out = [d * q ** k for d in out for k in range(e + 1)]
    return sorted(out)

def scan_divisors(n):
    out = set()
    for d in range(1, math.isqrt(n) + 1):
        if n % d == 0:
            out.add(d)
            out.add(n // d)
    return sorted(out)

p = 3678481
B = (p - 1).bit_length()
rows = []
normalization_count = 0
for a in range(1, B + 1):
    for u in range(1, B // a + 1):
        M = a * p + u
        fs = factor(M)
        ds = divisors(fs)
        assert ds == scan_divisors(M)
        ss = [s for s in ds if (s + 1) % (4 * a * u) == 0]
        g = math.gcd(a, u)
        for s in ss:
            assert math.gcd(s, g) == 1
            assert ((a // g) * p + u // g) % s == 0
            assert (s + 1) % (4 * (a // g) * (u // g)) == 0
            assert (a // g) * (u // g) <= a * u <= B
            normalization_count += 1
        if g == 1:
            rows.append({'a': a, 'u': u, 'M': M, 'factorization': fs, 'omega': len(fs), 'witnesses': ss})
high_omega = [r for r in rows if r['omega'] >= 4]
assert len(high_omega) == 14
assert all(not r['witnesses'] for r in high_omega)
base = next(r for r in rows if (r['a'], r['u']) == (1, 1))
assert 23 in base['witnesses']
t = (p + 1) // 23
v = (23 + 1) // 4
x, y, z = v * t, v * p, v * t * p
assert 4 * x * y * z == p * (x * y + x * z + y * z)

def fct_first(p):
    for i in range(1, 201):
        for d in divisors(factor(p + i)):
            if d % 4 != 3 or (p + d) % (4 * i):
                continue
            x = (p + d) // 4
            assert x % i == 0
            D = i * x
            assert x * x % D == 0
            assert (D + p * x) % d == 0
            y = (D + p * x) // d
            other = p * p * x * x // D
            assert (other + p * x) % d == 0
            z = (other + p * x) // d
            assert 0 < x <= y <= z
            assert 4 * x * y * z == p * (x * y + x * z + y * z)
            assert x % p and y % p and not z % p
            return {'p': p, 'i': i, 'd': d, 'x': x, 'y': y, 'z': z, 'type': 'I'}
    raise AssertionError('No FCT witness in fixed search limit')

primes = [2521, 66529, 345601, 670849, 5843041]
fct = [fct_first(n) for n in primes]
assert [r['i'] for r in fct] == [2, 9, 9, 5, 5]
possible_i = divisors(factor((2521 + 11) // 4))
same_d = [i for i in possible_i if (2521 + i) % 11 == 0]
assert same_d == []

toy = []
for f1, f2 in product([0, 1], repeat=2):
    phat = Fraction(f1 + f2, 2)
    toy.append({'f': [f1, f2], 'weight': '1/4', 'fixed_T2': str((f1 - Fraction(1, 2)) * (f2 - Fraction(1, 2))), 'fitted_T2': str((f1 - phat) * (f2 - phat))})
fixed_mean = sum(Fraction(r['fixed_T2']) for r in toy) / 4
fitted_mean = sum(Fraction(r['fitted_T2']) for r in toy) / 4
assert fixed_mean == 0 and fitted_mean == -Fraction(1, 8)
record = {'p': p, 'budget': B, 'coprime_pair_count': len(rows), 'all_divisor_methods_match': True, 'omega_at_least_four_rows': high_omega, 'omega_at_least_four_failures': len(high_omega), 'small_shift_solution': {'a': 1, 'u': 1, 's': 23, 'x': x, 'y': y, 'z': z}, 'normalization_witnesses_checked_at_this_input': normalization_count, 'FCT_fixed_five': fct, 'FCT_p2521_d11_possible_i': possible_i, 'FCT_p2521_d11_successful_i': same_d, 'calibration_toy': {'exact_rows': toy, 'fixed_null_T2_mean': str(fixed_mean), 'refitted_null_T2_mean': str(fitted_mean)}, 'global_ES_existence_proved': False, 'global_Hlog_proved': False, 'author_stratified_pvalues_recomputed': False}
(run / 'fixed-review-results.json').write_text(json.dumps(record, indent=2) + '\n')
(run / 'p3678481-all-coprime-rows.json').write_text(json.dumps(rows, indent=2) + '\n')
print(json.dumps(record, indent=2))
