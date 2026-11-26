import json
import sys
from pathlib import Path
from math import isqrt, prod

root = Path(sys.argv[1])

def jacobi(a, n):
    sign = 1
    a %= n
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5):
                sign = -sign
        a, n = n, a
        if a % 4 == n % 4 == 3:
            sign = -sign
        a %= n
    return sign if n == 1 else 0

def factor(n):
    fs = []
    d = 2
    while d * d <= n:
        e = 0
        while n % d == 0:
            n //= d
            e += 1
        if e:
            fs.append((d, e))
        d += 1
    if n > 1:
        fs.append((n, 1))
    return fs

results = []
for p in (345601, 670849):
    if factor(p) != [(p, 1)]:
        raise RuntimeError('Prime input mismatch')
    B = (p - 1).bit_length()
    shifts = []
    pairs = []
    for u in range(1, B + 1):
        J = jacobi(u, p)
        residue = pow(u, (p - 1) // 2, p)
        euler_J = -1 if residue == p - 1 else residue
        if J != euler_J:
            raise RuntimeError('Jacobi/Euler mismatch')
        shifts.append({'u': u, 'jacobi': J, 'euler_residue': residue})
        if J == -1:
            for a in range(1, B // u + 1):
                M = a * p + u
                fs = factor(M)
                ds = [1]
                for q, e in fs:
                    ds = [d * q ** k for d in ds for k in range(e + 1)]
                traversal = []
                for d in range(1, isqrt(M) + 1):
                    if M % d == 0:
                        traversal.append(d)
                        if d * d != M:
                            traversal.append(M // d)
                if sorted(ds) != sorted(traversal):
                    raise RuntimeError('Divisor mismatch')
                witnesses = [d for d in sorted(ds) if (d + 1) % (4 * a * u) == 0]
                pairs.append({'a': a, 'u': u, 'factorization': fs, 'all_divisors': sorted(ds), 'witnesses': witnesses})
    if any(row['witnesses'] for row in pairs):
        raise RuntimeError('Expected falsification not obtained')
    results.append({'p': p, 'budget': B, 'residue_mod840': p % 840,
                    'all_shifts': shifts, 'nonresidue_shifts': [r['u'] for r in shifts if r['jacobi'] == -1],
                    'all_admissible_nonresidue_pairs': pairs, 'HNR_refuted': True, 'Hlog_refuted': False})

example = {'p': 345601, 'a': 1, 'u': 19, 'M': 345620, 'modulus': 76,
           'unit_divisor_residues': sorted({d % 76 for d in results[0]['all_admissible_nonresidue_pairs'][0]['all_divisors'] if d % 2 and d % 19}),
           'q': 1571, 'q_residue': 1571 % 76, 'forbidden_group_power': pow(1571, 9, 76),
           'actual_q_exponent': 1}
payload = {'inputs': results, 'example': example, 'shift_values_checked': 39,
           'actual_pairs_checked': sum(len(r['all_admissible_nonresidue_pairs']) for r in results),
           'randomness': False, 'integer_range_extension': False, 'scope': 'exact finite integer checks; Lean is verified separately'}
root.joinpath('nonresidue-budget-results.json').write_text(json.dumps(payload, indent=2) + '\n')
print(json.dumps(payload, indent=2))
