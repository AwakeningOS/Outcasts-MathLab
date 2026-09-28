#!/usr/bin/env python3
"""Deterministic finite regression, not a proof outside the listed inputs."""
import hashlib
import json
from math import gcd, isqrt
from pathlib import Path


def prime(p):
    return p >= 2 and all(p % d for d in range(2, isqrt(p) + 1))


def direct(p, x):
    c, m = 4*x-p, p*x
    solutions = []
    # cy > M; y <= z implies cy <= 2M.
    for y in range(max(x, m//c+1), 2*m//c+1):
        z, remainder = divmod(m*y, c*y-m)
        if remainder == 0 and z >= y:
            solutions.append((x, y, z))
    return solutions


def reduced(p, x):
    if not prime(p) or p == 2 or not p < 4*x <= 3*p:
        raise ValueError("requires odd prime p and p < 4x <= 3p")
    c, m = 4*x-p, p*x
    if gcd(c, m) != 1:
        raise RuntimeError("coprimality failed")
    solutions = []
    for d in range(max(1, c*x-m), m+1):
        if m*m % d or (d+m) % c:
            continue
        e = m*m//d
        if (e+m) % c:
            raise RuntimeError("second divisibility failed")
        y, z = (d+m)//c, (e+m)//c
        if not (0 < x <= y <= z and 4*x*y*z == p*(x*y+x*z+y*z)):
            raise RuntimeError("reconstruction failed")
        if (c*y-m, c*z-m) != (d, e):
            raise RuntimeError("round trip failed")
        if d % (p*p) == 0:
            raise RuntimeError("unexpected p-adic exponent >= 2")
        if d % p == 0:
            if y % p or z % p:
                raise RuntimeError("Type II classification failed")
        elif y % p == 0 or z % p:
            raise RuntimeError("Type I classification failed")
        solutions.append((x, y, z))
    return sorted(solutions)


def main():
    cases = [(p, x) for p in range(3, 200) if prime(p)
             for x in range(p//4+1, 3*p//4+1)]
    cases += [(409, x) for x in range(409//4+1, 3*409//4+1)]
    cases += [(1201, x) for x in range(301, 307)]
    records = []
    for p, x in cases:
        actual, expected = reduced(p, x), direct(p, x)
        if actual != expected:
            raise RuntimeError(f"enumerators disagree: p={p}, x={x}")
        records.append({"p": p, "x": x, "solutions": actual})
    fixture = [(306, 15980, 172727820), (306, 16218, 1082101),
               (306, 21618, 61251)]
    if reduced(1201, 306) != fixture:
        raise RuntimeError("1201 fixture changed")
    if not (4*9 == 6*6 and (4+6) % 2 == 0 and (9+6) % 2 != 0):
        raise RuntimeError("counterexample changed")
    data = json.dumps(records, sort_keys=True, separators=(",", ":")).encode()
    result = {
        "scope": "all odd primes < 200, p=409 (all allowed x), p=1201 (x=301..306)",
        "cases": len(cases), "solutions": sum(len(r["solutions"]) for r in records),
        "independent_direct_search_matches": True,
        "records_sha256": hashlib.sha256(data).hexdigest(),
        "fixture_1201_x306": [list(solution) for solution in fixture],
        "noncoprime_counterexample": {"c": 2, "M": 6, "d": 4, "e": 9},
    }
    expected_path = Path(__file__).with_name("prime-divisor-results.json")
    expected = json.loads(expected_path.read_text(encoding="utf-8"))
    if result != expected:
        raise RuntimeError(f"finite regression differs from {expected_path.name}")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
