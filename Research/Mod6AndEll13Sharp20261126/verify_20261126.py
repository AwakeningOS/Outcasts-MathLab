#!/usr/bin/env python3
"""
Standalone reproducible verification script (Python 3 standard library only, no RNG, no assert)
for Research/Mod6AndEll13Sharp20261126 (Outcasts thread #162–#164).
"""
import math
import sys

RES6 = {1, 121, 169, 289, 361, 529}


def require(cond: bool, msg: str) -> None:
    if not cond:
        raise RuntimeError(f"Verification failed: {msg}")


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n == p:
            return True
        if n % p == 0:
            return False
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if a >= n:
            break
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(s - 1):
            x = (x * x) % n
            if x == n - 1:
                break
        else:
            return False
    return True


def jacobi(a: int, n: int) -> int:
    if n <= 0 or n % 2 == 0:
        raise ValueError("n must be positive odd")
    a %= n
    res = 1
    while a != 0:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5):
                res = -res
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3:
            res = -res
        a %= n
    return res if n == 1 else 0


def primes_up_to(limit: int):
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[0:2] = b"\x00\x00"
    for i in range(2, math.isqrt(limit) + 1):
        if sieve[i]:
            sieve[i * i : limit + 1 : i] = b"\x00" * (((limit - i * i) // i) + 1)
    return [i for i in range(2, limit + 1) if sieve[i]]


def factorint(n: int):
    res = {}
    d = 2
    while d * d <= n and d <= 50000:
        while n % d == 0:
            res[d] = res.get(d, 0) + 1
            n //= d
        d += 1 if d == 2 else 2

    def rho(m: int) -> int:
        if m % 2 == 0:
            return 2
        for c in range(1, 200):
            x, y, g = 2, 2, 1
            while g == 1:
                x = (x * x + c) % m
                y = (y * y + c) % m
                y = (y * y + c) % m
                g = math.gcd(abs(x - y), m)
            if g != m:
                return g
        return m

    def rec(m: int) -> None:
        if m == 1:
            return
        if is_prime(m):
            res[m] = res.get(m, 0) + 1
            return
        f = rho(m)
        rec(f)
        rec(m // f)

    if n > 1:
        rec(n)
    return res


def A_val(q: int) -> int:
    return q if q % 4 == 3 else 3 * q


def n2_prime(p: int, small_primes) -> int:
    for q in small_primes:
        if jacobi(q, p) == -1:
            return q
    raise RuntimeError(f"n2({p}) exceeded small_primes")


def admissible_vertex_of_c(p: int, c: int):
    if not (p < 3 * c < 9 * p) or c % 4 != 3:
        return None
    sqf = 1
    for pr, ex in factorint(c).items():
        if ex % 2 == 1:
            sqf *= pr
    if is_prime(sqf) and sqf % 4 == 3 and jacobi(sqf, p) == -1:
        return sqf
    if sqf % 3 == 0 and is_prime(sqf // 3) and (sqf // 3) % 4 == 1 and jacobi(sqf // 3, p) == -1:
        return sqf // 3
    return None


def main() -> None:
    print(f"Python {sys.version.split()[0]}")
    small_primes = [q for q in primes_up_to(10000) if q >= 11]

    # 1. Independent check of #163 items
    p = 236807209
    require(is_prime(p) and n2_prime(p, small_primes) == 13, "236807209 ell=13")
    require(p % 32 == 9 and p % 13 == 2 and p % 5 == 4 and (p + 3) % 17 == 0, "236807209 branch")
    require(((p + 39 * 15 * 15) // 4) % 17 == 0 and jacobi(17, p) == -1, "13 -15-> 17")
    xp = (p + 51) // 4
    require(xp == 59201815 and xp % 5 == 0 and (xp + 5) % 51 == 0, "17 d=5")

    h_list = [13, 17, 19, 23, 26, 29, 31, 34]
    rows_163 = []
    for s in range(1, 13):
        divs = [d for d in range(1, s + 1) if s % d == 0]
        for a in divs:
            for b in divs:
                if math.gcd(a, b) != 1:
                    continue
                for h in h_list:
                    if h > 3 * a:
                        continue
                    g = math.gcd(416 * (h + a), 4 * h * s)
                    if (41 * (h + a) + b) % g == 0:
                        rows_163.append((s, a, b, h))
    require(rows_163 == [(6, 6, 1, 17), (10, 10, 1, 29), (12, 6, 1, 17)], f"#163 table: {rows_163}")

    p = 405368329
    c = 33863 * 65 * 65
    r = 11425823
    require(is_prime(p) and is_prime(r) and admissible_vertex_of_c(p, c) == 33863, "405368329 c")
    require((p + c) // 4 == 12 * r and (4 * 72 * r + 1) % c == 0, "405368329 e=72r")

    p = 26007529
    fac20 = factorint(p + 20)
    divs20 = [1]
    for pr, ex in fac20.items():
        divs20 = [dv * (pr ** k) for dv in divs20 for k in range(ex + 1)]
    mods20 = sorted({dv % 20 for dv in divs20})
    require(fac20 == {3: 1, 23: 1, 376921: 1} and mods20 == [1, 3, 9], "26007529 mod20")
    require(((p + 39 * 25) // 4) % 17 == 0 and ((p + 51 * 45 * 45) // 4) % 59 == 0, "26007529 13->17->59")
    x59 = (p + 59) // 4
    require((x59 * x59) % 729 == 0 and (x59 + 729) % 59 == 0, "26007529 d=729")
    print("[1. #163 checks] PASS (transfer d=5, s<=12 table, 405368329, 26007529)")

    # 2. Independent check of #164 items + reachability completion
    eq_counts = {}
    for ell in small_primes:
        if ell % 6 != 5 or ell * ell >= 10**8:
            continue
        s0 = (ell + 1) // 3
        M = 4 * ell * s0
        Acoef = ell + s0
        p0 = (-pow(Acoef, -1, M)) % M
        for p in range(p0, 10**8, M):
            if p < 1009 or p <= ell * ell or (p % 840) not in RES6:
                continue
            if not is_prime(p) or n2_prime(p, small_primes) != ell:
                continue
            r = (Acoef * p + 1) // M
            if not is_prime(r):
                continue
            c = (s0 * p + 1) // ell
            if admissible_vertex_of_c(p, c) is not None:
                e = s0 * s0 * r
                require(4 * e + 1 == (ell + s0) * c, "thm4 eq witness")
                eq_counts[ell] = eq_counts.get(ell, 0) + 1
    require(eq_counts == {11: 207, 17: 35, 23: 2, 29: 2} and sum(eq_counts.values()) == 246, f"eq_counts={eq_counts}")

    cnt_661 = 0
    mods32 = set()
    first3_661 = []
    for p in range(337, 10**8, 408):
        if p < 1009 or (p % 840) not in RES6 or not is_prime(p):
            continue
        if jacobi(11, p) != 1 or jacobi(13, p) != -1:
            continue
        r = (23 * p + 1) // 408
        c = (6 * p + 1) // 17
        if is_prime(r) and admissible_vertex_of_c(p, c) is not None:
            cnt_661 += 1
            mods32.add(p % 32)
            if len(first3_661) < 3:
                first3_661.append(p)
    require(cnt_661 == 34 and mods32 == {1, 17} and first3_661 == [7681, 30529, 493201], "cnt_661")

    # #164 §3 reachability completion:
    pA, qA = 534018409, 397621963
    require(qA < pA < 2 * qA and factorint(4 * qA - pA) == {3: 1, 8689: 1, 40529: 1}, "534018409 in-degree 0")
    pB, qB = 14147458249, 14731
    require(39 * 1495 * 1495 < 3 * pB and ((pB + 39 * 1495 * 1495) // 4) % qB == 0, "14147458249 13 -1495-> 14731")
    require(jacobi(qB, pB) == -1 and (pB * pB + 52) % (qB * 827 * 827) == 0, "14147458249 c | p^2+52")
    print(f"[2. #164 checks] PASS (eq<10^8={eq_counts}, (6,6,1,17)<10^8=34, 13 -1495-> 14731)")

    # 3. Theorem 5A finite sanity scan: all p <= 100,000 with ell ≡ 1 (mod 6) have 0 successes for (ell+4)*r >= p, s != ell
    ps_100k = [p for p in primes_up_to(100000) if p >= 1009 and (p % 840) in RES6]
    checked_5a = 0
    for p in ps_100k:
        ell = n2_prime(p, small_primes)
        if ell % 6 != 1 or ell * ell >= p:
            continue
        for s in range(1, ell + 4):
            if s == ell:
                continue
            r_lo = (p + ell + 3) // (ell + 4)
            r_hi = (p - 1) // s
            for r in range(r_lo, r_hi + 1):
                if not is_prime(r):
                    continue
                x = s * r
                c = 4 * x - p
                if admissible_vertex_of_c(p, c) is None:
                    continue
                checked_5a += 1
                divs = [1]
                for pr, ex in factorint(x).items():
                    divs = [dv * (pr ** k) for dv in divs for k in range(2 * ex + 1)]
                require(not any((4 * e + 1) % c == 0 for e in divs), f"5A violation at p={p}, s={s}, r={r}")
    print(f"[3. Theorem 5A] PASS (p<=100k, ell≡1 mod 6: {checked_5a} sources in (ell+4)r>=p, s!=ell -> 0 successes)")

    # 4. Theorem 5B explicit prime counterexamples with ell = 13, s = 17, 408*r > 23*p + 1
    golden = [
        (128051449, 122130889, 1, 7271237, 43201114, 40224230380259575468082),
        (123297007849, 369850701547, 1, 7252172197, 41100122794, 36750543336207751533316366822882),
        (250067982481, 750187422667, 1, 14709638311, 83356453192, 306619175597585548179206931204472),
    ]
    for p, q, t, r, y, z in golden:
        require(is_prime(p) and (p % 840) in RES6 and n2_prime(p, small_primes) == 13, f"{p} ell=13")
        require(jacobi(17, p) == -1 and is_prime(q) and jacobi(q, p) == -1, f"{p} QNR 17 & q")
        require(is_prime(r) and jacobi(r, p) == 1, f"{p} QR prime r")
        c = A_val(q) * t * t
        x = 17 * r
        e = 17 * r * r
        require(4 * x == p + c and p < 3 * c < 9 * p, f"{p} upper source")
        require(408 * r > 23 * p + 1, f"{p} > 23/408")
        require((p * p + 68) % c == 0 and (4 * e + 1) % c == 0, f"{p} c | p^2+68")
        require(4 * x * y * z == p * (x * y + x * z + y * z), f"{p} unit fraction")
        print(f"[4. Theorem 5B witness] p={p}, s=17, r={r}, p/r={p/r:.6f} (< 408/23={408/23:.6f}) OK")

    print("\nALL CHECKS PASSED.")


if __name__ == "__main__":
    main()
