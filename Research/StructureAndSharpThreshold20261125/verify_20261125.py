#!/usr/bin/env python3
"""
Standalone reproducible verification script (Python 3 standard library only, no RNG, no assert)
for Research/StructureAndSharpThreshold20261125 (Outcasts thread #157–#161).
"""
import math
import sys

RES6 = {1, 121, 169, 289, 361, 529}


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


def divisors_of_sq(n: int):
    fac = factorint(n)
    divs = [1]
    for pr, ex in fac.items():
        divs = [d * (pr ** k) for d in divs for k in range(2 * ex + 1)]
    return divs


def check_source_both(p: int, q: int, t: int):
    c = A_val(q) * t * t
    if c >= 3 * p:
        return False, False
    x = (p + c) // 4
    divs = divisors_of_sq(x)
    t1 = any((4 * e + 1) % c == 0 for e in divs)
    t2 = False
    if 3 * c < p:
        t2 = any((d + x) % c == 0 for d in divs)
    return t1, t2


def check_unit_fraction(p: int, x: int, y: int, z: int) -> None:
    if not (p > 0 and x > 0 and y > 0 and z > 0):
        raise ValueError("Non-positive denominator")
    if 4 * x * y * z != p * (x * y + x * z + y * z):
        raise ValueError(f"Unit fraction mismatch for p={p}")


def check_vertex_all_fail(p: int, q: int):
    Aq = A_val(q)
    t_max = math.isqrt((3 * p - 1) // Aq)
    nsrc = 0
    for t in range(1, t_max + 1, 2):
        c = Aq * t * t
        if c >= 3 * p:
            break
        nsrc += 1
        t1, t2 = check_source_both(p, q, t)
        if t1 or t2:
            return nsrc, False
    return nsrc, True


def main() -> None:
    print(f"Python {sys.version.split()[0]}")

    # 1. Theorem 1A explicit constants and threshold table
    c_log = -math.log(1.0 - 2.0 / 13.0) / (2.0 / 13.0)
    if not (c_log < 1.09 and (4.0 / 3.0) * (math.e / 4.0) ** 4 < 0.5 and 4.0 * math.log(math.e / 4.0) < -1.09):
        raise RuntimeError("Theorem 1A constant check failed")
    primes_200k = [p for p in primes_up_to(200000) if p >= 13]
    print("\n[1. Theorem 1A] Brun pure sieve (odd truncation 2k-1, k=ceil(2S)+2, r>=13):")
    for h in (5, 20, 100, 1000, 10000):
        S = 2.0 * sum(1.0 / r for r in primes_200k[:h])
        k = math.ceil(2.0 * S) + 2
        m = 2 * k - 1
        E_sum = sum(math.comb(h, i) * (2 ** i) for i in range(1, min(m, h) + 1))
        log10_N = math.log10(E_sum) + (1.09 * S) / math.log(10)
        log10_p = 4.0 * (log10_N + math.log10(2.0))
        bound_70 = log10_p / (8.0 * math.log10(2.0))
        print(f"  |N+(ell)| > {h:5d} when log10(p) > {log10_p:6.2f} (#70 bound: > {bound_70:5.1f})")

    # 2. Theorem 2A/2B/2C & M_11 lock on all RES6 primes <= 500,000
    ps500 = [p for p in primes_up_to(500) if p >= 11]
    sign_table = {}
    for q in ps500:
        for b in ps500:
            if q == b:
                continue
            if jacobi(-A_val(q), b) != jacobi(b, A_val(q)):
                raise RuntimeError("Jacobi identity mismatch")
            eps = jacobi(b, A_val(q)) * jacobi(q, A_val(b))
            key = (q % 12, b % 12)
            if key in sign_table and sign_table[key] != eps:
                raise RuntimeError("4x4 table inconsistency")
            sign_table[key] = eps

    ps1000 = primes_up_to(1000)
    ps500k = [p for p in primes_up_to(500000) if p >= 1000 and (p % 840) in RES6]
    w_checked, multi_sink = 0, 0
    type_counts = {}
    for p in ps500k:
        B = int(round(p ** (1.0 / 3.0)))
        while (B + 1) ** 3 <= p:
            B += 1
        while B ** 3 > p:
            B -= 1
        V_W = [q for q in ps1000 if 11 <= q <= B and jacobi(q, p) == -1]
        if len(V_W) < 2:
            continue
        w_checked += 1
        adj = {q: set() for q in V_W}
        for q in V_W:
            Aq = A_val(q)
            for b in V_W:
                if b != q and jacobi(b, Aq) == -1:
                    if not (Aq * (b - 2) ** 2 < 3 * p):
                        raise RuntimeError("Window bound violated")
                    adj[q].add(b)
        W3 = [q for q in V_W if q % 4 == 3]
        for idx, q in enumerate(W3):
            for b in W3[idx + 1 :]:
                if not ((b in adj[q]) ^ (q in adj[b])):
                    raise RuntimeError("W3 tournament violation")
        M11 = [q for q in V_W if q % 12 == 11]
        for q0 in M11:
            for b in V_W:
                if b != q0 and not ((b in adj[q0]) ^ (q0 in adj[b])):
                    raise RuntimeError("11-mod-12 dominance violation")
        reach = {}
        for q in V_W:
            vis, st = {q}, [q]
            while st:
                u = st.pop()
                for v in adj[u]:
                    if v not in vis:
                        vis.add(v)
                        st.append(v)
            reach[q] = vis
        sinks, seen = [], set()
        for q in V_W:
            if q in seen:
                continue
            scc = {v for v in V_W if v in reach[q] and q in reach[v]}
            seen |= scc
            if all(reach[v] <= scc for v in scc):
                sinks.append(scc)
        if len(sinks) > 1:
            multi_sink += 1
            mods = tuple(sorted(tuple(sorted({q % 12 for q in s})) for s in sinks))
            type_counts[mods] = type_counts.get(mods, 0) + 1
            for s in (v for sc in sinks for v in sc):
                for q0 in M11:
                    if jacobi(s, q0) != -1:
                        raise RuntimeError("M11 lock violated")

    # Theorem 2C corrected breakdown on p0 = 42,698,041 (#158/#161)
    S0 = [41, 67, 83, 131, 151, 157, 181, 269, 313, 331]
    B0 = 349
    diag0 = sum(jacobi(n, A_val(q)) ** 2 for q in S0 for n in range(1, B0 + 1))
    tot0 = sum((sum(jacobi(n, A_val(q)) for q in S0)) ** 2 for n in range(1, B0 + 1))
    off0 = tot0 - diag0
    if (tot0, diag0, off0) != (3889, 2885, 1004):
        raise RuntimeError("Theorem 2C breakdown mismatch")
    print(f"\n[2. Theorem 2A/2B/2C] Checked {w_checked} RES6 primes <= 500k (|W_p|>=2): single_sink={w_checked - multi_sink}, multi_sink={multi_sink}, types={type_counts}, M11 lock 100%.")
    print(f"  p0=42698041 (1<=n<=349): total={tot0}, diag={diag0}, off-diag={off0}.")

    # 3. Theorem 3 (#159 full-divisor check) & Theorem 4 (sharp threshold) on p <= 50,000
    ps50k = primes_up_to(50000)
    res6_50k = [p for p in ps50k if p >= 1000 and (p % 840) in RES6]
    cnt_ell_div, cnt_forbid, cnt_12, cnt_other, cnt_prR, cnt_prR_succ = 0, 0, 0, 0, 0, 0
    t4_checked, t4_strict_ne_ell, t4_eq_hits = 0, 0, []
    for p in res6_50k:
        ell = next(q for q in ps1000 if q >= 11 and jacobi(q, p) == -1)
        s0 = (ell + 2) // 3
        for q in ps50k:
            if q >= p:
                break
            if q < 11 or jacobi(q, p) != -1:
                continue
            Aq = A_val(q)
            t_min = math.isqrt(p // (3 * Aq)) + 1
            if t_min % 2 == 0:
                t_min += 1
            t_max = math.isqrt((3 * p - 1) // Aq)
            for t in range(t_min, t_max + 1, 2):
                c = Aq * t * t
                if not (p < 3 * c < 9 * p):
                    continue
                x = (p + c) // 4
                fac = factorint(x)
                rmax = max(fac.keys())
                # Theorem 3 check (ell | x)
                if x % ell == 0:
                    cnt_ell_div += 1
                    R = x // ell
                    prR = is_prime(R)
                    if prR:
                        cnt_prR += 1
                    for i in range(3):
                        for j in range(3):
                            if (i, j) != (1, 2) and (4 * (ell ** i) * (R ** j) + 1) % c == 0:
                                cnt_forbid += 1
                    divs = divisors_of_sq(x)
                    wits = [e for e in divs if (4 * e + 1) % c == 0]
                    if wits:
                        if prR:
                            cnt_prR_succ += 1
                        if any(e == ell * R * R for e in wits):
                            cnt_12 += 1
                        else:
                            cnt_other += 1
                # Theorem 4 check (4*ell*s0*r >= (ell+s0)*p + 1)
                lhs = 4 * ell * s0 * rmax
                rhs = (ell + s0) * p + 1
                if lhs >= rhs:
                    t4_checked += 1
                    s = x // rmax
                    t1, t2 = check_source_both(p, q, t)
                    if t1 or t2:
                        if lhs == rhs:
                            t4_eq_hits.append((p, ell, q, t, s, rmax))
                        elif s != ell:
                            t4_strict_ne_ell += 1

    if (cnt_ell_div, cnt_forbid, cnt_12, cnt_other, cnt_prR, cnt_prR_succ) != (20733, 0, 4, 27, 2968, 0):
        raise RuntimeError("Theorem 3 / #159 counts mismatch")
    if t4_strict_ne_ell != 0 or t4_eq_hits != [(40609, 11, 14767, 1, 4, 3461)]:
        raise RuntimeError("Theorem 4 check failed")
    print(f"\n[3. Theorem 3 & #159] p<=50k (137 primes): ell|x upper sources={cnt_ell_div}, forbidden_8={cnt_forbid}, (1,2)={cnt_12}, other_divisors={cnt_other}, primeR={cnt_prR} (succ={cnt_prR_succ}).")
    print(f"[4. Theorem 4] p<=50k: checked {t4_checked} upper sources with 4*ell*s0*r >= (ell+s0)*p+1: strict(s!=ell)={t4_strict_ne_ell}, equality_hits={t4_eq_hits}.")

    # 4. Prime-R Type I witnesses (p=295129, p=376009) & #161 counterexample p=236807209
    check_unit_fraction(295129, 245113, 105556, 694174204120892)
    check_unit_fraction(376009, 160171, 227546, 1245829606731754)
    p_ce, q_ce = 236807209, 116539
    n13, f13 = check_vertex_all_fail(p_ce, 13)
    nq, fq = check_vertex_all_fail(p_ce, q_ce)
    if (n13, f13, nq, fq) != (2134, True, 39, True):
        raise RuntimeError("#161 counterexample root/q mismatch")
    for ch, exp_n in ((1999, 298), (3221, 136), (521, 337), (19069, 56), (97, 781), (199, 945)):
        nch, fch = check_vertex_all_fail(p_ce, ch)
        if (nch, fch) != (exp_n, True):
            raise RuntimeError(f"#161 child {ch} mismatch")
    print("\n[5. Witnesses & #161 counterexample] Verified p=295129, p=376009, and #161 counterexample p=236807209 (root 2134, q 39, 6 children all fail).")
    print("\nALL CHECKS PASSED.")


if __name__ == "__main__":
    main()
