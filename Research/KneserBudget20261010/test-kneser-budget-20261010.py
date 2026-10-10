import functools
import json
import math
import time
from pathlib import Path

RUN = Path('/mnt/hdd1t/outcasts-reply-20261010-DnoRad')
INPUTS = [1201, 2521, 66529, 345601, 670849, 1740481, 3678481, 5843041, 84525841]
START = time.monotonic()

def factor(n):
    out, q = [], 2
    while q*q <= n:
        e = 0
        while n % q == 0:
            n //= q
            e += 1
        if e:
            out.append((q, e))
        q = 3 if q == 2 else q+2
    if n > 1:
        out.append((n, 1))
    return out

def divisors(fs):
    ds = [1]
    for q, e in fs:
        old = ds[:]
        power = 1
        for _ in range(e):
            power *= q
            ds += [d*power for d in old]
    return sorted(ds)

def extend(H, r, m):
    out = set(H)
    x = r
    while x not in H:
        out.update(h*x % m for h in H)
        x = x*r % m
    return frozenset(out)

def generated(rs, m):
    H = frozenset({1})
    for r in rs:
        H = extend(H, r, m)
    return H

@functools.lru_cache(None)
def subgroups(G, m):
    found, pending = {frozenset({1})}, [frozenset({1})]
    while pending:
        H = pending.pop()
        for g in G-H:
            K = extend(H, g, m)
            if K not in found:
                found.add(K)
                pending.append(K)
    return sorted(found, key=lambda H: (len(H), sorted(H)))

def order_mod_subgroup(q, H, m):
    x, k = q % m, 1
    while x not in H:
        x = x*q % m
        k += 1
        assert k <= m
    return k

def saturation(unit_fs, m):
    H, traces = frozenset({1}), []
    change = True
    while change:
        change = False
        for q, e in unit_fs:
            order = order_mod_subgroup(q, H, m)
            if order > 1 and e >= order-1:
                old = H
                H = extend(H, q % m, m)
                traces.append({'q': q, 'e': e, 'quotient_order': order, 'from': sorted(old), 'to': sorted(H)})
                change = True
    return H, traces

def row(p, a, u):
    M, m = a*p+u, 4*a*u
    fs = factor(M)
    assert math.prod(q**e for q,e in fs) == M
    uf = [(q,e) for q,e in fs if math.gcd(q,m) == 1]
    G = generated([q % m for q,e in uf], m)
    H0, trace = saturation(uf, m)
    D = {1}
    for q,e in uf:
        powers = {pow(q, i, m) for i in range(e+1)}
        D = {d*r % m for d in D for r in powers}
    ds = divisors(fs)
    actual = {d % m for d in ds if math.gcd(d,m) == 1}
    assert D == actual
    assert all({d*h % m for d in D} == D for h in H0)
    hits = [d for d in ds if d % m == m-1]
    data = {'p':p, 'a':a, 'u':u, 'M':M, 'modulus':m, 'factorization':fs,
            'unit_factorization':uf, 'G':sorted(G), 'H0':sorted(H0), 'saturation_trace':trace,
            'actual_divisor_residues':sorted(D), 'witnesses':hits, 'K':False}
    if m-1 not in G:
        data['failure_kind'] = 'group_obstruction'
    elif m-1 in H0:
        data['K'] = True
        data['success_kind'] = 'saturation'
    else:
        audits = []
        for H in subgroups(G,m):
            if not H0 <= H or m-1 in H:
                continue
            sizes = [min(e+1, order_mod_subgroup(q,H,m)) for q,e in uf]
            L, index = sum(k-1 for k in sizes), len(G)//len(H)
            audits.append({'H':sorted(H), 'index':index, 'factor_image_sizes':sizes, 'L':L,
                           'threshold':index-1, 'passes':L>=index-1})
        bad = [z for z in audits if not z['passes']]
        data['quotients_tested'] = len(audits)
        data['K'] = not bad
        if bad:
            data['failure_kind'] = 'insufficient_Kneser_bound'
            data['bad_quotient'] = bad[0]
            data['all_bad_quotients'] = bad
        else:
            data['success_kind'] = 'Kneser'
    assert not data['K'] or hits, 'False-positive sufficient criterion'
    return data

def main():
    records = []
    failure = None
    for p in INPUTS:
        assert p > 7 and p % 840 in {1,121,169,289,361,529}
        assert factor(p) == [(p,1)]
        B = (p-1).bit_length()
        pairs = sorted((a*u,a,u) for a in range(1,B+1) for u in range(1,B//a+1) if math.gcd(a,u)==1)
        rows = []
        for cost,a,u in pairs:
            assert time.monotonic()-START < 180
            rows.append(row(p,a,u))
        hits = [r for r in rows if r['K']]
        actual = [r for r in rows if r['witnesses']]
        rec = {'p':p,'budget':B,'coprime_pairs':len(rows),'K_sufficient_pairs':len(hits),
               'actual_success_pairs':len(actual), 'first_K_pair': [hits[0]['a'],hits[0]['u']] if hits else None,
               'candidate_passes':bool(hits)}
        records.append(rec)
        print(json.dumps(rec),flush=True)
        (RUN / f'p{p}-kneser-rows.json').write_text(json.dumps(rows,indent=2)+'\n')
        if not hits:
            failure = {'p':p,'budget':B,'coprime_pairs':len(rows),'actual_successes':actual,
                       'failure_counts':{k:sum(r.get('failure_kind')==k for r in rows) for k in ['group_obstruction','insufficient_Kneser_bound']}}
            break
    result = {'candidate':'HKlog, saturated quotient Kneser certificate within ceil(log2 p)',
              'input_order_fixed':INPUTS,'records':records,'first_fixed_input_counterexample':failure,
              'new_ESC_range_verification':False,'Hlog_refuted':False,'universal_existence_proved':False,
              'elapsed_seconds':round(time.monotonic()-START,3)}
    (RUN / 'kneser-budget-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='first_fixed_input_counterexample'}),flush=True)
    if failure:
        print(json.dumps({'counterexample_summary':{k:v for k,v in failure.items() if k!='actual_successes'}},indent=2))
        print(json.dumps({'first_actual_success':failure['actual_successes'][0] if failure['actual_successes'] else None},indent=2))

if __name__=='__main__':
    main()
