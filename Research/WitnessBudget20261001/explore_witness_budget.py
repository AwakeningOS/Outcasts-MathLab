"""Falsify a pointwise logarithmic witness-budget hypothesis, not ESC itself."""
import argparse
import concurrent.futures
import hashlib
import json
import math
import platform
import time

RESIDUES = {1, 121, 169, 289, 361, 529}
TRIAL_PRIMES = []


def primes_to(n):
    flags = bytearray(b'\x01') * (n + 1)
    flags[:2] = b'\x00\x00'
    for q in range(2, math.isqrt(n) + 1):
        if flags[q]:
            flags[q * q:n + 1:q] = b'\x00' * ((n - q * q) // q + 1)
    return [q for q, yes in enumerate(flags) if yes]


def init_worker(primes):
    global TRIAL_PRIMES
    TRIAL_PRIMES = primes


def factor(n):
    result = []
    for q in TRIAL_PRIMES:
        if q * q > n:
            break
        exponent = 0
        while n % q == 0:
            n //= q
            exponent += 1
        if exponent:
            result.append((q, exponent))
    if n > 1:
        result.append((n, 1))
    return result


def divisors(factors):
    ds = [1]
    for q, e in factors:
        old = ds[:]
        power = 1
        for _ in range(e):
            power *= q
            ds.extend(d * power for d in old)
    return sorted(ds)


def parameter_pairs(budget):
    return sorted((a * u, a, u) for a in range(1, budget + 1)
                  for u in range(1, budget // a + 1) if math.gcd(a, u) == 1)


def witness(p, a, u, s):
    modulus = 4 * a * u
    if (s + 1) % modulus or (a * p + u) % s:
        raise ValueError('Invalid divisor witness')
    alpha, v = (s + 1) // modulus, (a * p + u) // s
    if a * p + u + v != 4 * a * alpha * u * v:
        raise ValueError('Parameter identity failed')
    xyz = sorted((alpha * u * v, a * alpha * u * p, a * alpha * v * p))
    x, y, z = xyz
    if min(xyz) <= 0 or 4 * x * y * z != p * (x * y + x * z + y * z):
        raise ValueError('Integer ESC identity failed')
    return dict(a=a, u=u, cost=a * u, s=s, v=v, alpha=alpha, xyz=xyz)


def search(p, budget, certificate=False):
    failures = []
    for cost, a, u in parameter_pairs(budget):
        m, modulus = a * p + u, 4 * a * u
        fs = factor(m)
        ds = divisors(fs)
        hits = [s for s in ds if (s + 1) % modulus == 0]
        if hits:
            return witness(p, a, u, hits[0]), failures
        if certificate:
            failures.append(dict(a=a, u=u, cost=cost, M=m, modulus=modulus,
                                 factorization=fs,
                                 divisor_residues=sorted({s % modulus for s in ds})))
    return None, failures


def analyze(p):
    budget = (p - 1).bit_length()  # exact ceil(log2 p), no floating point
    hit, _ = search(p, budget)
    row = dict(p=p, budget=budget, hypothesis_holds=hit is not None, witness=hit)
    if hit is None:
        fallback, _ = search(p, 4 * budget)
        row['fallback_budget'] = 4 * budget
        row['fallback_witness'] = fallback
    return row


def independent_divisors(n):
    # Independent trial of all integers up to sqrt(n), without factorization.
    ds = set()
    for d in range(1, math.isqrt(n) + 1):
        if n % d == 0:
            ds.update((d, n // d))
    return ds


def residue_obstruction(entry):
    modulus = entry['modulus']
    generators = [q % modulus for q, _ in entry['factorization']
                  if math.gcd(q, modulus) == 1]
    subgroup, pending = {1}, [1]
    while pending:
        residue = pending.pop()
        for q in generators:
            product = residue * q % modulus
            if product not in subgroup:
                subgroup.add(product)
                pending.append(product)
    return dict(unit_subgroup=sorted(subgroup),
                obstruction=('group_excludes_minus_one' if modulus - 1 not in subgroup
                             else 'finite_exponent_shortage'))


def audit_counterexample(p, budget):
    hit, cert = search(p, budget, certificate=True)
    if hit is not None:
        raise ValueError('Counterexample replay found a witness')
    for entry in cert:
        ds = independent_divisors(entry['M'])
        residues = sorted({s % entry['modulus'] for s in ds})
        if residues != entry['divisor_residues'] or entry['modulus'] - 1 in residues:
            raise ValueError('Independent divisor replay disagreed')
        entry.update(residue_obstruction(entry))
    all_pairs = 0
    for a in range(1, budget + 1):
        for u in range(1, budget // a + 1):
            all_pairs += 1
            if any((s + 1) % (4 * a * u) == 0
                   for s in independent_divisors(a * p + u)):
                raise ValueError('Non-coprime-inclusive replay found a witness')
    counts = {label: sum(entry['obstruction'] == label for entry in cert)
              for label in ('group_excludes_minus_one', 'finite_exponent_shortage')}
    return dict(p=p, budget=budget, checked_coprime_pairs=len(cert),
                checked_all_positive_pairs=all_pairs,
                obstruction_counts=counts, independent_replay=True, pair_failures=cert)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--limit', type=int, default=2_000_000)
    parser.add_argument('--start', type=int, default=8)
    parser.add_argument('--workers', type=int, default=8)
    parser.add_argument('--audit-prime', type=int)
    parser.add_argument('--audit-budget', type=int)
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    start = time.monotonic()
    if args.audit_prime is not None:
        if args.audit_budget is None or args.audit_budget < 1:
            parser.error('--audit-prime requires a positive --audit-budget')
        p, budget = args.audit_prime, args.audit_budget
        if p < 2 or any(p % d == 0 for d in range(2, math.isqrt(p) + 1)):
            raise ValueError('Audit input is not prime')
        init_worker(primes_to(math.isqrt((budget + 1) * p + budget + 1)))
        result = audit_counterexample(p, budget)
        hit, _ = search(p, budget + 1)
        result['next_budget_witness'] = hit
        result['elapsed_seconds'] = time.monotonic() - start
        with open(args.output, 'w', encoding='utf-8') as f:
            json.dump(result, f, indent=2, sort_keys=True)
            f.write('\n')
        print(json.dumps({k: v for k, v in result.items() if k != 'pair_failures'},
                         sort_keys=True), flush=True)
        return
    max_budget = (args.limit - 1).bit_length()
    trial = primes_to(math.isqrt(4 * max_budget * args.limit + 4 * max_budget))
    ps = [p for p in primes_to(args.limit) if p >= args.start and p > 7 and p % 840 in RESIDUES]
    print(json.dumps(dict(event='started',primes=len(ps),limit=args.limit,
                          workers=args.workers)), flush=True)
    with concurrent.futures.ProcessPoolExecutor(max_workers=args.workers,
                                               initializer=init_worker,
                                               initargs=(trial,)) as pool:
        rows = list(pool.map(analyze, ps, chunksize=32))
    failed = [r for r in rows if not r['hypothesis_holds']]
    init_worker(trial)
    audits = [audit_counterexample(r['p'], r['budget']) for r in failed[:3]]
    hist = {}
    for row in rows:
        if row['witness']:
            cost = str(row['witness']['cost'])
            hist[cost] = hist.get(cost, 0) + 1
    records = json.dumps(rows, sort_keys=True, separators=(',', ':')).encode()
    summary = dict(hypothesis='For every prime p in the six mod-840 residual classes, '
                   'there is a Type-II divisor witness with a*u<=ceil(log2 p)',
                   start=args.start, limit=args.limit, residues=sorted(RESIDUES), target_primes=len(ps),
                   failures=len(failed), first_failures=failed[:10], cost_histogram=hist,
                   max_observed_min_cost=max((r['witness']['cost'] for r in rows
                                             if r['witness']), default=0),
                   rows_sha256=hashlib.sha256(records).hexdigest(),
                   elapsed_seconds=time.monotonic()-start, python=platform.python_version(),
                   workers=args.workers, universal_ESC_claim=False)
    result = dict(summary=summary, rows=rows, counterexample_audits=audits)
    with open(args.output, 'w', encoding='utf-8') as f:
        json.dump(result, f, indent=2, sort_keys=True)
        f.write('\n')
    print(json.dumps(summary, sort_keys=True), flush=True)


if __name__ == '__main__':
    main()
