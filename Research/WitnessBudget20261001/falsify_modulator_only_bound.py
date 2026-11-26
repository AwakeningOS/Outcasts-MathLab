"""Test a new pointwise restriction using prior witness records, not a new ESC sweep."""
import argparse
import concurrent.futures
import hashlib
import importlib.util
import json
import math
from pathlib import Path
import platform
import time

LIB = None


def init_worker(source_dir, prime_bound):
    global LIB
    spec = importlib.util.spec_from_file_location('budget', Path(source_dir) / 'explore_witness_budget.py')
    LIB = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(LIB)
    LIB.init_worker(LIB.primes_to(prime_bound))


def analyze(p):
    B = (p - 1).bit_length()
    failures = []
    for a in range(1, B + 1):
        M, modulus = a * p + 1, 4 * a
        fs = LIB.factor(M)
        ds = LIB.divisors(fs)
        hits = [s for s in ds if (s + 1) % modulus == 0]
        if hits:
            return dict(p=p, budget=B, holds=True, witness=LIB.witness(p, a, 1, hits[0]))
        failures.append(dict(a=a, u=1, M=M, modulus=modulus, factorization=fs,
                             divisor_residues=sorted({s % modulus for s in ds})))
    return dict(p=p, budget=B, holds=False, negative_pairs=failures)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--source-dir', required=True)
    parser.add_argument('--output', required=True)
    parser.add_argument('--workers', type=int, default=8)
    args = parser.parse_args()
    start = time.monotonic()
    base = Path(args.source_dir)
    existing = []
    sources = []
    for filename, expected in [
        ('results.json', 'ee23c2187252324c85a4c8fb756301a394b2783c4d62fb6929120cd7e410a70f'),
        ('results-2m-100m.json', '32f56343f1a8df5e1296b90079ad7c387dea7cb17e6f22ad1dc82f5b9a014010')]:
        data = json.loads((base / filename).read_text())
        rows = data['rows']
        actual = hashlib.sha256(json.dumps(rows, sort_keys=True,
                                           separators=(',', ':')).encode()).hexdigest()
        if actual != expected or actual != data['summary']['rows_sha256']:
            raise ValueError('Source row checksum mismatch')
        existing.extend(rows)
        sources.append(dict(filename=filename, rows_sha256=actual))
    ps = sorted(r['p'] for r in existing if r['witness']['u'] != 1)
    prior = {r['p']: r['witness'] for r in existing}
    largest_p = max(ps)
    prime_bound = math.isqrt(largest_p * (largest_p - 1).bit_length() + 1)
    print(json.dumps(dict(event='started', source_rows=len(existing), new_inputs=len(ps),
                          workers=args.workers)), flush=True)
    with concurrent.futures.ProcessPoolExecutor(max_workers=args.workers,
                                               initializer=init_worker,
                                               initargs=(args.source_dir, prime_bound)) as pool:
        rows = list(pool.map(analyze, ps, chunksize=32))
    bad = [r for r in rows if not r['holds']]
    audits = []
    init_worker(args.source_dir, prime_bound)
    for row in bad[:3]:
        p = row['p']
        if any(p % d == 0 for d in range(2, math.isqrt(p) + 1)):
            raise ValueError('Counterexample input is not prime')
        for entry in row['negative_pairs']:
            ds = LIB.independent_divisors(entry['M'])
            actual = sorted({s % entry['modulus'] for s in ds})
            if actual != entry['divisor_residues'] or entry['modulus'] - 1 in actual:
                raise ValueError('Independent counterexample replay disagreed')
        positive = prior[p]
        LIB.witness(p, positive['a'], positive['u'], positive['s'])
        audits.append(dict(p=p, budget=row['budget'],
                           independently_checked_pairs=len(row['negative_pairs']),
                           negative_pairs=row['negative_pairs'],
                           full_type_II_positive_witness=positive,
                           independent_replay=True))
    summary = dict(hypothesis='Every target prime has a divisor witness with u=1 '
                   'and a<=ceil(log2 p)', source_target_primes=len(existing),
                   prior_u1_witnesses=len(existing)-len(ps), new_inputs=len(ps),
                   failures=len(bad), first_failures=[dict(p=r['p'], budget=r['budget'])
                                                     for r in bad[:10]],
                   sources=sources, independently_audited_failures=len(audits),
                   python=platform.python_version(), workers=args.workers,
                   elapsed_seconds=time.monotonic()-start,
                   universal_ESC_claim=False, lean_verified=False)
    result = dict(summary=summary, rows=rows, counterexample_audits=audits)
    Path(args.output).write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps(summary, sort_keys=True), flush=True)
    for audit in audits:
        print(json.dumps({k: v for k, v in audit.items() if k != 'negative_pairs'}), flush=True)


if __name__ == '__main__':
    main()
