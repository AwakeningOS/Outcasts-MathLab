"""Test C(p)<=3G(p) using existing exact-cost records and independent audits."""
import argparse
import hashlib
import importlib.util
import json
import math
from pathlib import Path
import platform
import time


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--source-dir', required=True)
    parser.add_argument('--output', required=True)
    args = parser.parse_args()
    start = time.monotonic()
    base = Path(args.source_dir)
    spec = importlib.util.spec_from_file_location('budget', base / 'explore_witness_budget.py')
    budget = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(budget)
    selected, total, sources = [], 0, []
    for filename, expected in [
        ('results.json', 'ee23c2187252324c85a4c8fb756301a394b2783c4d62fb6929120cd7e410a70f'),
        ('results-2m-100m.json', '32f56343f1a8df5e1296b90079ad7c387dea7cb17e6f22ad1dc82f5b9a014010')]:
        result = json.loads((base / filename).read_text())
        rows = result['rows']
        actual = hashlib.sha256(json.dumps(rows, sort_keys=True,
                                           separators=(',', ':')).encode()).hexdigest()
        if actual != expected or actual != result['summary']['rows_sha256']:
            raise ValueError('Source row checksum mismatch')
        total += len(rows)
        sources.append(dict(filename=filename, rows=len(rows), rows_sha256=actual))
        for row in rows:
            if not row['hypothesis_holds'] or row['witness'] is None:
                raise ValueError('Input set contains unresolved cost')
            if row['witness']['cost'] > 12:
                selected.append(row)
    if not selected:
        raise ValueError('No selected input')
    largest = max(r['p'] * r['witness']['cost'] + r['witness']['cost'] for r in selected)
    budget.init_worker(budget.primes_to(math.isqrt(largest)))
    observations = []
    for row in selected:
        p, cost = row['p'], row['witness']['cost']
        if p < 2 or any(p % d == 0 for d in range(2, math.isqrt(p) + 1)):
            raise ValueError('Selected input is not prime')
        audit = budget.audit_counterexample(p, cost - 1)
        hit, _ = budget.search(p, cost)
        if hit is None or hit['cost'] != cost:
            raise ValueError('Exact cost replay disagreed')
        eligible = [entry for entry in audit['pair_failures']
                    if entry['modulus'] - 1 in entry['unit_subgroup']]
        group_cost = min((entry['cost'] for entry in eligible), default=cost)
        first = [entry for entry in eligible if entry['cost'] == group_cost]
        observations.append(dict(p=p, C=cost, G=group_cost,
                                 triple_budget=3 * group_cost,
                                 hypothesis_holds=cost <= 3 * group_cost,
                                 first_group_candidates=first,
                                 successful_witness=hit,
                                 negative_audit=audit))
    result = dict(hypothesis='For every target prime with finite G(p), C(p)<=3*G(p)',
                  selection='All existing exact-cost rows with C>12; lower costs cannot '
                  'violate this bound because subgroup and divisor tests coincide '
                  'at costs 1,2,3 (unit groups modulo 4,8,12 have exponent at most 2)',
                  source_target_primes=total, sources=sources,
                  selected_inputs=len(selected),
                  failures=sum(not r['hypothesis_holds'] for r in observations),
                  observations=observations, python=platform.python_version(),
                  elapsed_seconds=time.monotonic() - start,
                  universal_ESC_claim=False, lean_verified=False)
    Path(args.output).write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'observations'}), flush=True)
    for row in observations:
        print(json.dumps({k: v for k, v in row.items() if k != 'negative_audit'}), flush=True)


if __name__ == '__main__':
    main()
