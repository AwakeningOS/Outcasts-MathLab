import hashlib
import json
import math
import time
from fractions import Fraction as Q
from pathlib import Path

run = Path('/mnt/hdd1t/outcasts-reply-20261014-Dgn34n')
source = Path('/mnt/hdd1t/outcasts-reply-20261013-ks9Uhb/check-residual-20261013.py')
namespace = {}
# Reuse reviewed definitions only: never execute yesterday's output-producing loop.
exec(compile(source.read_text().split('\nrows=[]; summaries=[]')[0], str(source), 'exec'), namespace)
start = time.monotonic()


def serial(x):
    if isinstance(x, Q):
        return str(x)
    if isinstance(x, dict):
        return {str(k): serial(v) for k, v in x.items()}
    if isinstance(x, (list, tuple)):
        return [serial(v) for v in x]
    return x


def slack_info(row):
    slack = row['signed_complex'] - row['complex_triangle_lower']
    b = row['V'] - row['factor_only_K']
    assert slack >= 0
    assert b == min(row['V'], max(Q(0), row['W'] - slack))
    assert (b > 0) == (row['V'] > 0 and row['W'] > slack)
    # The actual-divisor restriction supplies the compatibility omitted by arbitrary scalars.
    assert row['V'] >= Q(2 * row['W'], row['phi'])
    row.update({'approximation_slack': slack, 'capped_certificate_gap': b})
    return row


previous_rows = json.loads(Path('/mnt/hdd1t/outcasts-reply-20261013-ks9Uhb/residual-audit-rows.json').read_text())
previous_sharp = json.loads(Path('/mnt/hdd1t/outcasts-reply-20261013-ks9Uhb/residual-audit-results.json').read_text())['sharpness_pair']
prior_summaries = []
for p in [66529, 18490201, 1201]:
    data = [r for r in previous_rows + [previous_sharp] if r['p'] == p]
    for row in data:
        for k in ['signed_complex', 'complex_triangle_lower', 'V', 'factor_only_K', 'W']:
            row[k] = Q(row[k])
        slack_info(row)
    prior_summaries.append({'p': p, 'rows': len(data), 'sum_slack': sum((r['approximation_slack'] for r in data), Q(0)), 'positive_slack_rows': sum(r['approximation_slack'] > 0 for r in data), 'nonconstant_pairs': sum(len(pair['signed_pair_poly']) > 1 for r in data for pair in r['complex_pairs']), 'W_above_slack_pairs': [[r['a'], r['u']] for r in data if r['W'] > r['approximation_slack']]})

all_rows = []
boxes = []
failed_data = None
inputs = [84525841, 8615161, 53722321, 345601, 670849, 1740481, 3678481, 5843041]
for p in inputs:
    assert namespace['direct'](p) == [1, p] and p % 840 in {1, 121, 169, 289, 361, 529}
    B = (p - 1).bit_length()
    data = []
    for a in range(1, B + 1):
        for u in range(1, B // a + 1):
            if math.gcd(a, u) != 1:
                continue
            assert time.monotonic() - start < 120
            row = namespace['factor_certificate'](p, a, u)
            divisors = namespace['direct'](row['N'])
            assert divisors == namespace['old'].divisors(row['factors'])
            witnesses = [s for s in divisors if (s + 1) % row['m'] == 0]
            assert len(witnesses) == row['factor_character_count']
            row.update({'W': len(witnesses), 'witnesses': witnesses})
            data.append(slack_info(row))
    gap = sum((r['capped_certificate_gap'] for r in data), Q(0))
    record = {'p': p, 'B': B, 'pairs': len(data), 'sum_V': sum((r['V'] for r in data), Q(0)), 'sum_K': sum((r['factor_only_K'] for r in data), Q(0)), 'gap': gap, 'Wtot': sum(r['W'] for r in data), 'successful_pairs': [[r['a'], r['u']] for r in data if r['W'] > 0], 'sum_slack': sum((r['approximation_slack'] for r in data), Q(0)), 'positive_certificate_pairs': [[r['a'], r['u']] for r in data if r['capped_certificate_gap'] > 0]}
    assert gap >= 0
    boxes.append(record)
    all_rows.extend(data)
    if gap == 0:
        failed_data = data
        break


def mobius(n):
    fs = namespace['old'].factor(n)
    return 0 if any(e > 1 for q, e in fs) else (-1) ** len(fs)


def ramanujan(d, j):
    return sum(h * mobius(d // h) for h in namespace['old'].divisors(namespace['old'].factor(math.gcd(d, j))))


def orbit_audit(row):
    m, L = row['m'], row['root_order']
    L2, chars = namespace['character_data'](m)
    assert L2 == L
    units = sorted(chars[0]['phases'])
    lookup = {tuple(c['phases'][r] for r in units): c for c in chars}
    seen = set()
    orbits = []
    for c in chars:
        key = c['param']
        if c['real'] or key in seen:
            continue
        g = math.gcd(L, *c['phases'].values())
        d = L // g
        assert d > 2
        orbit = [lookup[tuple(k * c['phases'][r] % L for r in units)] for k in range(1, d + 1) if math.gcd(k, d) == 1]
        assert len({z['param'] for z in orbit}) == namespace['phi'](d)
        assert all(z['sign'] == c['sign'] for z in orbit)
        seen.update(z['param'] for z in orbit)
        coeffs = [1] + [0] * (d - 1)
        for q, e in row['factors']:
            if q == 2:
                continue
            phase = c['phases'][q % m] // g
            local = [0] * d
            for j in range(e + 1):
                local[j * phase % d] += 1
            coeffs = namespace['cyclic_mul'](coeffs, local, d)
        trace = c['sign'] * sum(value * ramanujan(d, j) for j, value in enumerate(coeffs))
        polynomial = [0]
        for z in orbit:
            poly = [1] + [0] * (L - 1)
            for q, e in row['factors']:
                if q == 2:
                    continue
                local = [0] * L
                for j in range(e + 1):
                    local[j * z['phases'][q % m] % L] += 1
                poly = namespace['cyclic_mul'](poly, local, L)
            polynomial = namespace['add'](polynomial, [c['sign'] * x for x in poly])
        reduced = namespace['reduce'](polynomial, L)
        assert reduced == [trace]
        orbits.append({'representative_param': key, 'order': d, 'size': len(orbit), 'sign': c['sign'], 'phase_coefficients': coeffs, 'trace_numerator': trace})
    assert len(seen) == sum(not c['real'] for c in chars)
    exact_complex = Q(sum(o['trace_numerator'] for o in orbits), row['phi'])
    assert exact_complex == row['signed_complex']
    exact_H = row['other_even_real'] - row['other_odd_real'] + exact_complex
    exact_K = min(row['V'], max(Q(0), -exact_H))
    assert row['V'] - exact_K == min(row['V'], row['W'])
    return {'p': row['p'], 'a': row['a'], 'u': row['u'], 'm': m, 'orbits': orbits, 'signed_complex': exact_complex, 'orbit_slack': '0', 'old_slack': row['approximation_slack'], 'old_gap': row['capped_certificate_gap'], 'orbit_gap': row['V'] - exact_K, 'W': row['W'], 'V': row['V']}


selection = failed_data if failed_data is not None else [r for r in all_rows if r['p'] == inputs[0]]
chosen = next((r for r in selection if r['W'] > 0 and r['approximation_slack'] > 0), next(r for r in selection if r['W'] > 0))
obstruction = slack_info(namespace['audit_pair'](18490201, 1, 14))
orbit_checks = [orbit_audit(chosen), orbit_audit(obstruction)]
participant = json.loads((run / 'participant-source-20261014.json').read_text())
fs = participant['files']
hashes = dict(line.split('  ', 1)[::-1] for line in fs['SHA256SUMS'].splitlines())
assert len(hashes) == 10
assert all(hashlib.sha256(fs[name].encode()).hexdigest() == expected for name, expected in hashes.items())
reported = json.loads(fs['delta58_results.json'])
for r in prior_summaries:
    claim = reported[str(r['p'])]
    assert str(r['sum_slack']) == claim['sum_delta58']
    assert r['rows'] == claim['rows'] and r['positive_slack_rows'] == claim['rows_with_positive_delta58']
    assert r['nonconstant_pairs'] == claim['nonconstant_complex_pairs_total']
    assert len(r['W_above_slack_pairs']) == claim['rows_with_W_gt_delta58']
ownlog = Path('/mnt/hdd1t/outcasts-reply-20261013-ks9Uhb/ResidualAccounting20261013.log').read_text()
assert fs['lean/ResidualAccounting20261013.luna.log'] == ownlog
result = {'contract': 'slack-certificate-contract-20261014.md', 'fixed_inputs': inputs, 'completed_boxes': boxes, 'stopped_on_first_zero_gap': failed_data is not None, 'untested_remaining_inputs': inputs[len(boxes):], 'prior113_slack_identity_checks': prior_summaries, 'orbit_checks': orbit_checks, 'participant_source_sha': participant['sha'], 'participant10_payload_hashes_matched': True, 'participant_axiom_log_byte_matches': True, 'participant_script_executed': False, 'new_general_existence_proved': False, 'Hlog_or_ESC_refuted': False, 'source_helper_sha256': hashlib.sha256(source.read_bytes()).hexdigest(), 'seconds': round(time.monotonic() - start, 3)}
(run / 'slack-certificate-results.json').write_text(json.dumps(serial(result), indent=2) + '\n')
(run / 'slack-certificate-rows.json').write_text(json.dumps(serial(all_rows), indent=2) + '\n')
print(json.dumps(serial(result), indent=2))
