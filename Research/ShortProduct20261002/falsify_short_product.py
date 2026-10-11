"""Test a pointwise short-product witness hypothesis, not ESC itself."""
import argparse
import concurrent.futures
import hashlib
import importlib.util
import json
import math
from pathlib import Path
import platform
import time

BASE = None
PAIRS = {}

def initialize(module_path, trial):
    global BASE
    spec = importlib.util.spec_from_file_location('budget', module_path)
    BASE = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(BASE)
    BASE.init_worker(trial)

def pairs(b):
    if b not in PAIRS:
        PAIRS[b] = BASE.parameter_pairs(b)
    return PAIRS[b]

def short_hit(fs, modulus):
    unit_primes = [q for q, _ in fs if math.gcd(q, modulus) == 1]
    for q in unit_primes:
        if q % modulus == modulus - 1:
            return q
    for i, q in enumerate(unit_primes):
        for r in unit_primes[i+1:]:
            if q * r % modulus == modulus - 1:
                return q * r
    # q^2 is never -1 mod a multiple of 4, so repeated-prime pairs cannot hit.
    return None

def analyze(row):
    p, b = row['p'], row['budget']
    for cost, a, u in pairs(b):
        fs = BASE.factor(a*p+u)
        s = short_hit(fs, 4*cost)
        if s is not None:
            return dict(p=p, budget=b, holds=True,
                        witness=BASE.witness(p,a,u,s),
                        witness_factorization=BASE.factor(s))
    return dict(p=p, budget=b, holds=False, previous_full_witness=row['witness'])

def independent_factor(n):
    fs = []
    d = 2
    while d*d <= n:
        e = 0
        while n % d == 0:
            e += 1
            n //= d
        if e:
            fs.append((d,e))
        d += 1
    if n > 1:
        fs.append((n,1))
    return fs

def replay_failure(row):
    p, b = row['p'], row['budget']
    if p < 2 or any(p%d == 0 for d in range(2,math.isqrt(p)+1)):
        raise ValueError('Selected counterexample not prime')
    records, min_omega = [], None
    for cost,a,u in pairs(b):
        M, modulus = a*p+u, 4*cost
        fs = BASE.factor(M)
        independent_fs = independent_factor(M)
        if fs != independent_fs or math.prod(q**e for q,e in fs) != M:
            raise ValueError('Independent factor replay disagreed')
        ds = BASE.divisors(fs)
        independent_ds = BASE.independent_divisors(M)
        if set(ds) != independent_ds:
            raise ValueError('Independent all-divisor replay disagreed')
        hits=[]
        for s in ds:
            if s % modulus == modulus-1:
                sf=independent_factor(s)
                omega=sum(e for _,e in sf)
                if omega <= 2:
                    raise ValueError('Short-product counterexample replay failed')
                w=BASE.witness(p,a,u,s)
                hit=dict(witness=w, factorization=sf, omega=omega)
                hits.append(hit)
                if min_omega is None or (omega,cost,s)<(min_omega['omega'],min_omega['witness']['cost'],min_omega['witness']['s']):
                    min_omega=hit
        unit=[q%modulus for q,_ in fs if math.gcd(q,modulus)==1]
        short_residues=sorted(set([1]+unit+[x*y%modulus for i,x in enumerate(unit) for y in unit[i+1:]]))
        if modulus-1 in short_residues:
            raise ValueError('Prime-pair check disagreed')
        obs=dict(a=a,u=u,cost=cost,M=M,modulus=modulus,factorization=fs,
                 unit_prime_residues=unit,short_product_residues=short_residues,
                 all_actual_divisor_residues=sorted({s%modulus for s in ds}),
                 all_actual_witnesses=hits)
        obs.update(BASE.residue_obstruction(obs))
        if hits:
            obs['obstruction'] = 'actual_witness_requires_at_least_three_factors'
        records.append(obs)
    if min_omega is None:
        raise ValueError('Original Hlog witness was not reproduced')
    C = min(entry['cost'] for entry in records if entry['all_actual_witnesses'])
    G = min(entry['cost'] for entry in records if entry['modulus']-1 in entry['unit_subgroup'])
    return dict(p=p,budget=b,coprime_pairs=len(records),min_omega=min_omega,C=C,G=G,
                independently_factored_and_enumerated=True,pairs=records)

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--source-dir',required=True)
    parser.add_argument('--workers',type=int,default=8)
    parser.add_argument('--output',required=True)
    args=parser.parse_args()
    start=time.monotonic()
    root=Path(args.source_dir)
    spec=importlib.util.spec_from_file_location('original',root/'explore_witness_budget.py')
    original=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(original)
    rows,sources=[],[]
    for name,expected in [('results.json','ee23c2187252324c85a4c8fb756301a394b2783c4d62fb6929120cd7e410a70f'),
                          ('results-2m-100m.json','32f56343f1a8df5e1296b90079ad7c387dea7cb17e6f22ad1dc82f5b9a014010')]:
        data=json.loads((root/name).read_text())
        digest=hashlib.sha256(json.dumps(data['rows'],sort_keys=True,separators=(',',':')).encode()).hexdigest()
        if digest != expected or digest != data['summary']['rows_sha256']:
            raise ValueError('Source checksum mismatch')
        rows.extend(data['rows'])
        sources.append(dict(file=name,rows=len(data['rows']),rows_sha256=digest))
    if any(not r['hypothesis_holds'] or r['budget'] != (r['p']-1).bit_length()
           or r['p']%840 not in original.RESIDUES for r in rows):
        raise ValueError('Source domain or original budget mismatch')
    upper=max(r['budget']*r['p']+r['budget'] for r in rows)
    trial=original.primes_to(math.isqrt(upper))
    initialize(str(root/'explore_witness_budget.py'),trial)
    known,selected=[],[]
    original_omega_hist={}
    for row in rows:
        w=row['witness']
        original.witness(row['p'],w['a'],w['u'],w['s'])
        sf=BASE.factor(w['s'])
        omega=sum(e for _,e in sf)
        original_omega_hist[omega]=original_omega_hist.get(omega,0)+1
        if omega<=2:
            known.append(dict(p=row['p'],budget=row['budget'],holds=True,witness=w,
                              witness_factorization=sf,source='previous_exact_witness'))
        else:
            selected.append(row)
    print(json.dumps(dict(event='started',source_inputs=len(rows),already_certified=len(known),
                          additional_inputs=len(selected),workers=args.workers)),flush=True)
    with concurrent.futures.ProcessPoolExecutor(max_workers=args.workers,initializer=initialize,
                                               initargs=(str(root/'explore_witness_budget.py'),trial)) as pool:
        new=list(pool.map(analyze,selected,chunksize=32))
    failures=sorted([r for r in new if not r['holds']],key=lambda r:r['p'])
    initialize(str(root/'explore_witness_budget.py'),trial)
    audits=[replay_failure(row) for row in failures[:3]]
    # Already-certified inputs remain in the pinned original public source logs.
    # Store every newly tested input here rather than duplicating those source rows.
    allrows=sorted(new,key=lambda r:r['p'])
    result=dict(hypothesis='Every target prime has a coprime Type-II divisor witness with a*u<=ceil(log2 p) and Omega(s)<=2',
                sources=sources,source_inputs=len(rows),already_certified=len(known),additional_inputs=len(selected),
                failures=len(failures),first_failures=failures[:10],original_witness_omega_histogram=original_omega_hist,
                independent_failure_audits=audits,rows=allrows,
                row_scope='All additional inputs; prior short witnesses are in the pinned original source logs',
                python=platform.python_version(),workers=args.workers,
                elapsed_seconds=time.monotonic()-start,universal_ESC_claim=False,lean_verified=False)
    Path(args.output).write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ['rows','independent_failure_audits']},sort_keys=True),flush=True)
    for audit in audits:
        print(json.dumps({k:v for k,v in audit.items() if k!='pairs'},sort_keys=True),flush=True)

if __name__=='__main__':
    main()
