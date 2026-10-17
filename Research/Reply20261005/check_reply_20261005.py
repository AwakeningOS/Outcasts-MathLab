#!/usr/bin/env python3
"""Exact two-method divisor audit for Outcasts #27. CPU run on mini only."""
import argparse
import gzip
import hashlib
import json
import math
from pathlib import Path
import time

P = 1740481

def primes_to(n):
    flags = bytearray(b'\x01') * (n+1)
    flags[:2] = b'\x00\x00'
    for q in range(2, math.isqrt(n)+1):
        if flags[q]:
            flags[q*q:n+1:q] = b'\x00' * ((n-q*q)//q+1)
    return [q for q in range(2,n+1) if flags[q]]

def prime_progression_factors(p, u, cap, root):
    residual = [0] + [a*p+u for a in range(1,cap+1)]
    factors = [[] for _ in range(cap+1)]
    for q in primes_to(root):
        r = (-u*pow(p,-1,q)) % q
        first = r if r else q
        for a in range(first,cap+1,q):
            exponent = 0
            while residual[a] % q == 0:
                residual[a] //= q
                exponent += 1
            if exponent:
                factors[a].append((q,exponent))
    for a in range(1,cap+1):
        if residual[a]>1:
            factors[a].append((residual[a],1))
        assert math.prod(q**e for q,e in factors[a]) == a*p+u
    return factors

def expand_divisors(factors):
    ds = [1]
    for q,e in factors:
        ds = [d*q**j for d in ds for j in range(e+1)]
    return sorted(ds)

def transposed_all_integer_divisors(p,u,cap,root):
    ds = [[] for _ in range(cap+1)]
    for d in range(1,root+1):
        residue = (-u*pow(p,-1,d)) % d if d>1 else 0
        amin = max(1, (d*d-u+p-1)//p)
        first = amin + (residue-amin) % d
        for a in range(first,cap+1,d):
            m = a*p+u
            assert m%d == 0 and d*d<=m
            ds[a].append(d)
            other = m//d
            if other != d:
                ds[a].append(other)
    return ds

def positive_record(p,a,u,s):
    assert (a*p+u)%s==0 and (s+1)%(4*a*u)==0
    alpha=(s+1)//(4*a*u)
    v=(a*p+u)//s
    xyz=sorted([alpha*u*v,a*alpha*u*p,a*alpha*v*p])
    x,y,z=xyz
    assert x>0 and 4*x*y*z==p*(x*y+x*z+y*z)
    return dict(a=a,u=u,s=s,alpha=alpha,v=v,product=a*u,xyz=xyz)

def small_product_exclusion(p,bound):
    rows=[]
    for a in range(1,bound+1):
        for u in range(1,bound//a+1):
            m=a*p+u
            residual=m
            factors=[]
            q=2
            while q*q<=residual:
                e=0
                while residual%q==0:
                    residual//=q
                    e+=1
                if e:
                    factors.append((q,e))
                q+=1
            if residual>1:
                factors.append((residual,1))
            da=expand_divisors(factors)
            db=[]
            for d in range(1,math.isqrt(m)+1):
                if m%d==0:
                    db.append(d)
                    if d*d!=m:
                        db.append(m//d)
            db.sort()
            assert da==db
            ss=[s for s in da if (s+1)%(4*a*u)==0]
            assert not ss, (a,u,ss)
            rows.append(dict(a=a,u=u,m=m,factors=factors,
                             expanded_divisors=da,traversal_divisors=db,witness_s=ss))
    assert len(rows)==29
    return dict(bound=bound,rows=rows,all_divisor_sets_equal=True,no_witness=True)

def audit(p,u,cap,out):
    started=time.monotonic()
    root=math.isqrt(cap*p+u)
    assert p>root
    factors=prime_progression_factors(p,u,cap,root)
    print(f'u={u} factor sieve complete, cap={cap}, root={root}',flush=True)
    traversed=transposed_all_integer_divisors(p,u,cap,root)
    positives=[]
    digest=hashlib.sha256()
    target=out/f'full-u{u}.ndjson.gz'
    divisor_count=0
    with target.open('wb') as raw:
        with gzip.GzipFile(fileobj=raw,mode='wb',mtime=0,filename='') as z:
            for a in range(1,cap+1):
                da=expand_divisors(factors[a])
                db=sorted(traversed[a])
                assert da==db, (p,u,a,da,db)
                assert len(da)==len(set(da))
                ss=[s for s in da if (s+1)%(4*a*u)==0]
                positives.extend(positive_record(p,a,u,s) for s in ss)
                row=dict(p=p,u=u,a=a,m=a*p+u,factors=factors[a],
                         expanded_divisors=da,traversal_divisors=db,witness_s=ss)
                line=(json.dumps(row,sort_keys=True,separators=(',',':'))+'\n').encode()
                digest.update(line)
                z.write(line)
                divisor_count+=len(da)
    result=dict(p=p,u=u,cap=cap,root=root,rows=cap,
                divisor_sets_equal_every_row=True,total_divisors=divisor_count,
                all_witnesses=positives,first_a=min((r['a'] for r in positives),default=None),
                ndjson_sha256=digest.hexdigest(),gzip_sha256=hashlib.sha256(target.read_bytes()).hexdigest(),
                seconds=round(time.monotonic()-started,3))
    print(json.dumps({k:v for k,v in result.items() if k!='all_witnesses'}),flush=True)
    print('first witnesses',json.dumps(positives[:5]),flush=True)
    return result

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    args.output.mkdir(parents=True,exist_ok=True)
    assert all(P%d for d in range(2,math.isqrt(P)+1)), 'p not prime'
    result=dict(p=P,mod840=P%840,budget=(P-1).bit_length(),
                contract='contract.md',execution_host='mini',workers=1,
                methods=['prime-progression factor expansion','transposed exhaustive integer divisor traversal'],
                universal_existence_proof=False,finite_negative_results_lean_formalized=False)
    result['audits']=[audit(P,u,cap,args.output) for u,cap in
                     [(1,101),(2,(P+17)//8),(3,(P+37)//12)]]
    result['cost12_witness']=positive_record(P,3,4,3311)
    result['no_product_below12']=small_product_exclusion(P,11)
    assert result['audits'][0]['first_a'] is not None, 'u1 prefix failed: hold classification'
    assert result['audits'][1]['first_a'] is None, 'u2 absence not reproduced'
    assert result['audits'][2]['first_a']==104, 'u3 first a differs'
    (args.output/'summary.json').write_text(json.dumps(result,indent=2)+'\n')
    print('COMPLETE all rows matched; no universal theorem asserted',flush=True)

if __name__=='__main__':
    main()
