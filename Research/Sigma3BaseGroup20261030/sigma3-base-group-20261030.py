"""Exact group vs bounded-divisor diagnostic on a fixed previously saved root."""
import hashlib
import json
import math
import time
from collections import Counter
from pathlib import Path

start=time.monotonic()
r=Path(__file__).resolve().parent
source=Path('/mnt/hdd1t/outcasts-reply-20261029-8AcltR/e1-replay-results.json')
blob=source.read_bytes()
assert hashlib.sha256(blob).hexdigest()=='a817fff69c78371c4e0e0911d9b4947bdd38e428dba179d375f95b71331fc463'
data=json.loads(blob)
p=data['summary']['p']
assert p==42698041
rows=data['root_sources']
assert len(rows)==510
counts=Counter()
examples={}
details=[]
for row in rows:
    assert row['q']==41
    m=123
    x=row['x']
    fac=row['factors']
    assert math.prod(g**e for g,e in fac)==x
    assert x%3==1 and pow(x,20,41)==40 and math.gcd(x,m)==1
    K={1}
    queue=[1]
    for a in queue:
        for g,e in fac:
            v=a*g % m
            if v not in K:
                K.add(v)
                queue.append(v)
    condition=any(g%3==2 for g,e in fac)
    ii=(-x)%m in K
    i=(-p*x)%m in K
    assert (122 in K)==condition==ii
    if condition:
        assert 80%len(K)==0 and (80//len(K))%2==1
        assert i==(4 in K)
    else:
        assert not i
    divs=[1]
    for g,e in fac:
        divs=[a*g**j for a in divs for j in range(2*e+1)]
    hits=sorted(d for d in divs if (d+x)%m==0)
    assert not row['hits']['I'] and not row['hits']['II']
    kind='group_blocked' if not ii else ('base_pass_full_fail' if hits else 'group_pass_base_divisor_fail')
    entry=dict(tau=row['tau'],c=row['c'],x=x,factors=fac,K_size=len(K),
               group_index=80//len(K),factor_2_mod3=condition,TypeII_in_K=ii,TypeI_in_K=i,
               actual_base_hits=hits,kind=kind)
    counts[kind]+=1
    if kind not in examples:
        examples[kind]=dict(entry,K=sorted(K),divisors_x_squared=sorted(divs),
                            divisor_residues_mod123=sorted({d%m for d in divs}))
    details.append(entry)
    assert time.monotonic()-start<30
summary=dict(p=p,q=41,base_modulus=123,sources=510,all_group_equivalences_match=True,
             counts=dict(counts),examples=examples,seconds=time.monotonic()-start,
             new_prime_scan=False,new_full_modulus_replay=False,Lean_executed=False,
             source_sha256=hashlib.sha256(blob).hexdigest(),
             code_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
(r/'sigma3-base-group-results.json').write_text(json.dumps(dict(summary=summary,rows=details),indent=2)+'\n')
(r/'sigma3-base-group-summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
