"""Fixed p30241 audit of #128 and a local scope check for #129-130.

Use the saved complete509-vertex closure. Classify both full selectors at all
1434 sources, including noncanonical sources. Check original factor pairs.
In the same data only, find the lexicographically first canonical edge q->r
with sigma(r)=1 for which BOTH vertices have every source fail. Stop the
edge selection at its first match. This tests a local sufficient condition,
not the stronger hypothesis of an all-failing closed set.
"""
from collections import Counter
from fractions import Fraction
from math import gcd,prod
from pathlib import Path
import json,sys


def divs(fs,m=2):
    ds=[1]
    for r,e in fs:ds=[d*r**j for d in ds for j in range(m*e+1)]
    return sorted(ds)


def main():
    data=json.loads(Path(sys.argv[1]).read_text());p=data['p'];assert p==30241
    rows={int(q):ss for q,ss in data['sources'].items()}
    depths={r:z['depth'] for z in data['layers'] for r in z['vertices']}
    tested={};successful=[];kinds=Counter();by_depth=Counter();source_depth=Counter()
    for q in sorted(rows):
        tested[q]=[]
        for s in rows[q]:
            x,c=s['x'],s['c'];assert 4*x==p+c and prod(r**e for r,e in s['factors'])==x
            ds=divs(s['factors']);hits={b:[d for d in ds if (d+k*x)%c==0] for b,k in [('I',p),('II',1)]}
            # Independent equivalent enumeration of the original factor-pair
            # conditions, with the p-adic power retained in {0,1,2}.
            pairhits=[]
            for e in range(3):
                for d in ds:
                    D=p**e*d;S=(p*x)**2//D
                    assert D*S==(p*x)**2
                    if (D+p*x)%c==0 and (S+p*x)%c==0:pairhits.append((e,d))
            assert {d for e,d in pairhits if e==0}==set(hits['I'])
            assert {d for e,d in pairhits if e==1}==set(hits['II'])
            assert {x*x//d for e,d in pairhits if e==2}==set(hits['I'])
            cert=[]
            for branch in ['I','II']:
                for d in hits[branch]:
                    D=d if branch=='I' else p*d;S=(p*x)**2//D
                    den=[x,(D+p*x)//c,(S+p*x)//c]
                    assert sum(Fraction(1,z) for z in den)==Fraction(4,p)
                    cert.append(dict(branch=branch,d=d,denominators=den))
            z=dict(**s,divisor_count=len(ds),hits=hits,certificates=cert)
            tested[q].append(z)
            if any(hits.values()):
                successful.append(dict(**z,depth=depths[q]))
                key='both' if all(hits.values()) else ('I_only' if hits['I'] else 'II_only')
                kinds[key]+=1;source_depth[depths[q]]+=1
    success_vertices=sorted({s['q'] for s in successful})
    for q in success_vertices:by_depth[depths[q]]+=1
    failed={q for q in rows if q not in success_vertices}
    chosen=None
    for q in sorted(failed):
        s=next(x for x in tested[q] if x['tau']==1)
        for r in sorted(s['children']):
            if r%4==3 and r in failed:
                child=next(x for x in tested[r] if x['tau']==1)
                # The child has a single prime modulus, so no CRT-component
                # mismatch or residual tau^2 is responsible for its failure.
                assert child['c']==r and not any(child['hits'].values())
                chosen=dict(q=q,r=r,parent_canonical=s,child_canonical=child,
                            parent_all_sources=tested[q],child_all_sources=tested[r],
                            common_divisor=gcd(s['x'],child['x']))
                break
        if chosen:break
    summary=dict(p=p,total_sources=sum(map(len,rows.values())),total_vertices=len(rows),
                 successful_sources=len(successful),kinds=dict(kinds),
                 successful_vertices=success_vertices,all_failed_vertices=len(failed),
                 success_vertices_by_depth=dict(sorted(by_depth.items())),
                 successful_sources_by_depth=dict(sorted(source_depth.items())),
                 canonical_success_sources=sum(s['tau']==1 for s in successful),
                 noncanonical_success_sources=[(s['q'],s['tau'],s['c']) for s in successful if s['tau']!=1])
    print(json.dumps(dict(summary=summary,successful_sources=successful,
                          all_sources=tested,local_failure_edge=chosen),indent=2))


if __name__=='__main__':main()
