import json
import math
import sys
from fractions import Fraction
from pathlib import Path

PRIMES = [2521, 66529, 345601, 670849, 5843041]

def factor(n):
    out=[]
    q=2
    while q*q<=n:
        e=0
        while n%q==0:
            n//=q
            e+=1
        if e:
            out.append((q,e))
        q = 3 if q==2 else q+2
    if n>1:
        out.append((n,1))
    return out

def divisors(fac):
    ds=[1]
    for q,e in fac:
        ds=[d*q**j for d in ds for j in range(e+1)]
    return sorted(ds)

def independent_divisors(n):
    ds=[]
    for d in range(1,math.isqrt(n)+1):
        if n%d==0:
            ds.append(d)
            if d*d!=n:
                ds.append(n//d)
    return sorted(ds)

def cf_candidates(p):
    a,b=4,p
    cf=[]
    while b:
        q,r=divmod(a,b)
        cf.append(q)
        a,b=b,r
    hm2,hm1,km2,km1=0,1,1,0
    principals=[]
    intermediates=[]
    for idx,q in enumerate(cf):
        if idx:
            for t in range(1,q+1):
                h=t*hm1+hm2
                k=t*km1+km2
                f=Fraction(h,k)
                if f.numerator==1 and 0<f<Fraction(4,p):
                    intermediates.append(f.denominator)
        h=q*hm1+hm2
        k=q*km1+km2
        principals.append([h,k])
        hm2,hm1,km2,km1=hm1,h,km1,k
    principal_units=[k for h,k in principals if h==1 and Fraction(h,k)<Fraction(4,p)]
    assert cf==[0,p//4,4]
    assert principal_units==[]
    assert sorted(set(intermediates))==[(p+3)//4]
    return {'canonical_cf':cf,'convergents':principals,'eligible_principal_unit_denominators':principal_units,'eligible_intermediate_unit_denominators':sorted(set(intermediates))}

def solve(p,c):
    x=(p+c)//4
    assert 4*x==p+c and 0<x<p
    assert math.gcd(x,c)==math.gcd(p,c)==1
    fx=factor(x)
    ds=divisors([(q,2*e) for q,e in fx])
    assert ds==independent_divisors(x*x)
    rows={'p':p,'c':c,'x':x,'factor_x':fx,'divisors_x_squared':ds,'TypeI':[],'TypeII':[]}
    for d in ds:
        q=x*x//d
        if (d+p*x)%c==0:
            assert (p*p*q+p*x)%c==0 and d<=p*x
            y=(d+p*x)//c
            z=(p*p*q+p*x)//c
            rows['TypeI'].append({'d':d,'xyz':[x,y,z]})
        if d<=x and (d+x)%c==0:
            assert (q+x)%c==0
            y=p*(d+x)//c
            z=p*(q+x)//c
            rows['TypeII'].append({'d':d,'xyz':[x,y,z]})
    for label,number in [('TypeI',1),('TypeII',2)]:
        for cert in rows[label]:
            x,y,z=cert['xyz']
            assert 0<x<=y<=z and 4*x*y*z==p*(x*y+x*z+y*z)
            assert sum(v%p==0 for v in [x,y,z])==number
    return rows

def main():
    run=Path(sys.argv[1])
    all_rows=[]
    summary=[]
    for p in PRIMES:
        assert factor(p)==[(p,1)] and p%840 in [1,121,169,289,361,529]
        cf=cf_candidates(p)
        rows=[solve(p,c) for c in range(3,128,4)]
        all_rows.extend(rows)
        item={'p':p,'cf':cf,'first_c_I':next((r['c'] for r in rows if r['TypeI']),None),'first_c_II':next((r['c'] for r in rows if r['TypeII']),None),'successful_candidates_I':sum(bool(r['TypeI']) for r in rows),'successful_candidates_II':sum(bool(r['TypeII']) for r in rows),'c3_I_count':len(rows[0]['TypeI']),'c3_II_count':len(rows[0]['TypeII']),'first_witness_I':next((r['TypeI'][0] for r in rows if r['TypeI']),None),'first_witness_II':next((r['TypeII'][0] for r in rows if r['TypeII']),None)}
        summary.append(item)
    (run/'type-branches-all-rows.json').write_text(json.dumps(all_rows,indent=2)+'\n')
    result={'inputs':PRIMES,'c_candidates':[3,127,4],'rows':len(all_rows),'all_divisors_independently_matched':True,'all_reconstructions_checked':True,'summary':summary,'new_global_existence_proof':False}
    (run/'reply-check-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    main()
