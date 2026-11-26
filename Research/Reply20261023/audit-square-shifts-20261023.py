"""Audit Outcasts #87 on the fixed p=2521, q=11 root and q=29 child.

Contract: no prime-range scan. Enumerate the 13 allowed odd root parameters;
retain every prime exponent and every actual divisor. Test Type I by Delta(A)
and Type II by A*A, cross-checking both against all d|x^2. Separate obstructions
visible modulo 11, modulo tau^2, and only in the full modulus 11*tau^2.
Do not infer joint realizability from marginal membership or coprimality.
"""
import itertools,json,math,time
from pathlib import Path

def factor(n):
    out={};q=2
    while q*q<=n:
        while n%q==0:out[q]=out.get(q,0)+1;n//=q
        q=3 if q==2 else q+2
    if n>1:out[n]=out.get(n,0)+1
    return out

def divs(f):
    out=[1]
    for q,e in f.items():out=[d*q**j for d in out for j in range(e+1)]
    return sorted(out)

def chi(n,p):
    k=pow(n%p,(p-1)//2,p)
    assert k in (0,1,p-1)
    return -1 if k==p-1 else k

def valuation(n,r):
    assert n!=0
    n=abs(n);e=0
    while n%r==0:e+=1;n//=r
    return e

def row(p,q,tau):
    sigma=1 if q%4==3 else 3; base=sigma*q;c=base*tau*tau
    assert c<3*p and (p+c)%4==0
    x=(p+c)//4;f=factor(x);D=divs(f)
    assert math.gcd(c,x)==1 and chi(x,p)==-1
    positive=[d for d in D if chi(d,p)==1]
    omega=sum(e for r,e in f.items() if chi(r,p)==-1)
    actual=divs({r:2*e for r,e in f.items()})
    branches={}
    for branch,target in [('I',-p),('II',-x)]:
        vals={}; pairs={}
        for mod in [base,tau*tau,c]:
            candidates=[(a,b,(a*pow(b,-1,mod) if branch=='I' else a*b)%mod)
                        for a,b in itertools.product(positive,repeat=2)]
            vals[mod]=sorted({v for a,b,v in candidates})
            pairs[mod]=[[a,b] for a,b,v in candidates if v==target%mod]
        # All actual square divisors give a separate arithmetic cross-check.
        direct=[d for d in actual if (d+(p*x if branch=='I' else x))%c==0]
        assert bool(direct)==bool(pairs[c])
        base_ok=bool(pairs[base]);square_ok=bool(pairs[tau*tau]);full_ok=bool(pairs[c])
        if full_ok:kind='success'
        elif not base_ok:kind='base obstruction'
        elif not square_ok:kind='square-parameter obstruction'
        else:kind='joint/full-modulus obstruction'
        branches[branch]=dict(target=target%c,base_target=target%base,square_target=target%(tau*tau),
            base_pass=base_ok,square_pass=square_ok,full_pass=full_ok,classification=kind,
            base_pairs=pairs[base],square_pairs=pairs[tau*tau],full_pairs=pairs[c],
            residue_sets={str(k):v for k,v in vals.items()},actual_divisor_hits=direct)
    return dict(p=p,q=q,tau=tau,base=base,c=c,x=x,factors=f,omega_minus=omega,
                positive_divisors=positive,gcd_base_square=math.gcd(base,tau*tau),branches=branches)

def main():
    started=time.monotonic();p=2521
    assert factor(p)=={p:1}
    rows=[row(p,11,t) for t in range(1,math.isqrt((3*p-1)//11)+1,2)]
    assert len(rows)==13 and all(not b['full_pass'] for r in rows for b in r['branches'].values())
    # Source and target powers are independently inspected, not assumed.
    transitions=[]
    for first,second in itertools.permutations(rows,2):
        delta=(second['tau']**2-first['tau']**2)//4
        assert second['x']-first['x']==11*delta
        for prime,e in first['factors'].items():
            R=prime**e;lhs=delta%R==0
            mod=R if prime!=2 else 2*R
            roots=(second['tau']-first['tau'])%mod==0 or (second['tau']+first['tau'])%mod==0
            assert lhs==roots and lhs==(second['x']%R==0)
            transitions.append(dict(tau1=first['tau'],tau2=second['tau'],prime=prime,e=e,preserved=lhs))
    child=row(p,29,1)
    assert child['x']==652 and child['branches']['I']['full_pass']
    d=child['branches']['I']['actual_divisor_hits'][0];x=child['x'];c=child['c']
    y=(d+p*x)//c;z=(p*p*(x*x//d)+p*x)//c
    assert 4*x*y*z==p*(x*y+x*z+y*z)
    summary=[dict(tau=r['tau'],x=r['x'],factors=r['factors'],omega_minus=r['omega_minus'],
        I=r['branches']['I']['classification'],II=r['branches']['II']['classification'],
        gcd=r['gcd_base_square']) for r in rows]
    # Added after the first fixed-input audit: test the exact valuation issue
    # raised by its mismatch with the proposed 2*3^k +/- 1 construction.
    freeze_rows=[]
    for tau in [5,7,17,19,25]:
        rr=next(r for r in rows if r['tau']==tau)
        delta=(tau*tau-1)//4
        e_delta=valuation(delta,3);e_new=valuation(rr['x'],3)
        if e_delta>1:assert e_new==1
        freeze_rows.append(dict(tau=tau,x=rr['x'],delta=delta,v3_delta=e_delta,v3_x=e_new))
    lift_rows=[]
    for k in range(1,6):
        mod=3**k
        roots=[t for t in range(mod) if (11*t*t+p)%mod==0]
        in_range=[r['tau'] for r in rows if r['x']%mod==0]
        lift_rows.append(dict(k=k,modulus=mod,roots=roots,allowed_odd_parameters=in_range))
    rr=rows[-1];c=rr['c'];positive=rr['positive_divisors']
    deltas={mod:sorted({a*pow(b,-1,mod)%mod for a,b in itertools.product(positive,repeat=2)}) for mod in [11,625,c]}
    assert (-p)%11 in deltas[11] and (-29)%11 in deltas[11]
    assert (-p)%625 not in deltas[625] and (-29)%625 not in deltas[625]
    result=dict(scope='one fixed root, 13 sources, one known child; not universal existence',
        root_rows=rows,summary=summary,power_preservation_tests=len(transitions),
        tested_prime_power_transition_equivalence=True,child=child,child_solution=dict(d=d,x=x,y=y,z=z),
        valuation_freeze_examples=freeze_rows,three_power_lifts=lift_rows,
        tau25_delta_sets=deltas,tau25_targets_mod625=dict(I=(-p)%625,II=(-29)%625),
        noncoprime_projection_counterexample=dict(values=[1,122],moduli=[11,121],full_modulus=1331),
        seconds=time.monotonic()-started)
    assert 122%11==1 and 122%121==1 and 122%1331!=1
    Path('square-shift-results.json').write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
    print(json.dumps({'summary':summary,'power_preservation_tests':len(transitions),'valuation_freeze_examples':freeze_rows,'three_power_lifts':lift_rows,'tau25_delta_sets':deltas,'tau25_targets_mod625':result['tau25_targets_mod625'],'child_solution':result['child_solution'],'seconds':result['seconds']},ensure_ascii=False))

if __name__=='__main__':main()
