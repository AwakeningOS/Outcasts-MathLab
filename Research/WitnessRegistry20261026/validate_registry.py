"""Exact finite validation of the proposal seed; Python standard library only.

No network access, third-party code, Lean execution, or prime-range search.
Unknown predicates/checkers and unsupported minimality claims fail closed.
"""
import argparse,copy,json,math,re,time
from functools import lru_cache
from fractions import Fraction
from pathlib import Path

def need(ok,msg):
    if not ok:raise ValueError(msg)
def integer(s):
    need(isinstance(s,str) and re.fullmatch('[1-9][0-9]*',s),'expected positive decimal string')
    return int(s)
def factors(n):
    result={};q=2
    while q*q<=n:
        while n%q==0:result[q]=result.get(q,0)+1;n//=q
        q=3 if q==2 else q+2
    if n>1:result[n]=1
    return result
def divisors(f):
    out=[1]
    for q,e in f.items():out=[d*q**j for d in out for j in range(e+1)]
    return out
def prime(n):return n>1 and factors(n)=={n:1}
def chi(n,p):return -1 if pow(n%p,(p-1)//2,p)==p-1 else pow(n%p,(p-1)//2,p)
def group(gens,m):
    seen={1};todo=[1]
    while todo:
        a=todo.pop()
        for b in gens:
            c=a*b%m
            if c not in seen:seen.add(c);todo.append(c)
    return seen
@lru_cache(None)
def cost_group(p,limit):
    C=G=None;first=None;checked=0
    for cost in range(1,limit+1):
        for a in range(1,cost+1):
            if cost%a:continue
            u=cost//a
            if math.gcd(a,u)!=1:continue
            checked+=1;n=a*p+u;m=4*cost;fac=factors(n)
            ds=divisors(fac)
            by_scan={v for k in range(1,math.isqrt(n)+1) if n%k==0 for v in (k,n//k)}
            need(set(ds)==by_scan,'factor-generated divisors differ from integer scan')
            hits=[s for s in ds if (s+1)%m==0]
            reachable=m-1 in group([q%m for q in fac if math.gcd(q,m)==1],m)
            if G is None and reachable:G=cost
            if C is None and hits:C=cost;first=dict(a=a,u=u,s=min(hits))
    return dict(C=C,G=G,first_witness=first,checked_coprime_pairs=checked,budget=limit)
def sigma(q):return 1 if q%4==3 else 3
def rows(p,q):
    A=sigma(q)*q;out=[]
    for t in range(1,math.isqrt((3*p-1)//A)+1,2):
        c=A*t*t;need((p+c)%4==0,'source not integral');x=(p+c)//4;fac=factors(x)
        ds=divisors({r:2*e for r,e in fac.items()})
        hit=any((d+x)%c==0 or (d+p*x)%c==0 for d in ds)
        out.append(dict(tau=t,x=x,success=hit,children=[r for r in fac if chi(r,p)==-1]))
    return out
@lru_cache(None)
def short_root(p):
    q=next(q for q in range(2,p) if prime(q) and chi(q,p)==-1)
    root=rows(p,q);need(root and not any(z['success'] for z in root),'root does not fully fail')
    children=sorted({r for z in root for r in z['children']})
    childrows={r:rows(p,r) for r in children}
    good=[r for r in children if any(z['success'] for z in childrows[r])]
    forced=[r for r in children if sigma(q)*q*(r-2)**2<3*p]
    need(good and not set(good)&set(forced),'restricted escape not refuted')
    return dict(q=str(q),root_sources=len(root),children=list(map(str,children)),all_child_sources=sum(map(len,childrows.values())),bound_children=list(map(str,forced)),good_children=list(map(str,good)))

PREDICATES={
    'product-cost-at-most-18-v1':{'op':'C_le_constant','constant':'18'},
    'product-cost-at-most-twice-group-v1':{'op':'C_le_multiple_G','multiple':'2'},
    'uniform-short-root-one-edge-v1':{'op':'successful_child_under_uniform_root_bound','root':'least_nonresidue_prime','bound':'A*(r-2)^2<3*p','success':'some_allowed_odd_tau_TypeI_or_TypeII'},
}
def validate(data):
    need(data['schema_version']==1,'unknown schema')
    need(data['thread_id']=='80c02e64-db15-446c-b2b4-b973abeb5c0c','wrong thread')
    need(data['target_domain']=={'prime':True,'min_exclusive':'7','modulus':'840','residues':['1','121','169','289','361','529']},'unknown target domain')
    ids=[r['id'] for section in ('witnesses','candidates','counterexamples') for r in data[section]]
    need(len(ids)==len(set(ids)),'duplicate identifier')
    candidates={x['id']:x for x in data['candidates']}
    for key,c in candidates.items():
        need(key in PREDICATES and c['predicate']==PREDICATES[key],'unknown or altered predicate')
        need(c['kind']=='universal_auxiliary_claim','candidate must be an auxiliary claim')
    for w in data['witnesses']:
        need(w['kind']=='positive_integer_solution','wrong witness kind')
        p=integer(w['p']);need(p>=2 and len(w['denominators'])==3,'bad witness input')
        x,y,z=map(integer,w['denominators'])
        need(4*x*y*z==p*(x*y+x*z+y*z),w['id']+' integer equality failed')
        need(sum((Fraction(1,d) for d in (x,y,z)),Fraction())==Fraction(4,p),'fraction mismatch')
        need(w['source_post_numbers'],'missing witness provenance')
    checks=[];covered=set()
    for e in data['counterexamples']:
        need(e['kind']=='auxiliary_claim_counterexample','cannot relabel as ESC counterexample')
        need(e['candidate_id'] in candidates,'missing candidate reference');covered.add(e['candidate_id'])
        need(e['minimality']=={'status':'not_claimed','order':None,'checked_lower_domain':None},'minimality needs a separate certificate; unsupported here')
        p=integer(e['p']);need(p>7 and prime(p) and p%840 in {1,121,169,289,361,529},'counterexample outside target domain')
        need(e['source_post_numbers'] and e['evidence'],'missing counterexample provenance')
        op=candidates[e['candidate_id']]['predicate']['op']
        if e['checker']=='cost_group_v1':
            need(op in ('C_le_constant','C_le_multiple_G'),'checker/predicate mismatch')
            C=integer(e['expected']['C']);G=integer(e['expected']['G']);need(C<=100,'seed checker budget cap')
            result=cost_group(p,C);need(result['C']==C and result['G']==G,'C/G mismatch')
            need(C>18 if op=='C_le_constant' else C>2*G,'candidate not refuted')
        elif e['checker']=='short_root_v1':
            need(op=='successful_child_under_uniform_root_bound','checker/predicate mismatch')
            need(p<=100000,'seed checker size cap')
            result=short_root(p);need(result==e['expected'],'short-root certificate mismatch')
        else:raise ValueError('unknown checker: '+e['checker'])
        checks.append(dict(id=e['id'],candidate_id=e['candidate_id'],finite_check='pass',counterexample_p_minimality_checked=False,details=result))
    need(covered==set(candidates),'candidate lacks a checked counterexample')
    return dict(witnesses_checked=len(data['witnesses']),candidate_counterexamples_checked=len(checks),checks=checks,Lean_executed=False,new_research_result=False,full_thread_inventory=False,universal_existence_proved=False)

def selftest(data):
    cases=[]
    def test(name,change):
        mutant=copy.deepcopy(data);change(mutant)
        try:validate(mutant)
        except (ValueError,KeyError,TypeError):cases.append(dict(test=name,rejected=True));return
        raise ValueError('mutation unexpectedly passed: '+name)
    test('wrong_denominator',lambda d:d['witnesses'][0]['denominators'].__setitem__(0,'307'))
    test('zero_denominator',lambda d:d['witnesses'][0]['denominators'].__setitem__(0,'0'))
    test('missing_candidate',lambda d:d['candidates'].pop())
    test('false_minimum_C',lambda d:d['counterexamples'][0]['expected'].__setitem__('C','18'))
    test('ESC_relabel',lambda d:d['counterexamples'][0].__setitem__('kind','ESC_counterexample'))
    test('changed_budget',lambda d:d['candidates'][0]['predicate'].__setitem__('constant','20'))
    test('unproved_minimality',lambda d:d['counterexamples'][0]['minimality'].__setitem__('status','proved'))
    test('unknown_checker',lambda d:d['counterexamples'][0].__setitem__('checker','trust_me'))
    return cases

def main():
    parser=argparse.ArgumentParser();parser.add_argument('registry',nargs='?',default=str(Path(__file__).with_name('registry.json')));parser.add_argument('--self-test',action='store_true');args=parser.parse_args()
    start=time.monotonic();data=json.loads(Path(args.registry).read_text());result=validate(data)
    if args.self_test:result['mutation_tests']=selftest(data)
    result['seconds']=time.monotonic()-start
    print(json.dumps(result,indent=2))
if __name__=='__main__':main()
