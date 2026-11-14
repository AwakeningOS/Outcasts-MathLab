"""Response to posts117/118. Fixed p1548961, no prime-range scan.
Replay all admissible root11 sources to check the corrected count.
At child73 audit every admissible odd tau (73 sources), preserving the
full modulus219*tau^2. Distinguish target support mod73, mod219 and full.
This is a fixed-input obstruction-transfer test, not universal existence.
"""
import hashlib,itertools,json,math,time
from fractions import Fraction
from pathlib import Path
r=Path(__file__).resolve().parent;start=time.perf_counter();p=1548961
def factor(n):
 out=[];d=2
 while d*d<=n:
  e=0
  while n%d==0:n//=d;e+=1
  if e:out.append((d,e))
  d=3 if d==2 else d+2
 if n>1:out.append((n,1))
 return out
def sqdivs(f):
 out=[1]
 for g,e in f:out=[d*g**j for d in out for j in range(2*e+1)]
 return sorted(out)
def src(q,t):
 A=q*(1 if q%4==3 else 3);c=A*t*t;x=(p+c)//4
 assert c<3*p and (p+c)%4==0 and math.gcd(x,c)==1
 f=factor(x);ds=sqdivs(f)
 I=[d for d in ds if (d+p*x)%c==0];II=[d for d in ds if (d+x)%c==0]
 return dict(q=q,tau=t,c=c,x=x,factors=f,divisors=ds,hitsI=I,hitsII=II)
def sources(q):
 A=q*(1 if q%4==3 else 3);t=1;out=[]
 while A*t*t<3*p:out.append(src(q,t));t+=2
 assert A*(t-2)**2<3*p<=A*t*t
 return out
roots=sources(11);children=sources(73)
assert len(roots)==325 and roots[-1]['tau']==649
assert len(children)==73 and children[-1]['tau']==145
root_success=[s for s in roots if s['hitsI'] or s['hitsII']]
assert [(s['tau'],bool(s['hitsI']),bool(s['hitsII'])) for s in root_success]==[(1,True,True),(7,True,False)]
child_rows=[]
for s in children:
 ds=s['divisors'];x=s['x'];t=s['tau']
 mod73=[d for d in ds if (d+x)%73==0]
 mod219=[d for d in ds if (d+x)%219==0]
 assert x%219==children[0]['x']%219
 assert math.gcd(x,children[0]['x'])==math.gcd(children[0]['x'],(t*t-1)//4)
 row=dict(s,mod73_hits=mod73,mod73_hit_parities_mod3=sorted({d%3 for d in mod73}),
          mod219_hits=mod219,mod219_carries=[(d+x)//219 for d in mod219],
          gcd_with_tau1=math.gcd(x,children[0]['x']))
 child_rows.append(row)
root_certificates=[]
for s in root_success:
 for kind in ('II','I'):
  if not s['hits'+kind]:continue
  d=s['hits'+kind][0];x=s['x'];c=s['c']
  R=p*d if kind=='II' else d
  S=(p*x)**2//R
  assert R*S==(p*x)**2 and (R+p*x)%c==0 and (S+p*x)%c==0
  y=(R+p*x)//c;z=(S+p*x)//c
  assert Fraction(4,p)==Fraction(1,x)+Fraction(1,y)+Fraction(1,z)
  root_certificates.append(dict(tau=s['tau'],kind=kind,d=d,denominators=[x,y,z]))
def first(predicate):return next((s for s in child_rows if predicate(s)),None)
selected=dict(first_mod73=first(lambda s:s['mod73_hits']),
 first_baseII=first(lambda s:s['mod219_hits']),
 first_baseII_but_fullII_failure=first(lambda s:s['mod219_hits'] and not s['hitsII']),
 first_baseII_but_both_full_failure=first(lambda s:s['mod219_hits'] and not(s['hitsI'] or s['hitsII'])),
 first_full_success=first(lambda s:s['hitsI'] or s['hitsII']))
for s in {v['tau']:v for v in selected.values() if v}.values():
 x=s['x'];direct=[]
 for d in range(1,x+1):
  if x*x%d==0:
   direct.append(d)
   if d!=x:direct.append(x*x//d)
 assert sorted(direct)==s['divisors']
res=dict(p=p,root_sources=len(roots),root_max_tau=649,root_failed_both=323,
 root_total_divisors=sum(len(s['divisors']) for s in roots),root_success=root_success,
 root_certificates=root_certificates,child_sources=len(children),child_max_tau=145,
 child_success_taus=[s['tau'] for s in children if s['hitsI'] or s['hitsII']],
 child_fullI_taus=[s['tau'] for s in children if s['hitsI']],
 child_fullII_taus=[s['tau'] for s in children if s['hitsII']],
 child_baseII_taus=[s['tau'] for s in child_rows if s['mod219_hits']],selected=selected,
 roots=roots,children=child_rows,independent_selected_divisor_enumeration=True,
 seconds=time.perf_counter()-start,CPU_host='mini',CPU_processes=1,
 peer_code_executed=False,Lean_executed=False,new_prime_range_scan=False,global_proof=False,
 code_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
(r/'tau-fiber-results-20261105.json').write_text(json.dumps(res,indent=2)+'\n')
print(json.dumps({k:v for k,v in res.items() if k not in('roots','children')},indent=2))
