import json, math, time
from pathlib import Path

ROOT=Path(__file__).resolve().parent
def fac(n):
    f=[]; r=2
    while r*r<=n:
        e=0
        while n%r==0: n//=r; e+=1
        if e:f.append((r,e))
        r=3 if r==2 else r+2
    if n>1:f.append((n,1))
    return f
def leg(a,p):
    v=pow(a%p,(p-1)//2,p)
    return -1 if v==p-1 else v
def divs(f):
    ds=[1]
    for r,e in f:ds=[d*r**k for d in ds for k in range(e+1)]
    return ds
def row(p,q=11,t=1):
    assert fac(p)==[(p,1)] and p%840 in (1,121,169,289,361,529)
    assert fac(q)==[(q,1)] and leg(q,p)==-1
    c=(1 if q%4==3 else 3)*q*t*t; x=(p+c)//4
    assert c<3*p and 4*x==p+c and math.gcd(p*x,c)==1
    f=fac(x); ds=divs(f); ds2=divs([(r,2*e) for r,e in f])
    A={d%c for d in ds if leg(d,p)==1}
    B={d%c for d in ds if leg(d,p)==-1}
    delta={a*pow(b,-1,c)%c for a in A for b in A}
    I=[d for d in ds2 if (d+p*x)%c==0]; II=[d for d in ds2 if (d+x)%c==0]
    assert bool(I)==((-p)%c in delta)
    return {'p':p,'q':q,'t':t,'c':c,'x':x,'factors':f,'A':sorted(A),'B':sorted(B),'delta':sorted(delta),'target_I':(-p)%c,'I':I,'II':II}

start=time.monotonic()
# Predeclared targeted test, not a prime-range conjecture search:
# p=2521, p'=2521+840*11*k, k=1..1000; stop at first prime with Type-I hit.
base=row(2521); tested=[]; found=None
for k in range(1,1001):
    if time.monotonic()-start>60:raise TimeoutError('resource limit, not exhausted')
    p=2521+9240*k
    if fac(p)!=[(p,1)]:continue
    r=row(p); tested.append(p)
    if r['I']:found=r;break
out={'base':base,'same_congruence_success':found,'prime_inputs_checked':tested,'search_bound_k':1000,'stopped':'counterexample' if found else 'exhausted','seconds':time.monotonic()-start}
assert not base['I']
if found:
    assert (found['p']-base['p'])%(840*11)==0
    d=found['I'][0]; p=found['p']; x=found['x']; c=found['c']
    y=(d+p*x)//c; z=(p*p*x*x//d+p*x)//c
    assert 4*x*y*z==p*(x*y+x*z+y*z)
    out['solution']=[x,y,z]
(ROOT/'crt-periodicity-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
