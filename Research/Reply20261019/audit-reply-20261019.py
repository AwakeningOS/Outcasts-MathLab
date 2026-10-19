import hashlib, json, math, time, urllib.request
from pathlib import Path
ROOT=Path(__file__).resolve().parent
start=time.monotonic()
def fac(n):
    f=[]; r=2
    while r*r<=n:
        e=0
        while n%r==0:n//=r;e+=1
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
def inspect(p,q,t):
    c=(1 if q%4==3 else 3)*q*t*t; x=(p+c)//4
    assert 4*x==p+c and c<3*p and math.gcd(p*x,c)==1
    f=fac(x); ds=divs(f); ds2=divs([(r,2*e) for r,e in f])
    A={d%c for d in ds if leg(d,p)==1}; B={d%c for d in ds if leg(d,p)==-1}
    assert A.isdisjoint(B) and len(A)==len(B)
    assert B=={x*pow(a,-1,c)%c for a in A}
    delta={a*pow(b,-1,c)%c for a in A for b in A}
    prod={a*b%c for a in A for b in A}
    I=any((d+p*x)%c==0 for d in ds2); II=any((d+x)%c==0 for d in ds2)
    assert I==((-p)%c in delta); assert II==((-x)%c in prod)
    nr=[(r,e) for r,e in f if leg(r,p)==-1]
    for r,e in nr:
        Ar={d%c for d in ds if x//d%r==0 and leg(d,p)==1}
        assert {r*a%c for a in Ar}<=B
        if not II: assert (-r)%c not in {a*pow(b,-1,c)%c for a in A for b in Ar}
    omega=sum(e for r,e in nr)
    if omega==1:
        r=nr[0][0]; m=x//r
        assert A=={d%c for d in divs(fac(m))}
        assert B=={r*a%c for a in A}
        assert II==((-r)%c in delta)
    return dict(p=p,q=q,t=t,c=c,x=x,factors=f,A=sorted(A),delta=sorted(delta),I=I,II=II,omega=omega,nr=nr)

PS=[2521,66529,345601,670849,1740481,3678481,5843041,8615161,18490201,38296729,53722321,84525841]
rows=[]
for p in PS:
    for q in range(11,400):
        if fac(q)!=[(q,1)] or leg(q,p)!=-1:continue
        for t in range(1,16,2):
            if time.monotonic()-start>60:raise TimeoutError('60sec; not exhausted')
            if (1 if q%4==3 else 3)*q*t*t>=3*p:continue
            rows.append(inspect(p,q,t))
assert len(rows)==3391
cycle=[11,211,683,89,17,643,113]
cycle_rows=[]
for i,q in enumerate(cycle):
    row=inspect(2521,q,1); r=cycle[(i+1)%len(cycle)]
    assert row['nr']==[(r,1)] and not row['I'] and not row['II']
    m=row['x']//r; cp=(1 if r%4==3 else 3)*r; xp=(2521+cp)//4
    assert xp%r!=0
    g=math.gcd(row['x'],xp)
    assert m%g==0 and all(leg(s,2521)==1 for s,e in fac(g))
    assert 4*xp==r*(4*m+(1 if r%4==3 else 3))-row['c']
    row.update(next_q=r,cofactor=m,target_II=(-r)%row['c'],target_I=(-2521)%row['c'],next_x=xp,common_gcd=g)
    cycle_rows.append(row)

# The CRT claim is *only* about frozen observed sets, not actual selectors for other p.
L=math.lcm(*(r['c'] for r in cycle_rows))
assert all((-2521)%r['c'] not in r['delta'] for r in cycle_rows)
result={'cohort_size':len(rows),'Omega1':sum(r['omega']==1 for r in rows),'Omega3':sum(r['omega']==3 for r in rows),'positive_set_reductions_agree':True,'new_full_group_table_recomputed':False,'cycle':cycle_rows,'frozen_CRT_contains':2521%L,'CRT_modulus':L,'paper_claim':'frozen failure sets retain the observed failing p by construction','seconds_math':time.monotonic()-start,'Lean_executed':False}
(ROOT/'reply-audit-results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))

# Exact published-byte check. The manifest is not interpreted as shell input.
pin='2eb1317c8404a5418be49b2fc6a2621e4852a91f'
base=f'https://raw.githubusercontent.com/AwakeningOS/Outcasts-MathLab/{pin}/Research/L8Magnitude20261017/'
def get(name):
    assert '/' not in name and name not in {'.','..'}
    with urllib.request.urlopen(base+name,timeout=30) as r:return r.read()
manifest=get('SHA256SUMS').decode(); checked=[]; lines=[]
for line in manifest.splitlines():
    expected,name=line.split(); data=get(name); actual=hashlib.sha256(data).hexdigest()
    crlf=hashlib.sha256(data.replace(b'\r\n',b'\n').replace(b'\n',b'\r\n')).hexdigest()
    checked.append(dict(file=name,expected=expected,actual=actual,exact_match=expected==actual,CRLF_match=expected==crlf,bytes=len(data)))
    lines.append(f'{actual}  {name}')
    if expected!=actual:assert name=='l8-development-results.csv' and expected==crlf
assert len(checked)==15
(ROOT/'SHA256SUMS.corrected').write_text('\n'.join(lines)+'\n')
(ROOT/'manifest-audit.json').write_text(json.dumps({'pinned_commit':pin,'files':checked},indent=2)+'\n')
print(json.dumps({'manifest_files':len(checked),'exact_matches':sum(r['exact_match'] for r in checked),'mismatches':[r for r in checked if not r['exact_match']]}))
