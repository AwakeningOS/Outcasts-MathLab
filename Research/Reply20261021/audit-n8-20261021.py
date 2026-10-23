"""Post-result audit. No participant code imported; no new cohort scan."""
import csv, gzip, hashlib, itertools, json, math, time
from collections import Counter
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parent
SRC = ROOT / 'source'
START = time.monotonic()
P = 100687129
B = 27
CLASSES = {1,121,169,289,361,529}
BOX = {(a,u) for a in range(1,B+1) for u in range(1,B+1) if a*u<=B and math.gcd(a,u)==1}
EK = {k for k in range(1,127) if 60%k==0 or 126%k==0}
EP = {(a,k//a) for k in EK for a in range(1,k+1) if k%a==0 and math.gcd(a,k//a)==1}
PAIRS = BOX | EP
assert (len(BOX),len(EP),len(PAIRS),len(BOX&EP)) == (75,81,111,45)

def sha(path):
    with path.open('rb') as fp:
        return hashlib.file_digest(fp,'sha256').hexdigest()

manifest = []
for line in (SRC/'SHA256SUMS').read_text().splitlines():
    expected,name = line.split()
    assert '/' not in name and name in {p.name for p in SRC.iterdir()}
    actual = sha(SRC/name)
    assert actual==expected,(name,actual,expected)
    manifest.append({'file':name,'sha256':actual})
assert len(manifest)==9
reported = json.loads((SRC/'n8_results.json').read_text())
with gzip.open(SRC/'n8_primes.jsonl.gz','rt') as fp:
    summaries = [json.loads(s) for s in fp]
primes = [s['p'] for s in summaries]
assert primes==sorted(set(primes)) and len(primes)==33663
assert all(10**8<p<120000000 and p%840 in CLASSES and (p-1).bit_length()==B for p in primes)
prime_sha = hashlib.sha256(''.join(f'{p}\n' for p in primes).encode()).hexdigest()
assert prime_sha==reported['G0']['prime_list_sha256']=='e2cf39689d2a6d1b05b19b42b551533995060e16509769235ae8f94bc0440c21'
by_p = {s['p']:s for s in summaries}
counts = Counter()
pair_counts = Counter()
target_rows = []
seen_primes=[]
with gzip.open(SRC/'n8_rows.csv.gz','rt',newline='') as fp:
    reader = csv.DictReader(fp)
    for p, it in itertools.groupby(reader,lambda r:int(r['p'])):
        seen_primes.append(p)
        rows = list(it)
        assert len(rows)==111 and {(int(r['a']),int(r['u'])) for r in rows}==PAIRS,p
        wbox=elog=eall=0
        cold=ccomb=F(0)
        for r in rows:
            a,u,w = int(r['a']),int(r['u']),int(r['W'])
            inb,ine = (a,u) in BOX,(a,u) in EP
            assert int(r['in_budget'])==inb and int(r['inE'])==ine
            counts['rows']+=1
            if ine:eall+=w
            if not inb:
                counts['extra_E_rows']+=1
                continue
            counts['box_rows']+=1
            wbox+=w
            if ine:elog+=w
            old,comb = F(r['c_old']),F(r['c_comb'])
            assert 0<=old<=comb<=w and math.ceil(comb)<=w
            cold+=old;ccomb+=comb
            if ine:
                assert F(r['eta'])==0 and old==w
            if int(r['L'])==8:
                mag=F(r['c_mag']);assert 0<=mag<=w and comb==max(old,mag)
                counts['l8_rows']+=1
                if w==0:counts['l8_W0']+=1
                if old==0:counts['l8_old0']+=1
                if w>0 and old==0:counts['l8_old0_Wpos']+=1
                if old>0:counts['l8_oldpos']+=1
                if old==0 and mag>0:
                    counts['l8_rescued']+=1;pair_counts[(a,u)]+=1
            else:assert comb==old
        s=by_p[p]
        assert (wbox,elog,eall,cold,ccomb)==(s['W_B'],s['E_log'],s['E_all'],F(s['Cert_old']),F(s['Cert_comb'])),p
        counts['box_old0']+=(cold==0)
        counts['box_rescued']+=(cold==0<ccomb)
        counts['box_comb_miss']+=(ccomb==0<wbox)
        if p==P:target_rows=rows
        assert time.monotonic()-START<300
assert seen_primes==primes
assert dict(counts)=={'rows':3736593,'box_rows':2524725,'l8_rows':201978,'l8_old0':188012,'l8_W0':157345,'extra_E_rows':1211868,'box_old0':0,'box_rescued':0,'box_comb_miss':0,'l8_old0_Wpos':30667,'l8_oldpos':13966,'l8_rescued':2335},dict(counts)
mins={key:min(s[key] for s in summaries) for key in ('W_B','E_log','E_all')}
assert mins=={'W_B':6,'E_log':2,'E_all':3}
assert all(s['W_B']>0 and s['E_log']>0 and s['E_all']>0 for s in summaries)
assert pair_counts==Counter({(1,8):525,(8,1):777,(8,3):335,(3,8):318,(1,24):145,(24,1):235})

def factor(n):
    fs=[];q=2
    while q*q<=n:
        e=0
        while n%q==0:n//=q;e+=1
        if e:fs.append((q,e))
        q=3 if q==2 else q+2
    if n>1:fs.append((n,1))
    return fs

def factor_divisors(fs):
    ds=[1]
    for q,e in fs:ds=[d*q**j for d in ds for j in range(e+1)]
    return sorted(ds)

def trial_divisors(n):
    ds=[]
    for d in range(1,math.isqrt(n)+1):
        if n%d==0:
            ds.append(d)
            if d*d!=n:ds.append(n//d)
    return sorted(ds)

def subgroup(gens,m):
    h={1};queue=[1]
    for x in queue:
        for g in gens:
            v=x*g%m
            if v not in h:h.add(v);queue.append(v)
    return h

assert factor(P)==[(P,1)]
n2=next(n for n in range(2,P) if pow(n,(P-1)//2,P)==P-1)
assert n2==17
outrows=[]
classifications=Counter()
for r in target_rows:
    a,u=int(r['a']),int(r['u']);N=a*P+u;m=4*a*u
    fs=factor(N);ds=factor_divisors(fs);independent=trial_divisors(N)
    assert ds==independent and math.prod(q**e for q,e in fs)==N
    hits=[s for s in ds if s%m==m-1]
    assert len(hits)==int(r['W']),(a,u,hits,r['W'])
    item={'a':a,'u':u,'N':N,'m':m,'factors':fs,'W':len(hits),'witnesses':hits,'in_budget':(a,u) in BOX,'in_E':(a,u) in EP}
    sols=[]
    for s in hits:
        alpha=(s+1)//m;v=N//s
        assert s+1==m*alpha and a*P==4*a*alpha*u*v-u-v
        x,y,z=alpha*u*v,a*alpha*u*P,a*alpha*v*P
        assert 4*x*y*z==P*(x*y+x*z+y*z)
        sols.append({'s':s,'alpha':alpha,'v':v,'x':x,'y':y,'z':z})
    item['solutions']=sols
    if (a,u) in BOX:
        units={d for d in range(1,m) if math.gcd(d,m)==1}
        squares={d*d%m for d in units}
        w2=sum(d%m in {(-h)%m for h in squares} for d in ds if math.gcd(d,m)==1)
        k=subgroup([q%m for q,e in fs if math.gcd(q,m)==1],m)
        cls='success' if hits else ('quadratic' if w2==0 else ('group' if m-1 not in k else 'exponent'))
        item.update(W_G2=w2,G2size=len(squares),m1K=m-1 in k,classification=cls)
        assert w2==int(r['W_G2']) and len(squares)==int(r['G2size']) and (m-1 in k)==bool(int(r['m1K']))
        classifications[cls]+=1
    outrows.append(item)
    assert time.monotonic()-START<300
v={'p':P,'B':B,'prime_trial_verified':True,'least_nonresidue':n2,'candidate_rows':len(outrows),'all_divisors_two_independent_paths_match':True,'W_B':sum(r['W'] for r in outrows if r['in_budget']),'E_log':sum(r['W'] for r in outrows if r['in_budget'] and r['in_E']),'E_all':sum(r['W'] for r in outrows if r['in_E']),'budget_classifications':dict(classifications),'positive_rows':[r for r in outrows if r['W']]}
assert (v['W_B'],v['E_log'],v['E_all'])==(6,2,3)
assert classifications==Counter(success=6,quadratic=60,group=1,exponent=8)
res={'source_pin':'3d17d5e83cd68b9bea71371155a56d6097644a9b','manifest':manifest,'all_manifest_matches':True,'uploaded_prime_records':len(primes),'uploaded_prime_list_sha256':prime_sha,'existing_data_consistency_counts':dict(counts),'existing_data_minima':mins,'existing_data_rescues_by_pair':{f'{a},{u}':c for (a,u),c in pair_counts.items()},'independent_single_prime':v,'limits':'All-cohort consistency is NOT arithmetic replay. All 111 actual-divisor rows independently replayed only at P. No character/certificate recomputation, Lean, global proof or new cohort scan. Post-result fixed-input audit.','seconds':time.monotonic()-START}
(ROOT/'n8-audit-results-20261021.json').write_text(json.dumps(res,ensure_ascii=False,indent=2)+'\n')
(ROOT/'n8-minimum-111-rows-20261021.json').write_text(json.dumps(outrows,ensure_ascii=False,indent=2)+'\n')
print(json.dumps(res,ensure_ascii=False,indent=2))
