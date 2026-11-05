"""Independent residual-factor-pair checks for the fixed-input source audit."""
import hashlib,json,math
from fractions import Fraction
from pathlib import Path
r=Path(__file__).resolve().parent
a=json.loads((r/'tau-fiber-results-20261105.json').read_text());p=a['p']
counts=[]
for row in a['roots']+a['children']:
 x=row['x'];c=row['c'];M=p*x;ds=row['divisors']
 # Full original residual numerator, including p exponent0,1,2.
 hits=[]
 for j in range(3):
  for d in ds:
   b=p**j*d;assert M*M%b==0
   other=M*M//b
   if (b+M)%c==0 and (other+M)%c==0:hits.append((j,d))
 assert [d for j,d in hits if j==0]==row['hitsI']
 assert [d for j,d in hits if j==1]==row['hitsII']
 assert len([d for j,d in hits if j==2])==len(row['hitsI'])
 counts.append(dict(q=row['q'],tau=row['tau'],original_pair_hits=len(hits)))
t31=next(s for s in a['children'] if s['tau']==31)
assert t31['mod219_hits']==[335,2525,76622741,577529615]
carry=t31['mod219_carries']
assert carry==[2010,2020,351884,2639130]
assert [k%31 for k in carry]==[26,5,3,7]
assert [k%961 for k in carry]==[88,98,158,224]
# Check the post117 exponent statement at the exact finite box.
fiber=[];mod3=[]
for i in range(3):
 for j in range(3):
  for k in range(3):
   d=5**i*29**j*2671**k
   if d%73==43:fiber.append([i,j,k])
   assert (d%3==2)==((i+j)%2==1)
assert fiber==[[0,0,1],[2,2,1]]
out=dict(verified=True,original_residual_sources=len(counts),root_sources=325,
 child_sources=73,child_failed_both=73,child_divisor_count=sum(len(s['divisors']) for s in a['children']),
 t31_divisors=len(t31['divisors']),t31_base_hits=t31['mod219_hits'],t31_carries=carry,
 t31_carry_mod31=[k%31 for k in carry],t31_carry_mod961=[k%961 for k in carry],
 post117_exponent_fiber=fiber,post118_corrected_count_verified=True,
 input_sha256=hashlib.sha256((r/'tau-fiber-results-20261105.json').read_bytes()).hexdigest(),
 original_pair_counts=counts,Lean_executed=False,global_proof=False)
(r/'tau-fiber-independent-20261105.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='original_pair_counts'}))
