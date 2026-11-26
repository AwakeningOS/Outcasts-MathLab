"""Audit post120 on existing fixed1548961 data; do not repeat its cohorts.
Check all73 child component counts. Find in the already saved root325 rows
a counterexample to the inference 'no full lift of base hits => residual
component itself empty'. Distinguish shared-prime power omissions from
genuine joint obstructions. No factoring, new source or prime-range scan.
"""
import collections,hashlib,json,math,sys
from pathlib import Path
r=Path(__file__).resolve().parent
path=Path(sys.argv[1]) if len(sys.argv)>1 else r/'tau-fiber-results-20261105.json'
a=json.loads(path.read_text());p=a['p'];counts={};details={}
def classify(s,kind):
 eta=1 if kind=='II' else p
 mods={'3':3,'r':s['q'],'t':s['tau']**2} if s['q']%4==1 else {'r':s['q'],'t':s['tau']**2}
 sets={k:[d for d in s['divisors'] if (d+eta*s['x'])%m==0] for k,m in mods.items()}
 missing=tuple(k for k in mods if not sets[k]);joint=set(s['divisors'])
 for ds in sets.values():joint.intersection_update(ds)
 full=s['hits'+kind]
 return dict(moduli=mods,missing=list(missing),sets=sets,
  component_intersection=sorted(joint),full_hits=full,
  label='+'.join(missing) if missing else ('SUCCESS' if full else 'JOINT'),
  overlap=math.prod(mods.values())!=math.lcm(*mods.values()))
for kind in('II','I'):
 rows=[dict(tau=s['tau'],**classify(s,kind)) for s in a['children']]
 counts[kind]=dict(collections.Counter(z['label'] for z in rows));details[kind]=rows
assert counts['II']=={'JOINT':1,'r+t':36,'3+r+t':32,'r':2,'t':2}
assert counts['I']=={'r+t':35,'3+r+t':29,'r':2,'t':4,'3+t':2,'3+r':1}
root3=next(s for s in a['roots'] if s['tau']==3)
counter=classify(root3,'II')
assert counter['sets']['r'] and counter['sets']['t'] and not counter['component_intersection']
assert 1 in counter['sets']['r'] and 5 in counter['sets']['t']
base=counter['sets']['r'];carries=[(d+root3['x'])//11 for d in base]
assert all(k%9 for k in carries)
overlap=[]
for s in a['roots']+a['children']:
 for kind in('II','I'):
  z=classify(s,kind)
  if z['label']=='JOINT' and z['overlap']:
   def valuation(n,q):
    e=0
    while n%q==0:n//=q;e+=1
    return e
   overlap.append(dict(q=s['q'],tau=s['tau'],x=s['x'],c=s['c'],kind=kind,
    factors=s['factors'],same_divisor_passes_all_listed_components=z['component_intersection'],
    valuation_at_q=[valuation(d+(p if kind=='I' else 1)*s['x'],s['q']) for d in z['component_intersection']],
    full_hits=z['full_hits']))
assert len(overlap)==1
assert overlap[0]['q']==11 and overlap[0]['tau']==11 and overlap[0]['kind']=='I'
assert overlap[0]['same_divisor_passes_all_listed_components']==[129191,6925761]
assert overlap[0]['valuation_at_q']==[2,2]
t31=next(s for s in a['children'] if s['tau']==31)
assert not classify(t31,'II')['sets']['t']
out=dict(p=p,child73_counts=counts,child73_details=details,
 original_cohorts_replayed=False,new_factoring=False,new_prime_range_scan=False,
 counterexample=dict(q=11,tau=3,x=root3['x'],c=99,factors=root3['factors'],
  base11_hits=base,residual9_hits=counter['sets']['t'],base11_carries=carries,
  base11_carry_mod9=[k%9 for k in carries],full_hits=[],divisor5_hits_residual=True),
 overlap_JOINT_examples_in_fixed_saved_data=overlap,
 tau31_residual_component_empty_verified=True,
 source_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
 code_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 Lean_executed=False,global_proof=False)
(r/'component-scope-results-20261106.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='child73_details'},indent=2))
