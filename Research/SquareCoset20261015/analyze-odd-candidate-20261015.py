import json
from pathlib import Path

run=Path('/mnt/hdd1t/outcasts-reply-20261015-ACqg3d')
rows=json.loads((run/'square-coset-rows.json').read_text())
data=[]
for p in sorted({r['p'] for r in rows}):
    good=[r for r in rows if r['p']==p and len(r['square_subgroup'])%2 and r['W']>0]
    best=min(good,key=lambda r:(r['a']*r['u'],r['a'],r['u'])) if good else None
    data.append({'p':p,'passes':bool(good),'successful_odd_H_pairs':len(good),'minimum_odd_H_cost_in_box':None if best is None else best['a']*best['u'],'example_pair':None if best is None else [best['a'],best['u']]})
result={'candidate':'Hoddlog: every residual target prime p has coprime positive a,u with au<=ceil(log2 p), odd |G^2|, and an actual target divisor','role':'Strengthening of Hlog motivated after the same610 discovery rows, not new priority or a proven theorem','timing':'Posthoc discovery-set check, not preregistered or held-out evidence','inputs':data,'all10_discovery_inputs_pass':all(r['passes'] for r in data),'universal_status':'Refuted on the discovery set at5843041' if not all(r['passes'] for r in data) else 'Unproved','no_new_primes_or_rows':True,'not_an_assumption_for_current_lemmas':True}
(run/'odd-candidate-discovery-check.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
