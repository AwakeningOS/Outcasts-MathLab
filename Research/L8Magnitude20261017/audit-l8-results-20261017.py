import csv
import importlib.util
import json
import math
import sys
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path

run=Path(__file__).resolve().parent
old=json.loads((run/'l8-norm-results-initial.json').read_text())
now=json.loads((run/'l8-norm-results.json').read_text())
assert all(now[k]==v for k,v in old.items() if k!='seconds')
rows=json.loads((run/'l8-fixed-rows.json').read_text())
examples=list(csv.DictReader((run/'l8-development-results.csv').open()))
gain=next(r for r in examples if Q(r['c_mag'])>0)
ns={'__file__':str(run/'check-l8-norm-20261017.py')}
source=(run/'check-l8-norm-20261017.py').read_text().split('\nassert ch.direct(P)')[0]
exec(compile(source,str(run/'check-l8-norm-20261017.py'),'exec'),ns)
gain_full=ns['row'](int(gain['p']),int(gain['a']),int(gain['u']),True)
assert gain_full['rescues_old_zero']
prior=json.loads(Path('/mnt/hdd1t/outcasts-reply-20261015-ACqg3d/square-coset-rows.json').read_text())
layer_counts=Counter(); excluded=[]
for r in prior:
    k=r['a']*r['u']
    if k in ns['E']:
        layer=ns['lam'](r['m'])//2
        layer_counts[layer,r['kind']]+=1
    elif r['kind']=='remaining_full_group_obstruction':
        excluded.append([r['p'],r['a'],r['u'],k,r['m'],len(r['square_subgroup'])])
assert excluded==[[18490201,1,13,13,52,6]]
expected={1:[90,3,87,0,0],2:[192,13,153,6,20],3:[144,15,99,0,30]}
for layer,v in expected.items():
    kinds=['success','quadratic_obstruction','remaining_full_group_obstruction','finite_exponent_shortage']
    assert [sum(layer_counts[layer,k] for k in kinds)]+[layer_counts[layer,k] for k in kinds]==v
necessity_failure=next((r for r in rows if r['W']==0 and r['nonresidue_multiplicity']>=2 and r['target_in_K']),None)
result={'initial_and_oracle_separated_all_old_result_fields_match':True,'initial_seconds':old['seconds'],
        'final_seconds':now['seconds'],'norm_validation_rows':now['norm_validation_rows'],
        'first_development_rescue':ns['serial'](gain_full),'correct_layer_table':expected,
        'outside_E_remaining_group_obstruction':excluded,'necessary_condition_plus_K_not_sufficient_example':necessity_failure,
        'new_bound_reconstructs_full_W':False,'norm_bound_uses_order8_argument':False,
        'lower_bound_values_on_development_set_not_holdout':True,'development_inputs_overlap_old10_at_p18490201':True}
(run/'l8-additional-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
