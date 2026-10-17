import hashlib
import importlib.util
import json
import math
import time
from pathlib import Path

RUN = Path('/mnt/hdd1t/outcasts-reply-20261010-DnoRad')
spec = importlib.util.spec_from_file_location('kb', RUN / 'test-kneser-budget-20261010.py')
kb = importlib.util.module_from_spec(spec)
spec.loader.exec_module(kb)
paths = ['/mnt/hdd1t/outcasts-witness-budget-20260930-r3Gjat/results.json',
         '/mnt/hdd1t/outcasts-witness-budget-20260930-r3Gjat/results-2m-100m.json']
rows, sources = [], []
for name in paths:
    d = json.loads(Path(name).read_text())
    raw = json.dumps(d['rows'], sort_keys=True, separators=(',', ':')).encode()
    digest = hashlib.sha256(raw).hexdigest()
    assert digest == d['summary']['rows_sha256']
    assert len(d['rows']) == d['summary']['target_primes']
    sources.append({'path':name,'rows':len(d['rows']),'rows_sha256':digest,
                    'declared_start':d['summary'].get('start'), 'actual_min_p':min(r['p'] for r in d['rows']),
                    'actual_max_p':max(r['p'] for r in d['rows']), 'limit':d['summary']['limit']})
    rows.extend(d['rows'])
rows.sort(key=lambda r:r['p'])
assert len(rows)==179468 and len({r['p'] for r in rows})==len(rows)
assert all(r['p']%840 in {1,121,169,289,361,529} and r['budget']==(r['p']-1).bit_length() for r in rows)
start = time.monotonic()
count, extra_boxes, slow_pass, failure, last_p = 0, 0, [], None, None
for old in rows:
    if time.monotonic()-start>=180:
        break
    p, B, hit = old['p'], old['budget'], old['witness']
    assert hit and (hit['s']+1)%(4*hit['a']*hit['u'])==0 and (hit['a']*p+hit['u'])%hit['s']==0
    r = kb.row(p,hit['a'],hit['u'])
    if not r['K']:
        extra_boxes += 1
        rs = []
        good = None
        for cost,a,u in sorted((a*u,a,u) for a in range(1,B+1) for u in range(1,B//a+1) if math.gcd(a,u)==1):
            rr = kb.row(p,a,u)
            rs.append(rr)
            if rr['K']:
                good = rr
                break
        if good:
            slow_pass.append({'p':p,'old_pair':[hit['a'],hit['u']],'new_K_pair':[good['a'],good['u']],
                              'old_has_actual_witness':True,'old_K':False})
        else:
            failure = {'p':p,'budget':B,'coprime_pairs':len(rs),'old_witness':hit,
                       'actual_success_pairs':sum(bool(z['witnesses']) for z in rs),
                       'failure_counts':{k:sum(z.get('failure_kind')==k for z in rs) for k in ['group_obstruction','insufficient_Kneser_bound']}}
            (RUN / 'counterexample-kneser-all-rows.json').write_text(json.dumps(rs,indent=2)+'\n')
            count += 1
            last_p=p
            break
    count += 1
    last_p=p
    if count%10000==0:
        print(json.dumps({'checked':count,'last_p':p,'seconds':round(time.monotonic()-start,2),'extra_boxes':extra_boxes}),flush=True)
result = {'candidate':'HKlog','sources':sources,'source_rows':len(rows),'checked_inputs':count,
          'checked_through_p':last_p,'all_source_inputs_checked':count==len(rows),
          'extra_boxes':extra_boxes,'different_K_pair_passes':slow_pass,'counterexample':failure,
          'stop_reason':'first_counterexample' if failure else ('all_source_inputs' if count==len(rows) else '180_second_limit'),
          'elapsed_seconds':round(time.monotonic()-start,3),'universal_existence_proved':False,
          'Hlog_refuted':False,'ESC_refuted':False,'new_integer_range_extension':False}
(RUN / 'kneser-existing-cohort-results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='different_K_pair_passes'},indent=2),flush=True)
