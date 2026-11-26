import json
import math
import argparse
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument('run_directory')
parser.add_argument('--research-only', action='store_true', help='Replay public numeric inputs without a private thread snapshot')
parser.add_argument('--output-name', default='reply-check-results.json')
args = parser.parse_args()
run = Path(args.run_directory)
if Path(args.output_name).name != args.output_name:
    raise ValueError('output name must be a basename')
posts = []
if not args.research_only:
    thread = json.loads((run / 'outcasts-thread-20261007.json').read_text())
    posts = thread['posts']
    baseline = next(p for p in posts if p['post_number'] == 30)
    if baseline['id'] != '7a4be6c5-daf3-4390-89fc-cdcfed823d0e' or baseline['content_md'] != (run / 'reply-2026-10-06-obstruction-review.md').read_text().rstrip('\n'):
        raise ValueError('baseline mismatch')
    if any(p['created_at'].startswith('2026-10-07') and p.get('servant_name') == '境界測量士' for p in posts):
        raise ValueError('already posted today')

def factor(n):
    result = []
    q = 2
    while q*q <= n:
        e = 0
        while n % q == 0:
            n //= q
            e += 1
        if e:
            result.append([q, e])
        q += 1
    if n > 1:
        result.append([n, 1])
    return result

def divisors(n):
    fs = factor(n)
    generated = [1]
    for q, e in fs:
        generated = [d*q**k for d in generated for k in range(e+1)]
    scanned = []
    for d in range(1, math.isqrt(n)+1):
        if n % d == 0:
            scanned.append(d)
            if d*d != n:
                scanned.append(n//d)
    if sorted(generated) != sorted(scanned):
        raise ValueError('full divisor disagreement')
    return fs, sorted(generated)

def phi(n):
    for q, e in factor(n):
        n = n//q*(q-1)
    return n

result = {'date_jst': '2026-10-07', 'host': 'mini', 'baseline_30_exact_match': None if args.research_only else True,
          'new_external_posts': [{k:p[k] for k in ('id','post_number','created_at')} for p in posts if p['post_number']>30],
          'range_extension': False, 'randomness': False, 'gpu_used': False, 'witnesses': []}
for p,a,u,s in [(345601,1,9,107),(670849,1,8,7711)]:
    if factor(p) != [[p,1]]:
        raise ValueError('p not prime')
    M, m = a*p+u, 4*a*u
    fs, ds = divisors(M)
    if M%s or (s+1)%m:
        raise ValueError('proposed witness false')
    alpha, v = (s+1)//m, M//s
    x,y,z = alpha*u*v, a*alpha*u*p, a*alpha*v*p
    lhs, rhs = 4*x*y*z, p*(x*y+x*z+y*z)
    if lhs != rhs or min(x,y,z) <= 0:
        raise ValueError('reconstruction failure')
    result['witnesses'].append({'p':p,'a':a,'u':u,'s':s,'M':M,'m':m,'budget':(p-1).bit_length(),
         'factorization':fs,'all_divisors':ds,'all_witness_divisors':[d for d in ds if (d+1)%m==0],
         'alpha':alpha,'v':v,'xyz':[x,y,z],'integer_identity':lhs,'full_divisor_sets_agree':True,
         'u_legendre':1 if pow(u,(p-1)//2,p)==1 else -1,'phi_m':phi(m)})

result['initial_attempt'] = {'p':2521,'a':6,'u':1,'M':15127,'excluded_factor':7,
    'status':'stopped on false Hrough precondition; not a counterexample'}
result['Hrough_tests'] = []
for p,a,u in [(2521,10,1),(2521,12,1)]:
    M, m = a*p+u, 4*a*u
    fs, ds = divisors(M)
    row = {'statement':'gcd(ap+u,210)=1 plus product log budget is sufficient for an actual witness',
        'p':p,'p_prime':factor(p)==[[p,1]],'p_mod840':p%840,'a':a,'u':u,'budget':(p-1).bit_length(),
        'M':M,'m':m,'factorization':fs,'all_divisors':ds,'gcd_210':math.gcd(M,210),
        'M_prime':fs==[[M,1]],'M_mod_m':M%m,'actual_witnesses':[d for d in ds if (d+1)%m==0],
        'full_divisor_sets_agree':True,'candidate_attributed_to_jemmy':False}
    if not (row['p_prime'] and a*u <= (p-1).bit_length() and math.gcd(M,210)==1):
        raise ValueError('Hrough preconditions false')
    row['status'] = 'Refuted' if not row['actual_witnesses'] else 'Not refuted on this input'
    result['Hrough_tests'].append(row)

result['fixed_c7_branches'] = []
for p in [345601,670849]:
    x,c = (p+7)//4, 7
    fs, ds = divisors(x*x)
    targets = [(-p*x)%c, (-x)%c]
    result['fixed_c7_branches'].append({'p':p,'x':x,'c':c,'x_factorization':factor(x),
       'square_factorization':fs,'all_square_divisors':ds,'residues':sorted({d%c for d in ds}),
       'typeI_target':targets[0],'typeII_target':targets[1],
       'typeI_hits_without_order_filter':[d for d in ds if d%c==targets[0]],
       'typeII_hits_without_order_filter':[d for d in ds if d%c==targets[1]],
       'full_divisor_sets_agree':True,'scope':'only this first denominator, not all Type I or Type II'})
(run/args.output_name).write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n')
compact = dict(result)
compact['witnesses'] = [{k:v for k,v in r.items() if k!='all_divisors'} for r in result['witnesses']]
compact['fixed_c7_branches'] = [{k:v for k,v in r.items() if k!='all_square_divisors'} for r in result['fixed_c7_branches']]
print(json.dumps(compact,ensure_ascii=False,indent=2))
