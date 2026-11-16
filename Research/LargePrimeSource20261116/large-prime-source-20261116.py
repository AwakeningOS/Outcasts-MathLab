"""Finite periodic certificate for the j=1 case, not a finite prime scan."""
import json
from math import gcd
from pathlib import Path
from collections import Counter
from time import monotonic

HARD = (1,121,169,289,361,529)

def main():
    start=monotonic()
    rows=[]
    for s in range(1,9):
        for sigma in (1,3):
            for alpha in range(1,s+1):
                for beta in range(1,s+1):
                    if s%(alpha*beta) or gcd(alpha,beta)!=1:
                        continue
                    for h in range(1,3*alpha+1):
                        row=dict(s=s,sigma=sigma,alpha=alpha,beta=beta,h=h)
                        if alpha>=sigma*h:
                            row['outcome']='q_range'
                        elif 4*h*s>9*(h+alpha):
                            row['outcome']='r_range'
                        else:
                            period=840*h*s*sigma
                            counts=Counter()
                            survivors=[]
                            for t in range(h*s*sigma):
                                for residue in HARD:
                                    p=840*t+residue
                                    counts['p_classes']+=1
                                    if (alpha*p+beta)%(h*sigma):continue
                                    q=(alpha*p+beta)//(h*sigma)
                                    counts['q_integer']+=1
                                    if q%4!=(3 if sigma==1 else 1):continue
                                    counts['q_type']+=1
                                    if gcd(q,210)!=1:continue
                                    counts['q_small_prime_free']+=1
                                    if ((h+alpha)*p+beta)%(4*h*s):continue
                                    r=((h+alpha)*p+beta)//(4*h*s)
                                    counts['r_integer']+=1
                                    if gcd(r,210)!=1:continue
                                    counts['r_small_prime_free']+=1
                                    survivors.append(p)
                            row.update(period=period,counts=dict(counts),
                                       survivors=survivors,
                                       outcome='unresolved' if survivors else 'congruence')
                        rows.append(row)
    summary=dict(tuples=len(rows),outcomes=dict(Counter(x['outcome'] for x in rows)),
                 unresolved=[x for x in rows if x['outcome']=='unresolved'],
                 seconds=monotonic()-start)
    Path('large-prime-source-results.json').write_text(json.dumps(dict(summary=summary,rows=rows),indent=2)+'\n')
    print(json.dumps(summary,indent=2))

if __name__=='__main__':main()
