import json
import sys
from collections import Counter
from pathlib import Path

run=Path(sys.argv[1])
rows=json.loads((run/'type-branches-all-rows.json').read_text())
counts=Counter()
examples={}
result=[]
for row in rows:
    c=row['c']
    H={1}
    todo=[1]
    generators=[q%c for q,e in row['factor_x']]
    while todo:
        h=todo.pop()
        for q in generators:
            v=h*q%c
            if v not in H:
                H.add(v)
                todo.append(v)
    # x is in H. Thus -px = -4x^2 and -x membership reduce to -4 and -1.
    groupI=(-4)%c in H
    groupII=(-1)%c in H
    assert groupI==((-row['p']*row['x'])%c in H)
    assert groupII==((-row['x'])%c in H)
    actualI=bool(row['TypeI'])
    actualII=bool(row['TypeII'])
    assert not actualI or groupI
    assert not actualII or groupII
    labelI='success' if actualI else 'exponent' if groupI else 'group'
    labelII='success' if actualII else 'exponent' if groupII else 'group'
    key=labelI+'/'+labelII
    counts[key]+=1
    item={'p':row['p'],'c':c,'x':row['x'],'factor_x':row['factor_x'],'group_residues':sorted(H),'I_status':labelI,'II_status':labelII,'divisors_x_squared':row['divisors_x_squared']}
    result.append(item)
    examples.setdefault(key,item)
out={'all_rows':len(rows),'classification_counts':dict(counts),'first_examples':examples,'interpretation':'A finite subgroup test is necessary, not sufficient. Exponent means target lies in generated subgroup but is absent from bounded exponent divisors. Type-II ordering loses no target because complement d -> x^2/d preserves target -x. No global existence claim.'}
(run/'branch-group-analysis.json').write_text(json.dumps(out,indent=2)+'\n')
(run/'branch-group-all-rows.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(out,indent=2))
