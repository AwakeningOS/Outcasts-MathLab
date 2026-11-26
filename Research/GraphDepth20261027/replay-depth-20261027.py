"""Independent replay: no import of the discovery implementation.
Use sieve, literal squares, trial divisor pairs and iterative layers.
"""
import json,math,time
from pathlib import Path
r=Path(__file__).resolve().parent;data=json.loads((r/'graph-depth-results.json').read_text());start=time.monotonic()
checks=[]
for run in data['runs']:
    p=run['p'];sieve=[True]*(p+1);sieve[0]=sieve[1]=False
    for k in range(2,math.isqrt(p)+1):
        if sieve[k]:
            for n in range(k*k,p+1,k):sieve[n]=False
    assert sieve[p]
    qr={k*k%p for k in range(1,p)}
    vertices=[q for q in range(2,p) if sieve[q] and q not in qr]
    assert set(map(str,vertices))==set(run['sources'])
    edge={};goods=set();total=0;divcount=0
    for q in vertices:
        a=q if q%4==3 else 3*q;t=1;rows=run['sources'][str(q)];ix=0;edge[q]=set()
        while a*t*t<3*p:
            c=a*t*t;x=(p+c)//4
            ds=set()
            for d in range(1,x+1):
                if x*x%d==0:ds.update((d,x*x//d))
            I=sorted(d for d in ds if (d+p*x)%c==0);II=sorted(d for d in ds if (d+x)%c==0)
            children={b for b in vertices if b<=x and x%b==0}
            row=rows[ix];assert row['tau']==t and row['x']==x and row['c']==c
            assert sorted(ds)==row['divisors_x_squared'] and row['hits']=={'I':I,'II':II}
            assert children==set(row['children'])
            assert all(sieve[int(b)] for b in row['factors']) and math.prod(int(b)**e for b,e in row['factors'].items())==x
            # Original two-unit-fraction residual test: D | (p*x)^2,
            # D == -p*x mod c. p is prime and coprime to x.
            residual=[d*p**e for d in ds for e in range(3) if (d*p**e+p*x)%c==0]
            assert bool(residual)==bool(I or II)
            if I or II:goods.add(q)
            edge[q].update(children);total+=1;divcount+=len(ds);ix+=1;t+=2
        assert ix==len(rows) and edge[q]==set(run['edges'][str(q)])
    assert goods==set(run['successful_vertices'])
    # Monotone reachability layers, separate from discovery's reverse BFS.
    layers=[goods.copy()];distance={q:0 for q in goods}
    while True:
        more={q for q in vertices if edge[q]&layers[-1]}|layers[-1]
        if more==layers[-1]:break
        for q in more-layers[-1]:distance[q]=len(layers)
        layers.append(more)
    assert distance=={int(q):v for q,v in run['distances'].items()}
    sel=run['selected'];q=sel['q'];fails=[q]+sorted(edge[q])
    assert all(v not in goods for v in fails) and distance[q]==2
    cert=sel['terminal'];x,y,z=cert['denominators'];assert 4*x*y*z==p*(x*y+x*z+y*z)
    checks.append(dict(p=p,all_graph_sources=total,divisors_tested=divcount,all_edges_match=True,
      original_residual_test_matches=True,iterative_layers_match=True,
      failure_sources={v:len(run['sources'][str(v)]) for v in fails},
      distance_six_vertices=[q for q,d in distance.items() if d==6],
      q17_sources=[{k:z[k] for k in ['tau','c','x','factors','children']} for z in run['sources']['17']]))
result=dict(passed=True,checks=checks,seconds=time.monotonic()-start)
(r/'independent-replay.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
