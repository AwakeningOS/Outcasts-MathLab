"""Pre-execution contract: falsify the proposed all-vertex one-edge rescue lemma.

Candidate U1: for every hard prime p and every NR-prime q<p, if all allowed
square sources at q fail both exact divisor tests, some outgoing NR-prime
factor r has a successful allowed source. U1 implies E1 and global occupancy.
Unlike E1, q is not restricted to the least nonresidue. A failed cycle alone
does not refute U1: a successful outside neighbor may exist.

Inputs fixed in advance: p=2521, then 12889 only if no counterexample at 2521.
At each input enumerate the whole finite graph, all odd tau with sigma*q*tau^2
<3p, and all divisors of x^2 (full exponent caps). Reverse BFS from all locally
successful vertices gives exact shortest distances. Stop after the first input
with D(q)>1 or an unreachable vertex; choose the smallest counterexample q.
Record all sources of q and every direct neighbor, plus one shortest escape.
An unreachable vertex is only a square-source-method obstruction, not an ESC
counterexample. No counterexample in these fixed inputs proves nothing global.
Budget: one CPU process on mini, 120 seconds; no prime-range expansion, no GPU.
Independent replay uses literal quadratic residue sets, trial-divisor pairs,
and iterative reachability, and must match before any publication.
"""
import collections, json, math, time
from pathlib import Path

def factor(n):
    out={};r=2
    while r*r<=n:
        while n%r==0:out[r]=out.get(r,0)+1;n//=r
        r=3 if r==2 else r+2
    if n>1:out[n]=out.get(n,0)+1
    return out
def divisors(f):
    ans=[1]
    for r,e in f.items():ans=[a*r**j for a in ans for j in range(e+1)]
    return sorted(ans)
def sigma(q):return 1 if q%4==3 else 3
def chi(a,p):return -1 if pow(a,(p-1)//2,p)==p-1 else 1
def isprime(n):return n>=2 and factor(n)=={n:1}
def rows(p,q):
    out=[]
    for t in range(1,math.isqrt((3*p-1)//(sigma(q)*q))+1,2):
        c=sigma(q)*q*t*t;x=(p+c)//4;f=factor(x)
        assert (p+c)%4==0 and 0<x<p and math.gcd(c,x)==1 and chi(x,p)==-1
        ds=divisors({r:2*e for r,e in f.items()})
        hits={key:[d for d in ds if (d+k*x)%c==0] for key,k in [('I',p),('II',1)]}
        out.append(dict(q=q,tau=t,c=c,x=x,factors=f,divisors_x_squared=ds,hits=hits,
                        children=[r for r in f if chi(r,p)==-1]))
    assert out
    return out
def good(row):return bool(row['hits']['I'] or row['hits']['II'])

def main():
    start=time.monotonic();runs=[]
    for p in (2521,12889):
        assert isprime(p) and p%840 in {1,121,169,289,361,529}
        vs=[q for q in range(3,p,2) if isprime(q) and chi(q,p)==-1]
        sources={q:rows(p,q) for q in vs}
        edges={q:sorted({r for z in sources[q] for r in z['children']}) for q in vs}
        goods=[q for q in vs if any(map(good,sources[q]))]
        reverse={q:[] for q in vs}
        for q in vs:
            assert edges[q] and q not in edges[q]
            for r in edges[q]:reverse[r].append(q)
        dist={q:0 for q in goods};queue=collections.deque(goods)
        while queue:
            r=queue.popleft()
            for q in reverse[r]:
                if q not in dist:dist[q]=dist[r]+1;queue.append(q)
        bad=[q for q in vs if q not in dist or dist[q]>1]
        run=dict(p=p,vertex_count=len(vs),source_count=sum(map(len,sources.values())),
                 sources=sources,edges=edges,successful_vertices=goods,distances=dist,
                 distance_histogram=dict(collections.Counter(dist.values())),
                 unreachable=[q for q in vs if q not in dist],U1_counterexample_vertices=bad)
        if bad:
            q=bad[0];path=[q]
            while path[-1] in dist and dist[path[-1]]:
                path.append(min(r for r in edges[path[-1]] if dist[r]==dist[path[-1]]-1))
            path_rows=[]
            for a,b in zip(path,path[1:]):
                z=next(z for z in sources[a] if b in z['children']);path_rows.append(z)
            if path[-1] in goods:
                z=next(z for z in sources[path[-1]] if good(z));branch=next(k for k in ['I','II'] if z['hits'][k]);d=z['hits'][branch][0];x=z['x'];c=z['c']
                if branch=='I':y=(d+p*x)//c;zz=(p*p*(x*x//d)+p*x)//c
                else:y=p*((d+x)//c);zz=p*((x*x//d+x)//c)
                assert min(x,y,zz)>0 and 4*x*y*zz==p*(x*y+x*zz+y*zz)
                certificate=dict(source=z,branch=branch,d=d,denominators=[x,y,zz])
            else:certificate=None
            run['selected']=dict(q=q,neighbors=edges[q],shortest_path=path,edge_sources=path_rows,
                                 terminal=certificate,
                                 failure_vertex_set=[q]+edges[q],
                                 failure_source_count=sum(len(sources[r]) for r in [q]+edges[q]))
        runs.append(run)
        assert time.monotonic()-start<120
        if bad:break
    result=dict(contract='U1 all-vertex one-edge rescue; fixed inputs 2521 then 12889; stop at first refuting input',runs=runs,
                seconds=time.monotonic()-start,Lean_executed=False,ESC_counterexample_search=False)
    (Path(__file__).resolve().parent/'graph-depth-results.json').write_text(json.dumps(result,indent=2)+'\n')
    for r in runs:
        print(json.dumps({k:r[k] for k in ['p','vertex_count','source_count','distance_histogram','unreachable','successful_vertices','selected'] if k in r}))

if __name__=='__main__':main()
