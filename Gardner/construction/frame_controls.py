"""Small, literal square/diagonal domain checks independent of the production projection."""
import itertools
import subprocess
import sys
from audit_full_frame import canonical,generate

def literal(e,a,b,which):
    edges=[]
    for x,y in itertools.product(a,b):
        u=x+y; v=x-y
        if which==1:
            ok=(u%e in a or v%e in a)
        elif which==2:
            ok=(u%e in b or (-v)%e in b)
        else:
            ok=(u%e in a and u%e in b) or (v%e in a and (-v)%e in b)
        if not ok: edges.append(((0,v%e),(1,u%e)))
    types=[(f,k) for f in (0,1) for k in range(e)]
    return any(all(d in keys or s in keys for d,s in edges)
               for keys in itertools.combinations(types,2))

def mask(axis):
    return sum(1<<x for x in axis)

def small(exe,n,p):
    intervals={}
    for points in itertools.combinations(range(n),p+1):
        e=points[-1]-points[0]
        intervals.setdefault(e,[]).append((points,{v-points[0] for v in points[:-1]}))
    tight,loose=set(),set()
    for e,items in intervals.items():
        for (r,a),(c,b) in itertools.combinations_with_replacement(items,2):
            if sum(r)==sum(c) and literal(e,a,b,0):
                ta,tb=r[0],c[0]
                if mask(a)>mask(b):a0,b0,ta,tb=mask(b),mask(a),tb,ta
                else:a0,b0=mask(a),mask(b)
                tight.add((e,a0,b0,ta,tb))
            def h(z):
                active=[2*x-(n-1) for x in range(n) if x not in z]
                return 21*sum(active)**2-5*sum(x*x for x in active)
            if h(r)==h(c) and literal(e,a,b,1) and literal(e,a,b,2):
                loose.add(tuple(sorted((canonical(mask(r),n),canonical(mask(c),n)))))
    actual=subprocess.check_output([exe,str(n),str(p)],text=True,stderr=subprocess.DEVNULL)
    assert tight=={tuple(map(int,line.split())) for line in actual.splitlines()}
    shapes=subprocess.check_output([exe,str(n),str(p),'shapes'],text=True,stderr=subprocess.DEVNULL)
    assert loose==generate([tuple(map(int,l.split())) for l in shapes.splitlines()],n)
    return len(tight),len(loose)

def boundary():
    # Check the geometric implication at all cells and frame intercepts, including
    # one-hit/corner lines. Classify ACTUAL integer diagonals before reducing mod e.
    tally=[0,0,0]
    counts=[0,0,0]
    for e in range(2,8):
        def choices():
            for s in itertools.combinations(range(1,e),2):
                yield {0,e,*s}
        for A,B in itertools.product(choices(),repeat=2):
            grid=set(itertools.product(A,B))
            border={p for p in grid if p[0] in (0,e) or p[1] in (0,e)}
            U={v%e for v in A};V={v%e for v in B}
            for slope in (-1,1):
                for k in {y-slope*x for x,y in grid}:
                    line={(x,y) for x,y in grid if y-slope*x==k}
                    hits=line&border
                    tally[len(hits)]+=1
                    for x,y in line:
                        d=(x-y)%e;s=(x+y)%e
                        rowgood=s in U if slope==-1 else d in U
                        colgood=s in V if slope==-1 else (-d)%e in V
                        if any(y0 in (0,e) for _,y0 in hits): assert rowgood
                        if any(x0 in (0,e) for x0,_ in hits): assert colgood
                        if len(hits)==2: assert rowgood and colgood
                        counts[len(hits)]+=1
    assert all(tally)
    print('actual diagonals with 0/1/2 distinct frame hits',tally,'cell incidence checks',counts)

if __name__=='__main__':
    for n,p in [(6,2),(8,3),(10,4)]:
        print('literal small domains matched',n,p,small(sys.argv[1],n,p))
    boundary()
