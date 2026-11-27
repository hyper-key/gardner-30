"""Independently regenerate the complete-diagonal, equal-span projected domain."""
from collections import Counter,defaultdict
from functools import lru_cache
from itertools import combinations_with_replacement
from pathlib import Path
import sys
import time

def canonical(w,n):
    return min(w,int(f'{w:0{n}b}'[::-1],2))

@lru_cache(None)
def missing_cells(e,mask):
    vals={i for i in range(e) if mask>>i&1}
    return [[a for a in vals if (a+b)%e not in vals and (a-b)%e not in vals] for b in range(e)]

@lru_cache(None)
def side(e,a,b):
    holes=missing_cells(e,a)
    graph=defaultdict(set)
    for j in range(e):
        if not b>>j&1: continue
        if len(holes[j])>2: return False
        for i in holes[j]:
            graph[(i-j)%e].add((i+j)%e)
    # A third augmenting path certifies that >=3 distinct lines are required.
    right={}
    def augment(x,seen):
        for y in graph[x]:
            if y not in seen:
                seen.add(y)
                if y not in right or augment(right[y],seen):
                    right[y]=x
                    return True
        return False
    for x in graph:
        augment(x,set())
        if len(right)>=3: return False
    return True

def generate(shapes,n=30):
    scopes=defaultdict(set)
    for e,m in shapes:
        for off in range(n-e):
            w=canonical((m|(1<<e))<<off,n)
            vals=[i for i in range(n) if w>>i&1]
            z=[2*i-(n-1) for i in vals]  # unused axes
            # Using unused squares gives active H plus the same constant on each axis.
            invariant=21*sum(z)**2+5*sum(x*x for x in z)
            q=(w>>vals[0])&~(1<<e)
            scopes[e,invariant].add((w,q))
    result=set()
    for (e,h),axes in scopes.items():
        for (ar,a),(br,b) in combinations_with_replacement(sorted(axes),2):
            if side(e,a,b) and side(e,b,a):
                result.add((ar,br))
    return result

def parse_ref(lines,n):
    pairs=set()
    for line in lines:
        e,a,b,ta,tb=map(int,line.split())
        pair=tuple(sorted(canonical((x|(1<<e))<<t,n) for x,t in [(a,ta),(b,tb)]))
        assert pair not in pairs
        pairs.add(pair)
    return pairs
if __name__=='__main__':
    t=time.process_time()
    shapes=[tuple(map(int,x.split())) for x in Path(sys.argv[1]).read_text().splitlines()]
    actual=generate(shapes)
    expected=parse_ref(Path(sys.argv[2]).read_text().splitlines(),30)
    assert actual==expected, (len(actual-expected),len(expected-actual))
    print('PASS shape count',len(shapes),'canonical full-span pairs',len(actual))
    print('spans',dict(sorted(Counter(w.bit_length()-((w&-w).bit_length()) for w,v in actual).items())))
    import hashlib
    content=''.join(f'{w} {v}\n' for w,v in sorted(actual)).encode()
    print('canonical SHA256',hashlib.sha256(content).hexdigest(),'CPU seconds',round(time.process_time()-t,3))
