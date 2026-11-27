"""Independently verify all axis profiles without importing any search routine."""
from collections import Counter
from functools import lru_cache
import gzip
from itertools import combinations_with_replacement, product
import json


def domain(n,pmax):
    out=set()
    for start in range(n):
        for end in range(start+n//2-1,n):
            for p in range(1,pmax+1):
                for residues in range(1,2**p):
                    v=tuple(i for i in range(start,end+1) if residues>>int(i%p)&1)
                    if len(v)==n//2: out.add(v)
    return len(out),sorted({min(v,tuple(n-i-1 for i in reversed(v))) for v in out})


class Case:
    def __init__(self,n,a,b):
        self.n=n
        self.r=sorted(set(range(n))-set(a)); self.c=sorted(set(range(n))-set(b))
        self.holes={(x-y,x+y) for x in a for y in b}
        self.support=[Counter(x-y for x in self.r for y in self.c),
                      Counter(x+y for x in self.r for y in self.c)]
        self.forced=[{d for d,s in self.holes if self.support[1][s]<2},
                     {s for d,s in self.holes if self.support[0][d]<2}]

    def check_quick(self,reason,proof):
        if reason=='matching':
            assert len(proof)>self.n and len({d for d,s in proof})==len({s for d,s in proof})==len(proof)
            assert all(tuple(e) in self.holes for e in proof)
        elif reason=='uncoverable':
            d,s=proof
            assert (d,s) in self.holes and self.support[0][d]<2 and self.support[1][s]<2
        elif reason=='forced_lane_capacity':
            ds,ss=map(set,proof)
            assert ds<=self.forced[0] and ss<=self.forced[1] and max(len(ds),len(ss))>self.n//2
        else:
            raise AssertionError(reason)

    def leaves(self,proof):
        n=self.n
        @lru_cache(None)
        def sq(f,chosen):
            required=2*(sum(self.r)+(-1 if f==0 else 1)*sum(self.c))
            m=n-2*len(chosen)
            assert m in range(7)
            rem=required-2*sum(chosen)
            weights=[k for k in self.support[f] if k not in chosen]
            # Direct multiset enumeration; the search instead recurses on
            # possible remaining sums. Legal multiplicity also respects support.
            sums=set()
            for v in combinations_with_replacement(weights,m):
                if sum(v)!=rem: continue
                if any(c>min(2,self.support[f][k]) for k,c in Counter(v).items()): continue
                sums.add(2*sum(k*k for k in chosen)+sum(k*k for k in v))
            return sums
        total=4*sum(x*x for x in self.r+self.c)
        hist=Counter()
        def walk(node,ds,ss):
            if node=='Q':
                assert max(len(ds),len(ss))>n//2
                hist['quota']+=1
                return
            if node=='M':
                assert len(ds)<=n//2 and len(ss)<=n//2
                assert all(d in ds or s in ss for d,s in self.holes)
                a,b=sq(0,ds),sq(1,ss)
                assert not any(total-x in b for x in a)
                hist['moment']+=1
                return
            f,k,left,right=node
            assert f in (0,1)
            touching={p[1-f] for p in self.holes if p[f]==k and p[0] not in ds and p[1] not in ss}
            assert touching
            if f==0:
                walk(left,ds|{k},ss)
                walk(right,ds,ss|touching)
            else:
                walk(left,ds,ss|{k})
                walk(right,ds|touching,ss)
        walk(proof,*map(frozenset,self.forced))
        return hist


def check():
    with gzip.open('clipped_cert.json.gz','rt') as f: doc=json.load(f)
    with gzip.open('clipped_trees.json.gz','rt') as f: trees=json.load(f)
    count,ax=domain(30,5)
    assert count==doc['raw'] and [list(v) for v in ax]==doc['unused']
    pending=set(combinations_with_replacement(range(len(ax)),2))
    assert len(pending)==3403 and doc['n']==30 and doc['pmax']==5
    for i,j,reason,p in doc['rejects']:
        pending.remove((i,j))
        Case(30,ax[i],ax[j]).check_quick(reason,p)
    assert sorted(pending)==sorted(map(tuple,doc['kept']))
    hist=Counter()
    for i,j,t in trees:
        pending.remove((i,j))
        hist.update(Case(30,ax[i],ax[j]).leaves(t))
    assert not pending
    print('PASS',count,'axes,',len(ax),'axis reps, 3403 pairs,',len(trees),'trees;',dict(hist))
    i,j,t=trees[0]
    try:
        Case(30,ax[i],ax[j]).leaves('M')
    except AssertionError:
        print('PASS bogus unsplit root rejected')
    else:
        raise AssertionError('corruption accepted')

if __name__=='__main__':
    check()
