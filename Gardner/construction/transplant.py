"""Enumerate all legal extensions of a translated intact seed, through a fixed depth."""
import argparse
import json
import time
from collections import Counter
from itertools import product
from pathlib import Path

def lines(p):
    r,c=p
    return (0,r),(1,c),(2,r+c),(3,r-c)

def extend(seed, n, depth):
    counts=Counter(key for p in seed for key in lines(p))
    assert len(set(seed))==len(seed) and max(counts.values(),default=0)<=2
    free=[p for p in product(range(n), repeat=2) if p not in seed and
          all(counts[k]<2 for k in lines(p))]
    idx={k:i for i,k in enumerate({k for p in free for k in lines(p)})}
    members=[0]*len(idx)
    labels=[]
    for b,p in enumerate(free):
        labels.append([idx[k] for k in lines(p)])
        for i in labels[-1]:
            members[i] |= 1<<b
    existing=sum(1<<i for k,i in idx.items() if counts[k]==1)
    seen, hist = [0]*(depth+1), Counter()
    best=len(free)+1
    top=None
    def dfs(t, available, unused, singles, moves):
        nonlocal best, top
        seen[t]+=1
        if t==depth:
            holes=available.bit_count()
            hist[holes]+=1
            if holes<best:
                best,top=holes,moves
            return
        while unused:
            bit=unused & -unused
            b=bit.bit_length()-1
            unused ^= bit
            blocked=bit
            new_single=singles
            for i in labels[b]:
                mask=1<<i
                if singles & mask:
                    blocked |= members[i]
                new_single ^= mask
            dfs(t+1,available & ~blocked, unused & ~blocked,new_single,moves+(b,))
    full=(1<<len(free))-1
    dfs(0,full,full,existing,())
    return seen,hist,best,([free[b] for b in top] if top is not None else [])

def main():
    p=argparse.ArgumentParser()
    p.add_argument('witness')
    p.add_argument('--n',type=int,default=30)
    p.add_argument('--q',type=int,default=30)
    p.add_argument('--out',default='transplant-result.json')
    a=p.parse_args()
    data=json.loads(Path(a.witness).read_text())
    best=a.n**2
    t0=time.monotonic()
    q=a.q-len(data['queens'])
    totals=[0]*(q+1)
    rows=[]
    for i,j in product(range(a.n-data['n']+1),repeat=2):
        orig=[(x+i,y+j) for x,y in data['queens']]
        seen,hist,h,extra=extend(orig,a.n,q)
        totals=[x+y for x,y in zip(totals,seen)]
        rows.append({'offset':[i,j],'legal_extensions':seen,'best_holes':h,
                     'histogram':dict(sorted(hist.items()))})
        if h<best:
            best=h
            bestdata={'n':a.n,'queens':sorted(orig+extra),'offset':[i,j],'extra':extra,
                      'holes':h}
        print('offset',i,j,'legal final',seen[-1],'best',h,flush=True)
    doc={'source':a.witness,'target':[a.n,a.q],'totals':totals,'best':bestdata,'rows':rows}
    Path(a.out).write_text(json.dumps(doc,indent=2)+'\n')
    print('sum',totals,'best',best,'elapsed',round(time.monotonic()-t0,3))
if __name__=='__main__':
    main()
