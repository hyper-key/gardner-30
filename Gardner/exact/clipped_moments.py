"""Branch on diagonal covers, then screen necessary first and second moments."""
from collections import Counter
from functools import lru_cache
import gzip
from itertools import product
import json
from pathlib import Path
import time


def enumerate_marginals(support, forced, n, needed_sum):
    rem=n-2*len(forced)
    if rem>6:
        raise RuntimeError(f'unexpected marginal dimension {rem}')
    options=sorted(k for k,v in support.items() if v>0 and k not in forced)
    target=needed_sum-2*sum(forced)
    out=[]
    def rec(start,remaining,target,chosen):
        if not remaining:
            if target==0: out.append(tuple(chosen))
            return
        if start==len(options) or target<remaining*options[start] or target>remaining*options[-1]:
            return
        if remaining==1:
            if target in support and target not in forced and target>=options[start]:
                out.append(tuple(chosen+[target]))
            return
        for i in range(start,len(options)):
            k=options[i]
            if k*remaining>target: break
            rec(i+1,remaining-1,target-k,chosen+[k])
            if support[k]>=2:
                rec(i+1,remaining-2,target-2*k,chosen+[k,k])
    rec(0,rem,target,[])
    return out


def profiles(n,ur,uc):
    rows=set(range(n))-set(ur); cols=set(range(n))-set(uc)
    supports=[Counter(x-y for x in rows for y in cols),Counter(x+y for x in rows for y in cols)]
    holes={(r-c,r+c) for r in ur for c in uc}
    df=frozenset(d for d,s in holes if supports[1][s]<2)
    sf=frozenset(s for d,s in holes if supports[0][d]<2)
    stats=Counter()
    verified=set()
    @lru_cache(None)
    def extra(f,keys):
        return enumerate_marginals(supports[f],keys,n,2*(sum(rows)+(-1 if f==0 else 1)*sum(cols)))
    @lru_cache(None)
    def visit(ds,ss):
        stats['nodes']+=1
        if len(ds)>n//2 or len(ss)>n//2:
            return
        edges=[(d,s) for d,s in holes if d not in ds and s not in ss]
        if edges:
            degree=Counter((f,e[f]) for e in edges for f in (0,1))
            f,k=max(degree,key=lambda k:(degree[k],k))
            neighbors={e[1-f] for e in edges if e[f]==k}
            if f==0:
                visit(ds|{k},ss)
                visit(ds,ss|neighbors)
            else:
                visit(ds,ss|{k})
                visit(ds|neighbors,ss)
            return
        stats['covers']+=1
        required=4*(sum(r*r for r in rows)+sum(c*c for c in cols))
        remainder=required-2*sum(k*k for k in ds)-2*sum(k*k for k in ss)
        sqs={}
        for a in extra(1,ss):
            sqs.setdefault(sum(x*x for x in a),[]).append(a)
        for b in extra(0,ds):
            for a in sqs.get(remainder-sum(x*x for x in b),[]):
                verified.add((tuple(sorted(tuple(ds)*2+b)),tuple(sorted(tuple(ss)*2+a))))
    visit(df,sf)
    return stats,sorted(verified)


if __name__=='__main__':
    doc=json.loads(gzip.decompress(Path('clipped_cert.json.gz').read_bytes()))
    start=time.process_time()
    for i,j in doc['kept']:
        stats,options=profiles(30,doc['unused'][i],doc['unused'][j])
        print(json.dumps(dict(pair=[i,j],**stats,profiles=options)),flush=True)
    import sys
    print('CPU seconds',round(time.process_time()-start,3),file=sys.stderr)
