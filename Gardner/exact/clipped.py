"""Enumerate clipped periodic unused axes and screen the Cartesian product."""
import gzip
from collections import Counter
from itertools import combinations_with_replacement
import json
from pathlib import Path
import time
from axis_matching import pair_test


def axes(n, pmax):
    raw=set()
    for p in range(1,pmax+1):
        for word in range(1,1<<p):
            filled=[k for k in range(n) if word>>(k%p)&1]
            # Any interval clipping to exactly n/2 points yields a consecutive
            # length-n/2 slice of this list, and every such slice is obtainable.
            raw.update(tuple(filled[a:a+n//2]) for a in range(len(filled)-n//2+1))
    return len(raw), sorted({min(x,tuple(n-1-i for i in reversed(x))) for x in raw})


if __name__=='__main__':
    start=time.process_time()
    n=30
    raw,unused=axes(n,5)
    rejects=[]
    kept=[]
    hist=Counter()
    for i,j in combinations_with_replacement(range(len(unused)),2):
        rows,cols=(set(range(n))-set(unused[k]) for k in (i,j))
        q=pair_test(n,rows,cols)
        hist[q['reason']]+=1
        if q['reason']=='survives':
            kept.append([i,j])
        else:
            rejects.append([i,j,q['reason'],q['proof']])
    doc=dict(n=n,pmax=5,raw=raw,unused=unused,kept=kept,rejects=rejects)
    Path('clipped_cert.json.gz').write_bytes(gzip.compress(json.dumps(doc,separators=(',',':')).encode(),
                                                            compresslevel=9,mtime=0))
    print(json.dumps(dict(n=n,pmax=5,raw=raw,representatives=len(unused),
                          pairs=sum(hist.values()),counts=hist,kept=kept,
                          cpu_s=round(time.process_time()-start,3))))
