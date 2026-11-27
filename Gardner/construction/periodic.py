"""Screen prescribed balanced periodic occupied axes; reflections and transposition quotient."""
from collections import Counter
from itertools import combinations, combinations_with_replacement
import json
from pathlib import Path
import sys
import time
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'exact'))
from axis_matching import pair_test

n=30
def masks():
    raw=set()
    for p in range(1,11):
        if n%p or p%2:
            continue
        for residues in combinations(range(p),p//2):
            raw.add(tuple(i for i in range(n) if i%p in residues))
    canonical={min(r,tuple(sorted(n-1-i for i in r))) for r in raw}
    return len(raw),sorted(canonical)

def main():
    t=time.process_time()
    raw,axes=masks()
    outcomes=[]
    hist=Counter()
    survivors=[]
    for i,j in combinations_with_replacement(range(len(axes)),2):
        r,c=axes[i],axes[j]
        res=pair_test(n,set(r),set(c))
        hist[res['reason']]+=1
        if res['reason']=='survives':
            survivors.append((i,j))
        else:
            # indexed certificate records are checked by the independent, local script
            outcomes.append([i,j,res['reason'],res['proof']])
    import gzip
    doc={'n':n,'raw_axes':raw,'axes':axes,'counts':dict(hist),
         'survivors':survivors,'rejections':outcomes}
    with gzip.GzipFile(filename='periodic-cert.json.gz',mode='wb',mtime=0) as f:
        f.write(json.dumps(doc,separators=(',',':')).encode())
    print('unreduced axes',raw,'axis representatives',len(axes),'pairs',sum(hist.values()))
    print(dict(hist),'survivors',survivors)
    print('process seconds',round(time.process_time()-t,3))
if __name__=='__main__': main()
