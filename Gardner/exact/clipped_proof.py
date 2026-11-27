"""Produce finite cover-split proof trees for the survivors of clipped.py."""
from collections import Counter
import gzip
import json
from pathlib import Path


def tree(n,ur,uc):
    r=set(range(n))-set(ur); c=set(range(n))-set(uc)
    ac=[Counter(x-y for x in r for y in c),Counter(x+y for x in r for y in c)]
    holes={(x-y,x+y) for x in ur for y in uc}
    df={d for d,s in holes if ac[1][s]<2}
    sf={s for d,s in holes if ac[0][d]<2}
    def prove(ds,ss):
        if max(len(ds),len(ss))>n//2: return 'Q'
        remaining=[e for e in holes if e[0] not in ds and e[1] not in ss]
        if not remaining: return 'M'
        deg=Counter((f,e[f]) for e in remaining for f in (0,1))
        f,k=max(deg,key=lambda a:(deg[a],a))
        neighbors={e[1-f] for e in remaining if e[f]==k}
        if f==0:
            return [f,k,prove(ds|{k},ss),prove(ds,ss|neighbors)]
        return [f,k,prove(ds,ss|{k}),prove(ds|neighbors,ss)]
    return prove(df,sf)


if __name__=='__main__':
    with gzip.open('clipped_cert.json.gz','rt') as f: doc=json.load(f)
    proofs=[[i,j,tree(30,doc['unused'][i],doc['unused'][j])] for i,j in doc['kept']]
    Path('clipped_trees.json.gz').write_bytes(gzip.compress(json.dumps(proofs,separators=(',',':')).encode(),
                                                           compresslevel=9,mtime=0))
