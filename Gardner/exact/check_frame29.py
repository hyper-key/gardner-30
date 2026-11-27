"""Independent local certificate verification and small-span projection audit."""
from collections import Counter
import gzip
from itertools import combinations, combinations_with_replacement, product
import json
from pathlib import Path
from check_clipped import Case


def good_mod(e,x,y):
    bad={(i-j,i+j) for i in x for j in y
         if not (((i+j)%e in x and (i+j)%e in y) or ((i-j)%e in x and (j-i)%e in y))}
    edges={(d%e,s%e) for d,s in bad}
    if not edges: return True
    d,s=next(iter(edges))
    def one(rest):
        return len({x for x,y in rest})<=1 or len({y for x,y in rest})<=1
    return one({edge for edge in edges if edge[0]!=d}) or one({edge for edge in edges if edge[1]!=s})


def small_spans(actual):
    for e in range(14,18):
        axes=[frozenset((0,)+a) for a in combinations(range(1,e),13)]
        found=set()
        for x,y in combinations_with_replacement(axes,2):
            dx=sum(x)-sum(y)
            if dx%15: continue
            if not good_mod(e,x,y):continue
            mx,my=(sum(1<<k for k in a) for a in (x,y))
            for offset in range(30-e):
                offset2=offset+dx//15
                if 0<=offset2<30-e:
                    found.add((e,mx,my,offset,offset2) if mx<=my else (e,my,mx,offset2,offset))
        assert found=={z for z in actual if z[0]==e}
        print('span',e,'direct modular projection matches',len(found),'translations')


def known_control(n,q):
    u=sorted(set(range(n))-{x for x,y in q});v=sorted(set(range(n))-{y for x,y in q})
    e=u[-1]-u[0]
    assert e==v[-1]-v[0] and sum(u)==sum(v)
    assert len(u)==len(v)==n//2
    ur={i-u[0] for i in u[:-1]};vr={i-v[0] for i in v[:-1]}
    assert good_mod(e,ur,vr)
    missing={(i,j) for (i,j) in product(ur,vr) if not (
        (i+j)%e in ur and (i+j)%e in vr or (i-j)%e in ur and (j-i)%e in vr)}
    sat=[{key for key,v in Counter(f(r,c) for r,c in q).items() if v==2}
         for f in (lambda r,c:r-c,lambda r,c:r+c)]
    border={(r,c) for r in u for c in v if r in (u[0],u[-1]) or c in (v[0],v[-1])}
    bad_d={k for k in sat[0] if sum(r-c==k for r,c in border)<2}
    bad_s={k for k in sat[1] if sum(r+c==k for r,c in border)<2}
    assert [len(keys) for keys in sat]==[n//2,n//2-1] and len(bad_d)+len(bad_s)<=2
    assert all((r+u[0]-c-v[0]) in bad_d or (r+u[0]+c+v[0]) in bad_s for r,c in missing)
    print('known',n,'bad ordinary diagonals',len(bad_d)+len(bad_s),'modular violations',len(missing))


if __name__=='__main__':
    axes=[tuple(map(int,z.split())) for z in Path('frame29_full.txt').read_text().splitlines()]
    assert len(set(axes))==len(axes)==9016
    small_spans(axes)
    known_control(6,[[1,1],[1,3],[3,1],[3,5],[5,3],[5,5]])
    for n in (10,18,26):
        known_control(n,json.loads(Path(f'../construction/witness{n}.json').read_text())['queens'])
    with gzip.open('frame29_certs.json.gz','rt') as f: records=json.load(f)
    hist=Counter()
    for (e,u,v,i,j),(kind,cert) in zip(axes,records,strict=True):
        a=[k+i for k in range(e) if (u>>k)&1]+[e+i]
        b=[k+j for k in range(e) if (v>>k)&1]+[e+j]
        assert len(a)==len(b)==15 and sum(a)==sum(b) and min(a+b)>=0 and max(a+b)<30
        case=Case(30,a,b)
        if kind=='survives':
            hist.update(case.leaves(cert))
        elif kind=='matching_after_forcing':
            ds,ss,m=cert
            assert set(ds)<=case.forced[0] and set(ss)<=case.forced[1]
            assert len(set(ds))+len(set(ss))+len(m)>30
            assert len({d for d,s in m})==len({s for d,s in m})==len(m)
            assert all(tuple(p) in case.holes and p[0] not in ds and p[1] not in ss for p in m)
        else:
            case.check_quick(kind,cert)
        hist[kind]+=1
    print('PASS every supplied pair',dict(hist))
