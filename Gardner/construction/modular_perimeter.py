"""Evaluate modular candidates against exact-once perimeter, supports, coverage and moments."""
from collections import Counter,defaultdict
import itertools
import json
from pathlib import Path

def bits(mask):
    return [i for i in range(mask.bit_length()) if mask>>i&1]

def search(e,ma,mb,ta,tb):
    ur={t+ta for t in bits(ma)+[e]}; uc={t+tb for t in bits(mb)+[e]}
    assert len(ur)==len(uc)==15 and sum(ur)==sum(uc)==225
    ar=set(range(30))-ur; ac=set(range(30))-uc
    square=set(itertools.product(ur,uc))
    border={p for p in square if p[0] in (min(ur),max(ur)) or p[1] in (min(uc),max(uc))}
    assert len(border)==56
    slots=dict()
    available=Counter()
    for r,c in itertools.product(ar,ac):
        for k in [(0,r-c),(1,r+c)]:
            available[k]+=1
    for r,c in border:
        for k in [(0,r-c),(1,r+c)]:
            slots.setdefault(k,set()).add((r,c))
    choices={k:v for k,v in slots.items() if len(v)==2 and available[k]>=2}
    edges={p:[k for k,v in choices.items() if p in v] for p in border}
    hist=Counter()
    marginal=[]
    def check(mask,selected):
        if mask:
            opts=lambda p:[k for k in edges[p] if choices[k]<=mask]
            p=min(mask,key=lambda p:(len(opts(p)),p))
            for k in opts(p):
                check(mask-choices[k],selected+[k])
            return
        hist['perfect']+=1
        D={z for f,z in selected if f==0}
        S={z for f,z in selected if f==1}
        if (len(D),len(S))!=(15,13):
            return
        hist['split']+=1
        if any(r-c not in D and r+c not in S for r,c in square):
            return
        hist['cover']+=1
        if sum(D)!=sum(ar)-sum(ac):
            return
        hist['firstD']+=1
        need=2*(sum(ar)+sum(ac)-sum(S))
        m2=4*(sum(r*r for r in ar)+sum(c*c for c in ac))-2*sum(z*z for z in D)-2*sum(z*z for z in S)
        # The four queens outside the 13 paired sum lines have distinct sums.
        # Difference lines are fully specified, further restricting sum support.
        poss={r+c for r,c in itertools.product(ar,ac) if r-c in D and r+c not in S}
        poss=sorted(poss)
        for a,b,c in itertools.combinations(poss,3):
            d=need-a-b-c
            if d<=c or d not in poss or a*a+b*b+c*c+d*d!=m2: continue
            hist['marginals']+=1
            marginal.append((sorted(D),sorted(S),[a,b,c,d]))
    check(border,[])
    return hist,marginal

if __name__=='__main__':
    data=[]; totals=Counter()
    for line in Path('modular-pairs.txt').read_text().splitlines():
        key=tuple(map(int,line.split()))
        hist,m=search(*key)
        totals.update(hist)
        data.append({'axis':key,'statistics':dict(hist),'profiles':m})
    Path('modular-perimeter.json').write_text(json.dumps(data,separators=(',',':'))+'\n')
    print('inputs',len(data),'totals',dict(totals),'pairs-with-final-profile',sum(bool(x['profiles']) for x in data))
