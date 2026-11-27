"""Verify each obstruction using only its data, the original board, and 15+13 quotas."""
from collections import Counter
import json
from pathlib import Path

def check(keys,doc):
    assert keys==[row[0] for row in doc]
    outcomes=Counter()
    for key,(typ,data) in doc:
        e,mask_a,mask_b,base_a,base_b=map(int,key.split())
        r,c=[sorted(t+u for u in range(e+1) if mask>>(u%e)&1)
             for t,mask in ((base_a,mask_a),(base_b,mask_b))]
        assert len(r)==len(c)==15 and sum(r)==sum(c)==225
        assert sorted(r+c)[0]>=0 and sorted(r+c)[-1]<30
        def cell(d,s):
            assert (s+d)%2==(s-d)%2==0 and (s+d)//2 in r and (s-d)//2 in c
        def potential(d=None,s=None):
            return sum(1 for i in range(30) if i not in r
                       for j in range(30) if j not in c and (i-j==d or i+j==s))
        if typ=='29-lines':
            assert len(data)==len({d for d,s in data})==len({s for d,s in data})==29
            for d,s in data: cell(d,s)
        elif typ=='bad-cell':
            d,s=data
            cell(d,s)
            assert potential(d=d)<2 and potential(s=s)<2
        elif typ=='forced-sums':
            assert len({s for d,s in data})>=14
            for d,s in data:
                cell(d,s)
                assert potential(d=d)<2
        elif typ=='monochrome':
            assert r==c==list(range(1,30,2))
        else: raise ValueError(typ)
        outcomes[typ]+=1
    return outcomes

if __name__=='__main__':
    keys=Path('modular-pairs.txt').read_text().splitlines()
    doc=json.loads(Path('modular-certificate.json').read_text())
    print('PASS',dict(check(keys,doc)))
    bad=next(d for _,(typ,d) in doc if typ=='29-lines')
    bad[0]=bad[1]
    try: check(keys,doc)
    except AssertionError: pass
    else: raise AssertionError('accepted duplicate matching edge')
    print('PASS rejected duplicate edge')
