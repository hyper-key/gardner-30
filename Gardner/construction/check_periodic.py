"""Validate each stored rejection without importing the axis screen or a matching algorithm."""
import gzip
from itertools import combinations_with_replacement
import json
import sys

def axes():
    choices=set()
    for p in (1,2,3,5,6,10):
        for mask in range(1<<p):
            x=tuple(i for i in range(30) if (mask>>(i%p))&1)
            if len(x)==15:
                reversed_x=tuple(29-i for i in reversed(x))
                choices.add(min(x,reversed_x))
    return sorted(choices)

def verify(data):
    assert data['n']==30 and data['raw_axes']==270
    ax=axes()
    assert [list(x) for x in ax]==data['axes']
    allpairs=set(combinations_with_replacement(range(len(ax)),2))
    evens=tuple(range(0,30,2)); checker=(ax.index(evens),ax.index(evens))
    assert data['survivors']==[list(checker)]
    allpairs.remove(checker)
    for i,j,reason,proof in data['rejections']:
        assert (i,j) in allpairs
        allpairs.remove((i,j))
        r,c=set(ax[i]),set(ax[j])
        def unsafe(d,s):
            a,b=divmod(s+d,2),divmod(s-d,2)
            return (a[1]==b[1]==0 and 0<=a[0]<30 and 0<=b[0]<30
                    and a[0] not in r and b[0] not in c)
        def sites(d=None,s=None):
            if d is not None:
                return sum(a-d in c for a in r)
            return sum(s-a in c for a in r)
        if reason=='matching':
            assert len(proof)>30
            ds,ss=zip(*proof)
            assert len(set(ds))==len(set(ss))==len(proof)
            assert all(unsafe(*edge) for edge in proof)
        elif reason=='uncoverable':
            d,s=proof
            assert unsafe(d,s) and sites(d=d)<2 and sites(s=s)<2
        elif reason=='forced_lane_capacity':
            df,sf=map(set,proof)
            assert max(len(df),len(sf))>15
            for d in df:
                assert any(unsafe(d,s) and sites(s=s)<2 for s in range(59))
            for s in sf:
                assert any(unsafe(d,s) and sites(d=d)<2 for d in range(-29,30))
        else:
            raise AssertionError(reason)
    assert not allpairs

if __name__=='__main__':
    path=sys.argv[1] if len(sys.argv)>1 else 'periodic-cert.json.gz'
    with gzip.open(path,'rt') as f: doc=json.load(f)
    verify(doc)
    print('PASS 135 masks, 9179 rejected representatives, survivor exactly (even,even)')
    doc['rejections'][0][3]=[]
    try: verify(doc)
    except (ValueError,AssertionError): pass
    else: raise AssertionError('accepted damaged first rejection')
    print('PASS damaged rejection rejected')
