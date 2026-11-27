"""Verify a finite mathematical exclusion of all 256 consecutive-axis pairs."""
import json
import sys
from collections import Counter
from itertools import product


def check(records):
    # Reflections send a start i to 15-i; transpose interchanges starts.
    needed = {tuple(sorted((min(i,15-i),min(j,15-j))))
              for i,j in product(range(16),repeat=2)}
    assert len(records)==len(needed)==36
    hist = Counter()
    for i,j,kind,raw in records:
        assert (i,j) in needed
        needed.remove((i,j))
        def support(k, sign):
            # Each active row intersects the diagonal in at most one active
            # column, c = r-k for a difference or c = k-r for a sum.
            return sum(j <= sign*(r-k) < j+15 for r in range(i,i+15))
        def keys(points, use_diff):
            result = set()
            for r,c in points:
                assert 0<=r<30 and 0<=c<30
                assert r not in range(i,i+15) and c not in range(j,j+15)
                d,s = r-c,r+c
                if use_diff:
                    assert support(s,-1)<2
                    result.add(d)
                else:
                    assert support(d,1)<2
                    result.add(s)
            return result
        if kind == 'hole':
            assert len(raw)==1 and len(keys(raw,True))==len(keys(raw,False))==1
        elif kind in ('force_d','force_s'):
            assert len(keys(raw,kind=='force_d'))>=16
        elif kind == 'moment':
            ds,ss = keys(raw[0],True),keys(raw[1],False)
            assert len(ds)<=15 and len(ss)<=15
            # Centered absolute diagonal keys of any queen in this 15x15 box
            # are at most 14. Every forced key has exactly two queens.
            bound = (2*sum((d-(i-j))**2 for d in ds)
                     +2*sum((s-(i+j+14))**2 for s in ss)
                     +(60-2*(len(ds)+len(ss)))*14**2)
            required = 8 * sum(x*x for x in range(-7,8))
            assert bound<required
            print('moment bound',i,j,bound,'<',required)
        else:
            raise ValueError(kind)
        hist[kind] += 1
    assert not needed
    return hist

if __name__=='__main__':
    with open(sys.argv[1]) as fp:
        c = json.load(fp)
    print('PASS representative interval pairs',dict(check(c)))
    c.pop()
    try:
        check(c)
    except AssertionError:
        print('PASS missing orbit rejected')
    else:
        raise AssertionError('missing orbit accepted')
