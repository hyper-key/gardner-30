"""Independent verifier for the 25,650 parity-perturbation orbit certificates."""
from itertools import chain, combinations_with_replacement
from collections import Counter
import gzip
import json
import sys


def verify(data):
    # Reflection in that axis changes majority parity, so choose the even
    # majority in each axis. Transposition allows sorting the canonical axes.
    axes = []
    for even_out in range(0,30,2):
        for odd_in in range(1,30,2):
            axes.append(tuple(k for k in range(30) if (k%2==0 and k!=even_out) or k==odd_in))
    original=tuple(range(0,30,2))
    assert len(data)==225*226//2+225
    hist = Counter()
    for pts,(rows,cols) in zip(data,chain(combinations_with_replacement(axes,2), ((original,a) for a in axes)),strict=True):
        holes = [divmod(x,30) for x in pts]
        assert all(0<=r<30 and 0<=c<30 and r not in rows and c not in cols for r,c in holes)
        if len(holes)==1:
            (r,c), = holes
            assert sum(c+(u-r) in cols for u in rows)<2
            assert sum(c-(u-r) in cols for u in rows)<2
        elif len(holes)==31:
            assert len({r-c for r,c in holes})==len({r+c for r,c in holes})==31
        else:
            raise AssertionError('bad certificate length')
        hist[len(holes)] += 1
    return hist


if __name__=='__main__':
    data=json.loads(gzip.decompress(open(sys.argv[1],'rb').read()))
    print('verified 204300 oriented axis pairs; representatives by certificate length',dict(verify(data)))
    data[0]=[]
    try:
        verify(data)
    except AssertionError:
        print('PASS corrupted case rejected')
    else:
        raise AssertionError('accepted corruption')
