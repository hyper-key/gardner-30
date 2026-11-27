"""Independently check radius-1 and radius-2 deletion certificates.

No imports from witness verifier, SMT encoding or neighborhood solver.
"""
from itertools import combinations, product
import json
import sys


def check(cert):
    n = cert['seed']['n']
    points = [tuple(x) for x in cert['seed']['queens']]
    seed = set(points)
    assert len(seed) == len(points) == 31 and n == 30
    assert all(len(p)==2 and all(type(x) is int and 0 <= x < n for x in p) for p in points)
    board = set(product(range(n),repeat=2))
    def queen_dir(p,q):
        dx,dy = p[0]-q[0],p[1]-q[1]
        if dx == 0: return (0,1)
        if dy == 0: return (1,0)
        if dx == dy: return (1,1)
        if dx == -dy: return (1,-1)
        return None
    def triple(p,q,x):
        v = queen_dir(p,q)
        return v is not None and (p[0]-x[0])*v[1] == (p[1]-x[1])*v[0]
    assert len(cert['holes']) == 496
    proof = iter(cert['holes'])
    # For every pair of seed queens store only geometric triples they would
    # produce with a third point. Validity and candidate domains follow directly.
    attacked = {pair: {x for x in board if x not in pair and triple(*pair,x)}
                for pair in combinations(sorted(seed),2)}
    assert all(not (seed & a) for a in attacked.values())
    assert set.union(set(seed),*attacked.values()) == board
    for d in (1,2):
        for removed in combinations(sorted(seed),d):
            keep = seed - set(removed)
            blocked = set.union(set(keep),*(v for pair,v in attacked.items() if set(pair)<=keep))
            free = board - blocked
            hole_ids = next(proof)
            assert all(type(k) is int and 0 <= k < n*n for k in hole_ids)
            holes = [divmod(k,n) for k in hole_ids]
            assert set(holes) <= free
            if d == 1:
                assert holes
            else:
                for candidate in free - seed:
                    # Show at least one listed distinct free square remains
                    # addable after the proposed sole outside queen is inserted.
                    assert any(h != candidate and all(not triple(candidate,q,h) for q in keep)
                               for h in holes)
    assert next(proof,None) is None


if __name__ == '__main__':
    with open(sys.argv[1]) as fp:
        cert = json.load(fp)
    check(cert)
    assert len(cert['holes']) == 496
    # Remove the required singleton-shell hole and demand rejection.
    cert['holes'][0] = []
    try:
        check(cert)
    except AssertionError:
        pass
    else:
        raise AssertionError('accepted a corrupted proof')
    print('PASS: seed, 31 singleton and 465 double-deletion cases. Corrupted certificate rejected.')
