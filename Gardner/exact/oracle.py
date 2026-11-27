"""Independent direct geometric forbidden triples and insertion test. No model import."""
from itertools import combinations


def forbidden(n):
    triples = []
    for i, j, k in combinations(range(n * n), 3):
        a, b = divmod(i, n)
        c, d = divmod(j, n)
        e, f = divmod(k, n)
        x, y = c - a, d - b
        if (x == 0 or y == 0 or abs(x) == abs(y)) and x * (f - b) == y * (e - a):
            triples.append((1 << i) | (1 << j) | (1 << k))
    return triples


def placements(n):
    ts = forbidden(n)
    full = (1 << (n*n)) - 1
    # Precompute validity of every bit pattern with geometric triples.
    valid = bytearray(not any(m & t == t for t in ts) for m in range(full + 1))
    result = set()
    for m in range(full + 1):
        if not valid[m]:
            continue
        empty = full ^ m
        while empty:
            bit = empty & -empty
            if valid[m | bit]:
                break
            empty ^= bit
        else:
            result.add(m)
    return result
