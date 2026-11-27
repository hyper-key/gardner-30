"""Enumerate projected SMT models and compare the TWO SETS for exact equality."""
from collections import Counter
import hashlib
import json
import time
from model import Solver
from oracle import placements


def run(n):
    t = time.monotonic()
    expected = placements(n)
    seen = set()
    s = Solver(n)
    while True:
        result = s.query('(check-sat)')
        if result == 'unsat':
            break
        if result != 'sat':
            raise RuntimeError(result)
        m = s.witness()
        assert m in expected and m not in seen, m
        seen.add(m)
        s.exclude(m)
    s.close()
    assert seen == expected, sorted(expected - seen)[:5]
    return dict(n=n, subsets=2 ** (n*n), projected=len(seen),
                counts=dict(sorted(Counter(m.bit_count() for m in seen).items())),
                sha256=hashlib.sha256(' '.join(map(str, sorted(seen))).encode()).hexdigest(),
                wall_s=round(time.monotonic() - t, 3))


if __name__ == '__main__':
    for n in range(1, 5):
        print(json.dumps(run(n)), flush=True)
