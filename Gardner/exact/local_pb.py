"""Independent check of exact Hamming shells by adding two PB counts."""
import argparse
import json
import time
from pathlib import Path
from model import Solver, cardinality, coords

args = argparse.ArgumentParser()
args.add_argument('source', type=Path)
args.add_argument('removed', nargs='+', type=int)
args.add_argument('--timeout-ms', type=int, default=10000)
a = args.parse_args()
data = json.loads(a.source.read_text())
n = data['n']
inside = {r*n+c for r,c in data['queens']}
assert len(inside) == len(data['queens']) and all(0 <= r < n and 0 <= c < n for r,c in data['queens'])
outside = set(range(n**2)) - inside
for d in a.removed:
    start = time.monotonic()
    s = Solver(n, timeout_ms=a.timeout_ms)
    for index_set, count in ((inside, len(inside)-d), (outside, d-1)):
        vs = [f'q{i}' for i in sorted(index_set)]
        for op in ('at-most','at-least'):
            s.send('(assert ' + cardinality(op,count,vs) + ')')
    status = s.query('(check-sat)')
    obj = dict(n=n, base=len(inside), removed=d, added=d-1, timeout_ms=a.timeout_ms, seed=0, status=status)
    if status == 'sat':
        obj['queens'] = coords(n,s.witness())
    elif status == 'unknown':
        obj['reason'] = s.query('(get-info :reason-unknown)')
    s.close()
    obj['wall_s'] = round(time.monotonic() - start, 3)
    print(json.dumps(obj), flush=True)
