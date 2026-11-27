"""Generate evidence for consecutive occupied axes; one representative per D4 orbit."""
import json
from collections import Counter
from itertools import product

cases = []
for i in range(8):
    for j in range(i,8):
        rows, cols = set(range(i,i+15)), set(range(j,j+15))
        active = list(product(sorted(rows),sorted(cols)))
        holes = list(product(sorted(set(range(30))-rows),sorted(set(range(30))-cols)))
        ds, ss = Counter(r-c for r,c in active),Counter(r+c for r,c in active)
        impossible = [(r,c) for r,c in holes if ds[r-c]<2 and ss[r+c]<2]
        force_d = {r-c:(r,c) for r,c in holes if ss[r+c]<2}
        force_s = {r+c:(r,c) for r,c in holes if ds[r-c]<2}
        if impossible:
            reason, pts = 'hole', impossible[:1]
        elif len(force_d)>15:
            reason, pts = 'force_d', list(force_d.values())[:16]
        elif len(force_s)>15:
            reason, pts = 'force_s', list(force_s.values())[:16]
        else:
            reason, pts = 'moment', [list(force_d.values()),list(force_s.values())]
        cases.append([i,j,reason,pts])
print(json.dumps(cases,separators=(',',':')))
