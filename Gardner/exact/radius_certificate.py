"""Create compact hole certificates for the first two deletion shells."""
from itertools import combinations
import json
from pathlib import Path
import sys
from repair import Repair, indices

source = Path(sys.argv[1])
s = json.loads(source.read_text())
q = Repair(s['n'],s['queens'])
proof = []
for d in (1,2):
    for removed in combinations(q.cells,d):
        occ = q.seed ^ sum(1<<i for i in removed)
        free = q.full ^ occ
        for line in q.lines:
            if (line & occ).bit_count() == 2:
                free &= ~line
        if d == 1:
            assert free
            proof.append([next(indices(free))])
            continue
        candidates = free & ~q.seed
        core = []
        # If just one new queen can be chosen, it must resolve ALL of these
        # holes, each by occupying it or joining an already singly occupied line.
        while candidates:
            best = None
            for i in indices(free):
                resolves = 1<<i
                for k in q.inc[i]:
                    if q.lines[k] & occ:
                        resolves |= q.lines[k]
                left = candidates & resolves
                key = (left.bit_count(), i, left)
                if best is None or key < best:
                    best = key
            assert best is not None and best[0] < candidates.bit_count()
            candidates = best[2]
            core.append(best[1])
        proof.append(core)
print(json.dumps(dict(seed=s,holes=proof),separators=(',',':')))
