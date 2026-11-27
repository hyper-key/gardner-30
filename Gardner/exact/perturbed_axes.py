"""Generate short, streamed hole/matching certificates on parity-perturbed axes."""
import json
import sys
from collections import Counter
from itertools import chain, combinations_with_replacement
from pathlib import Path
from axis_matching import matching


def generate():
    even = set(range(0,30,2))
    axes = [even - {x} | {y} for x in sorted(even) for y in range(1,30,2)]
    axes.append(even)
    board = set(range(30))
    for i,j in chain(combinations_with_replacement(range(225),2), ((225,k) for k in range(225))):
        r,c = axes[i],axes[j]
        ds = Counter(x-y for x in r for y in c)
        ss = Counter(x+y for x in r for y in c)
        holes = [(x,y) for x in sorted(board-r) for y in sorted(board-c)]
        hole = next(((x,y) for x,y in holes if ds[x-y]<2 and ss[x+y]<2),None)
        if hole is not None:
            yield [30*hole[0]+hole[1]]
            continue
        m = matching((x-y,x+y) for x,y in holes)
        if len(m) > 30:
            yield [30*((s+d)//2)+(s-d)//2 for d,s in m[:31]]
        else:
            raise RuntimeError(f'unresolved axis pair {i},{j}')


if __name__=='__main__':
    import gzip
    import time
    start=time.monotonic()
    records=list(generate())
    Path(sys.argv[1]).write_bytes(gzip.compress(json.dumps(records,separators=(',',':')).encode(),
                                               compresslevel=9,mtime=0))
    print('representatives by certificate length',dict(Counter(map(len,records))),
          'wall_s',round(time.monotonic()-start,3))
