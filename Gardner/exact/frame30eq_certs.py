"""Encode local rejection and cover trees for every reported translated axis."""
from pathlib import Path
import gzip
import json
from axis_matching import pair_test
from clipped_proof import tree

records=[]
for line in Path('frame30eq_full.txt').read_text().splitlines():
    e,u,v,i,j=map(int,line.split())
    a={i+k for k in range(e) if u>>k&1}|{i+e}
    b={j+k for k in range(e) if v>>k&1}|{j+e}
    r=pair_test(30,set(range(30))-a,set(range(30))-b)
    kind=r['reason']
    proof=tree(30,a,b) if kind=='survives' else r['proof']
    records.append([kind,proof])
Path('frame30eq_certs.json.gz').write_bytes(gzip.compress(json.dumps(records,separators=(',',':')).encode(),
                                                       compresslevel=9,mtime=0))
