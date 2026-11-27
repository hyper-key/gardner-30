"""Serialize each existing axis/certificate pair as one JSON line; no verdict logic."""
import argparse
import gzip
import json
from pathlib import Path

p=argparse.ArgumentParser()
p.add_argument('--sample',action='store_true',help='first two of each rejection type per branch')
p.add_argument('--damaged',action='store_true',help='replace a cover-tree root with an invalid quota leaf')
a=p.parse_args()
for family,prefix in ((29,'frame29'),(30,'frame30eq')):
    axes=Path(prefix+'_full.txt').read_text().splitlines()
    with gzip.open(prefix+'_certs.json.gz','rt') as f:
        data=json.load(f)
    seen={}
    for line,(kind,proof) in zip(axes,data,strict=True):
        if a.damaged and kind!='survives':continue
        if a.sample and seen.get(kind,0)>=2:continue
        seen[kind]=seen.get(kind,0)+1
        record=[family,*map(int,line.split()),kind,'Q' if a.damaged else proof]
        print(json.dumps(record,separators=(',',':')))
        if a.damaged:raise SystemExit(0)
