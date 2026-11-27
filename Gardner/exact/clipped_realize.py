"""Realize a fixed pair of axes with just |R|*|C| square variables."""
import argparse
from collections import defaultdict
import gzip
from itertools import product
import json
from pathlib import Path
import re
import subprocess
import time
from model import cardinality


def realize(n,unused_r,unused_c,limit):
    rows,cols=(sorted(set(range(n))-set(a)) for a in (unused_r,unused_c))
    pts=list(product(rows,cols))
    by=[defaultdict(list) for _ in range(4)]
    text=[f'(set-option :timeout {limit})','(set-option :smt.random_seed 0)',
          '(set-option :sat.random_seed 0)']
    for k,(r,c) in enumerate(pts):
        name=f'q{k}'
        text.append(f'(declare-fun {name} () Bool)')
        for axis,key in enumerate([r,c,r-c,r+c]):
            by[axis][key].append(name)
    for family in by[:2]:
        for vs in family.values():
            for op in ('at-least','at-most'):
                text.append(f'(assert {cardinality(op,2,vs)})')
    sat={}
    for axis in (2,3):
        for key,vs in by[axis].items():
            tag=f's{len(sat)}'
            sat[axis,key]=tag
            text.append(f"(assert {cardinality('at-most',2,vs)})")
            text.append(f"(define-fun {tag} () Bool {cardinality('at-least',2,vs)})")
    for r,c in product(unused_r,unused_c):
        d=sat.get((2,r-c),'false')
        s=sat.get((3,r+c),'false')
        text.append(f'(assert (or {d} {s}))')
    text.append('(check-sat)')
    start=time.monotonic()
    p=subprocess.Popen(['z3','-in','-smt2'],stdin=subprocess.PIPE,stdout=subprocess.PIPE,text=True)
    p.stdin.write('\n'.join(text)+'\n')
    p.stdin.flush()
    status=p.stdout.readline().strip()
    assert status in ('sat','unsat','unknown'),status
    obj=dict(n=n,status=status,ms=limit)
    if status=='sat':
        names=' '.join(f'q{k}' for k in range(len(pts)))
        out=p.communicate(f'(get-value ({names}))\n(exit)\n')[0]
        parsed=re.findall(r'\(q(\d+) (true|false)\)',out)
        assert sorted(int(i) for i,_ in parsed)==list(range(len(pts)))
        obj['queens']=[list(pts[int(i)]) for i,v in parsed if v=='true']
    else:
        p.communicate('(exit)\n')
    assert p.returncode==0
    obj['wall_s']=round(time.monotonic()-start,3)
    return obj


if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--ms',type=int,default=350)
    ap.add_argument('--retry',type=Path)
    args=ap.parse_args()
    seed12=json.loads(Path('../construction/witness12.json').read_text())
    unused12=sorted(set(range(12))-{r for r,c in seed12['queens']})
    assert unused12==sorted(set(range(12))-{c for r,c in seed12['queens']})==[2,3,5,6,8,9]
    control=realize(12,unused12,unused12,1000)
    assert control['status']=='sat'
    print(json.dumps(dict(label='12-control',**control)),flush=True)
    doc=json.loads(gzip.decompress(Path('clipped_cert.json.gz').read_bytes()))
    pairs=doc['kept']
    if args.retry:
        records=[json.loads(z) for z in args.retry.read_text().splitlines()]
        pairs=[r['pair'] for r in records if r.get('pair') and r['status']=='unknown']
    for i,j in pairs:
        a,b=doc['unused'][i],doc['unused'][j]
        obj=realize(30,a,b,args.ms)
        print(json.dumps(dict(pair=[i,j],**obj)),flush=True)
