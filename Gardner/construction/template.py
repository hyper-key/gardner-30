"""Construct monochromatic candidates by selecting diagonal covers, then filling lines using Z3."""
import argparse
import itertools
import json
import re
import subprocess
import time
from pathlib import Path

def minimal_covers(m, hole=None):
    cells = [(i-j, i+j+1) for i in range(m) for j in range(m) if (i,j) != hole]
    by_parity = []
    for parity in range(2):
        neighbors = {d: {u for e,u in cells if e == d}
                     for d,_ in cells if d%2 == parity}
        # All possible unions of neighborhoods of unselected difference lines.
        unions = {frozenset()}
        for cols in neighbors.values():
            unions |= {u | cols for u in unions}
        by_parity.append([(frozenset(d for d, cols in neighbors.items()
                                     if not cols <= u), u) for u in unions])
    for (d0,s0),(d1,s1) in itertools.product(*by_parity):
        d,s = d0 | d1, s0 | s1
        if len(d) <= m and len(s) <= m:
            yield d,s

def smt(m, hole, need_d, need_s, symmetric):
    variables = {}
    diag = {}
    lines = ['(set-logic ALL)']
    q = lambda i,j: f'x{i}_{j}'
    for i,j in itertools.product(range(m),repeat=2):
        variables[i,j] = q(*sorted((i,j))) if symmetric else q(i,j)
    lines += [f'(declare-const {v} Bool)' for v in sorted(set(variables.values()))]
    def card(v, k, op):
        if k < 0 or (op=='at-least' and k>len(v)):
            return '(assert false)'
        if (op=='at-most' and k>=len(v)) or (op=='at-least' and k==0):
            return '(assert true)'
        return f"(assert ((_ {op} {k}) {' '.join(v)}))"
    def emit(v,lo,hi):
        lines.extend([card(v,lo,'at-least'),card(v,hi,'at-most')])
    for i in range(m):
        emit([variables[i,j] for j in range(m)],2,2)
        if not symmetric:
            emit([variables[j,i] for j in range(m)],2,2)
    for proj,req,extra in [(lambda i,j: i-j,need_d,hole[0]-hole[1]),
                           (lambda i,j: i+j,need_s,hole[0]+hole[1]+1)]:
        for key in sorted({proj(i,j) for i,j in variables} | {extra} | req):
            v = [x for (i,j),x in variables.items() if proj(i,j)==key]
            hi=2-int(key==extra)
            emit(v, hi if key in req else 0, hi)
    lines += ['(check-sat)', "(get-value ("+' '.join(sorted(set(variables.values())))+'))']
    return '\n'.join(lines), variables

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--m',type=int,default=15)
    p.add_argument('--ms',type=int,default=250)
    p.add_argument('--attempts',type=int,default=400)
    p.add_argument('--seed',type=int,default=148)
    p.add_argument('--general',action='store_true')
    p.add_argument('--out',required=True)
    a=p.parse_args()
    import random
    rng=random.Random(a.seed)
    started=time.monotonic()
    specs=[]
    for i in range(a.m):
        for j in range(i+1):
            h=i,j
            for d,s in minimal_covers(a.m,h):
                # For reflection-transpose symmetry of the even block, its
                # difference counts must agree at k and -k. A required line
                # with an odd queen only needs one even queen.
                if not a.general:
                    if len(d | {-x for x in d}) > a.m+1:
                        continue
                    if any(abs(k)==a.m-1 and k!=i-j for k in d):
                        continue
                if any(k in (0,2*a.m-2,2*a.m-1) and k!=i+j+1 for k in s):
                    continue
                specs.append((h,d,s))
    rng.shuffle(specs)
    print('templates-with-holes',len(specs),flush=True)
    counts={}
    for trial,(hole,d,s) in enumerate(specs[:a.attempts]):
        data,x=smt(a.m,hole,d,s,not a.general)
        output=subprocess.run(['z3','-in'], text=True, input=f'(set-option :timeout {a.ms})\n'+data,capture_output=True).stdout
        result=output.splitlines()[0]
        counts[result]=counts.get(result,0)+1
        if result=='sat':
            model=dict(re.findall(r'\((x\d+_\d+) (true|false)\)',output))
            pts=sorted([(2*i,2*j) for (i,j),v in x.items() if model[v]=='true']+
                       [(2*hole[0]+1,2*hole[1]+1)])
            Path(a.out).write_text(json.dumps({'n':2*a.m,'queens':pts})+'\n')
            print('trial',trial,'hole',hole,'D',sorted(d),'S',sorted(s))
            break
    print('responses',counts,'elapsed',round(time.monotonic()-started,3),flush=True)
if __name__=='__main__':
    main()
