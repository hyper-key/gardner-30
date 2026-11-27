"""Refine a diagonal cover to occupancy profiles using first and second moments."""
from collections import Counter, defaultdict
import itertools
import json
import random
import re
import subprocess
import time
from pathlib import Path
from template import minimal_covers

def profile_options(m, need, extra, issum):
    center = m-1 if issum else 0
    base = Counter({k:2-int(k==extra) for k in need})
    count = 2*m-sum(base.values())
    target = 2*m*center-sum(k*v for k,v in base.items())
    choices = [k for k in range(center-m+1, center+m)
               if k not in need]
    if any(cnt > m-abs(k-center) for k,cnt in base.items()):
        return {}
    result = defaultdict(list)
    def rec(i, rest, total, values):
        if not rest:
            if total==0:
                profile=base.copy()
                profile.update(values)
                moment = sum((k-center)**2*v for k,v in profile.items())
                result[moment].append(profile)
            return
        if not choices or i>=len(choices) or not choices[i]*rest<=total<=choices[-1]*rest:
            return
        for t in range(i,len(choices)):
            k=choices[t]
            if k*rest>total:
                break
            cap=min(2-int(k==extra),m-abs(k-center))
            for mult in range(1,min(cap,rest)+1):
                rec(t+1,rest-mult,total-k*mult,values+[k]*mult)
    rec(0,count,target,[])
    return result

def make(m,hole,d,s,symmetric):
    pts = {(i,j): 'x%d_%d'%(tuple(sorted((i,j))) if symmetric else (i,j))
           for i,j in itertools.product(range(m),repeat=2) if d[i-j] and s[i+j]}
    lines = ['(set-logic ALL)']
    lines += [f'(declare-const {v} Bool)' for v in sorted(set(pts.values()))]
    for key,req in [(lambda i,j:i, {v:2 for v in range(m)}),
                    (lambda i,j:j, {v:2 for v in range(m)}),
                    (lambda i,j:i-j, d), (lambda i,j:i+j, s)]:
        for k,g in sorted(req.items()):
            vs=[v for (i,j),v in pts.items() if key(i,j)==k]
            if len(vs)<g: return None, {}
            for cond in ('at-least','at-most'):
                lines.append(f"(assert ((_ {cond} {g}) {' '.join(vs)}))")
    lines += ['(check-sat)', '(get-value ('+' '.join(sorted(set(pts.values())))+'))']
    return '\n'.join(lines),pts

def main():
    import argparse
    p=argparse.ArgumentParser()
    p.add_argument('--m',type=int,default=15)
    p.add_argument('--seed',type=int,default=111)
    p.add_argument('--ms',type=int,default=300)
    p.add_argument('--attempts',type=int,default=200)
    p.add_argument('--out',default='witness31.json')
    p.add_argument('--even-only',action='store_true',help='seek 2m queens on board 2m')
    a=p.parse_args()
    start=time.monotonic()
    m=a.m
    # Sum((i-j)^2+(i+j-(m-1))^2) over 2m points, with 2 per row/col.
    target=2*m*(m*m-1)//3
    holes=[None] if a.even_only else [(i,j) for i in range(m) for j in range(i+1)]
    rng=random.Random(a.seed)
    rng.shuffle(holes)
    stats=Counter()
    for hole in holes:
        d0=hole[0]-hole[1] if hole else 10**6
        s0=hole[0]+hole[1]+1 if hole else 10**6
        tasks=[]
        for needed_d,needed_s in minimal_covers(m,hole):
            D=profile_options(m,needed_d,d0,False)
            S=profile_options(m,needed_s,s0,True)
            for moment,dl in D.items():
                for d,s in itertools.product(dl,S.get(target-moment,[])):
                    tasks.append((d,s))
        rng.shuffle(tasks)
        stats['holes']+=1
        stats['moment_matches']+=len(tasks)
        for d,s in tasks:
            for sym in ([True,False] if all(d[k]==d[-k] for k in d) else [False]):
                data,x=make(m,hole,d,s,sym)
                if data is None:
                    stats['no-capacity']+=1
                    continue
                output=subprocess.run(['z3','-in'], text=True, input=f'(set-option :timeout {a.ms})\n'+data,capture_output=True).stdout
                result=output.splitlines()[0]
                stats[result]+=1
                if result=='sat':
                    model=dict(re.findall(r'\((x\d+_\d+) (true|false)\)',output))
                    pts=sorted([(2*i,2*j) for (i,j),v in x.items() if model[v]=='true']+
                               ([(2*hole[0]+1,2*hole[1]+1)] if hole else []))
                    Path(a.out).write_text(json.dumps({'n':2*m,'queens':pts})+'\n')
                    print('hole',hole,'even symmetric',sym,'D',sorted(d.elements()),'S',sorted(s.elements()))
                    print('counts',dict(stats),'elapsed',round(time.monotonic()-start,3))
                    return
                if sum(stats[v] for v in ('sat','unsat','unknown'))>=a.attempts:
                    print('counts',dict(stats),'elapsed',round(time.monotonic()-start,3))
                    return
    print('counts',dict(stats),'elapsed',round(time.monotonic()-start,3))
if __name__=='__main__':
    main()
