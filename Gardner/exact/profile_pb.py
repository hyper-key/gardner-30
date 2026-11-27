"""Conditional structure cuts ONLY at n=k=30; use --emit for portable artifacts."""
import argparse
import collections
import json
import time
from model import Solver, cardinality, coords, lines, model


def cuts(refined=False):
    n = 30
    families = collections.defaultdict(list)
    for r in range(n):
        for c in range(n):
            for f, j in enumerate((r,c,r-c,r+c)):
                families[f,j].append(r*n+c)
    # Use exactly the order of first group insertion supplied by model.py.
    assert list(families.values()) == lines(n)
    sat = [[] for _ in range(4)]
    incident = [[] for _ in range(n*n)]
    for i, ((f,j), cells) in enumerate(families.items()):
        sat[f].append(f's{i}')
        for c in cells:
            incident[c].append(f's{i}')
    q = [f"(assert (or {' '.join(ls)}))" for ls in incident]
    # Every square, including an occupied square, has a saturated line here.
    for f in range(4):
        q.append(f"(define-fun full{f} () Bool {cardinality('at-least',15,sat[f])})")
    if refined:
        q.append('(assert (and full0 full1 (or full2 full3)))')
        for f in (2,3):
            q.append(f"(assert {cardinality('at-least',13,sat[f])})")
        color = [f'q{r*n+c}' for r in range(n) for c in range(n) if (r+c)%2==0]
        choices = [f"(and {cardinality('at-least',k,color)} {cardinality('at-most',k,color)})"
                   for k in (10,12,14,16,18,20)]
        q.append(f"(assert (or {' '.join(choices)}))")
        return '\n'.join(q)
    for f in (0,1):
        q.append(f"(define-fun near{f} () Bool {cardinality('at-least',14,sat[f])})")
    q.append('(assert (or (and full0 full1 (or full2 full3)) (and full2 full3 near0 near1)))')
    return '\n'.join(q)


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    group = ap.add_mutually_exclusive_group()
    group.add_argument('--cut', action='store_true')
    group.add_argument('--refined', action='store_true')
    ap.add_argument('--emit', action='store_true')
    ap.add_argument('--timeout-ms', default=5000, type=int)
    a = ap.parse_args()
    if a.emit:
        print(model(30,30,a.timeout_ms))
        if a.cut or a.refined:
            print(cuts(a.refined))
        print('(check-sat)')
    else:
        start = time.monotonic()
        s = Solver(30,30,a.timeout_ms)
        if a.cut or a.refined:
            s.send(cuts(a.refined))
        status = s.query('(check-sat)')
        obj = dict(n=30,size=30,cut="refined" if a.refined else a.cut,timeout_ms=a.timeout_ms,seed=0,status=status)
        if status == 'sat':
            obj['queens'] = coords(30,s.witness())
        elif status == 'unknown':
            obj['reason'] = s.query('(get-info :reason-unknown)')
        for line in s.query('(get-info :all-statistics)').splitlines():
            import re
            m = re.match(r'[\s(]*:(conflicts|sat-conflicts|rlimit-count|sat-decisions|decisions|memory)\s+(\S+?)\)?$',line)
            if m:
                obj[m.group(1)] = m.group(2)
        s.close()
        obj['wall_s'] = round(time.monotonic()-start,3)
        print(json.dumps(obj))
