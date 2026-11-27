"""Fast necessary tests for one choice of the paired rows and columns."""
import argparse
from collections import Counter, defaultdict
import json
from pathlib import Path
import random
import time


def matching(edges):
    adjacency = defaultdict(list)
    for a, b in sorted(edges):
        adjacency[a].append(b)
    right = {}
    def augment(a, seen):
        for b in adjacency[a]:
            if b in seen:
                continue
            seen.add(b)
            if b not in right or augment(right[b], seen):
                right[b] = a
                return True
        return False
    for a in sorted(adjacency, key=lambda a: len(adjacency[a])):
        augment(a, set())
    return sorted((a,b) for b,a in right.items())


def pair_test(n, rows, cols):
    assert n % 2 == 0 and len(rows) == len(cols) == n//2
    board = set(range(n))
    avd = Counter(r-c for r in rows for c in cols)
    avs = Counter(r+c for r in rows for c in cols)
    edges = [(r-c,r+c) for r in board-rows for c in board-cols]
    match = matching(edges)
    dforce, sforce = set(), set()
    illegal = None
    for d,s in edges:
        if avd[d]<2 and avs[s]<2:
            illegal = [d,s]
            break
        if avd[d]<2:
            sforce.add(s)
        if avs[s]<2:
            dforce.add(d)
    res = {'matching_size':len(match)}
    if illegal:
        res.update(reason='uncoverable', proof=illegal)
    elif len(dforce)>n//2 or len(sforce)>n//2:
        res.update(reason='forced_lane_capacity',proof=[sorted(dforce),sorted(sforce)])
    elif len(match)>n:
        res.update(reason='matching', proof=match)
    else:
        remaining = [(d,s) for d,s in edges if d not in dforce and s not in sforce]
        m2 = matching(remaining)
        if len(m2) + len(dforce) + len(sforce)>n:
            res.update(reason='matching_after_forcing', proof=[sorted(dforce),sorted(sforce),m2])
        else:
            res.update(reason='survives')
    return res


def axis(x):
    return sorted(set(x))


def sample(label, pairs, n, save):
    counts = Counter()
    mh = Counter()
    examples = {}
    t = time.monotonic()
    for rows,cols in pairs:
        rows,cols = set(rows),set(cols)
        r = pair_test(n,rows,cols)
        reason = r['reason']
        counts[reason] += 1
        mh[r['matching_size']] += 1
        if reason not in examples:
            examples[reason] = dict(n=n,rows=axis(rows),cols=axis(cols),**r)
    save[label] = examples
    print(json.dumps(dict(label=label,n=n,draws=sum(counts.values()),classification=dict(counts),
                          matching_histogram=dict(sorted(mh.items())),wall_s=round(time.monotonic()-t,3))),
          flush=True)


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--seed', type=int, default=300031)
    ap.add_argument('--draws', type=int, default=1000)
    ap.add_argument('--examples', type=Path)
    args = ap.parse_args()
    rng = random.Random(args.seed)
    examples = {}
    # The six-queen witness is listed in calibration.jsonl.
    sample('known-6', [({1,3,5},{1,3,5})],6,examples)
    sample('known-4', [({0,3},{0,3}),({1,2},{1,2})],4,examples)
    sample('invalid-4', [({0,2},{0,2})],4,examples)
    intervals = [set(range(i,i+15)) for i in range(16)]
    parity = [set(range(i,30,2)) for i in (0,1)]
    sample('all-interval-pairs', ((a,b) for a in intervals for b in intervals),30,examples)
    sample('all-parity-pairs', ((a,b) for a in parity for b in parity),30,examples)
    def pick():
        return set(rng.sample(range(30),15))
    def perturb_parity():
        base = parity[rng.randrange(2)]
        return (base-{rng.choice(sorted(base))})|{rng.choice(sorted(set(range(30))-base))}
    sample('uniform-independent', ((pick(),pick()) for _ in range(args.draws)),30,examples)
    sample('uniform-identical', ((a,a) for a in (pick() for _ in range(args.draws))),30,examples)
    sample('one-swap-from-parity-per-axis', ((perturb_parity(),perturb_parity())
                                             for _ in range(args.draws)),30,examples)
    if args.examples:
        args.examples.write_text(json.dumps(examples,sort_keys=True)+'\n')
