"""Necessary diagonal count vectors for the one-color equality case n=2m."""
import argparse
from collections import Counter, defaultdict
from functools import lru_cache
from itertools import combinations_with_replacement, product
import json


def mandatory(m, parity, t):
    ds = {d for d in range(1-m, m) if d % 2 == parity and abs(d) < t}
    sums = set(range(2-m+t, m+1-t, 2)) if t < m else set()
    return ds, sums


@lru_cache(None)
def complete(m, mandatory_keys):
    keys = range(1-m, m)
    fixed = tuple(sorted(mandatory_keys * 2))
    if len(fixed) > 2*m or any(m-abs(x) < 2 for x in fixed):
        return ()
    candidates = [x for x in keys if x not in fixed]
    need = 2*m - len(fixed)
    # All templates reaching this call pass the two family cardinality bounds.
    answers = []
    for extra in combinations_with_replacement(candidates, need):
        if sum(extra) != -sum(fixed):
            continue
        if any(count > min(2, m-abs(x)) for x, count in Counter(extra).items()):
            continue
        answers.append(tuple(sorted(fixed + extra)))
    return tuple(answers)


def profiles(m):
    target_square_sum = 2*sum((2*i-(m-1))**2 for i in range(m))
    choices = [list(range(p, m, 2))+[m+1] for p in (0, 1)]
    totals = Counter()
    possibilities = set()
    for te, to in product(*choices):
        de, se = mandatory(m, 0, te)
        do, so = mandatory(m, 1, to)
        dkeys, skeys = de | do, se | so
        if max(len(dkeys),len(skeys)) > m:
            continue
        totals["capacity_templates"] += 1
        ds = complete(m, tuple(sorted(dkeys)))
        ss = complete(m, tuple(sorted(skeys)))
        if ds and ss:
            totals["first_moment_templates"] += 1
        index = defaultdict(list)
        for s in ss:
            # d and the UNcentered sum i+j of each queen have the same parity.
            k = (sum(x*x for x in s), sum((x+m-1)%2 for x in s))
            index[k].append(s)
        feasible = False
        for d in ds:
            k = (target_square_sum-sum(x*x for x in d), sum(x%2 for x in d))
            for s in index.get(k, []):
                possibilities.add((d,s))
                feasible = True
        if feasible:
            totals["second_moment_and_parity_templates"] += 1
    totals["distinct_marginal_pairs"] = len(possibilities)
    return totals, sorted(possibilities)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("sizes", nargs="+", type=int, help="even full-board sizes")
    parser.add_argument("--dump")
    args = parser.parse_args()
    if args.dump and len(args.sizes) != 1:
        parser.error("dump accepts one size")
    for n in args.sizes:
        assert n >= 2 and n % 2 == 0
        counts, options = profiles(n//2)
        print(n, json.dumps(counts, sort_keys=True))
        if args.dump:
            with open(args.dump, "w") as out:
                json.dump(options, out)
                out.write("\n")
