#!/usr/bin/env python3
"""Exact swap-neighborhood enumeration. No solver or model.py dependency."""
import argparse
from collections import Counter
from itertools import combinations
import json
import math
from pathlib import Path
import time


def indices(bits):
    while bits:
        b = bits & -bits
        yield b.bit_length() - 1
        bits ^= b


class Repair:
    def __init__(self, n, queens):
        self.n = n
        if type(n) is not int or n < 1:
            raise ValueError('invalid board size')
        if any(len(p) != 2 or any(type(x) is not int or not 0 <= x < n for x in p) for p in queens):
            raise ValueError('invalid coordinate')
        cells = sorted(r*n + c for r, c in queens)
        if len(set(cells)) != len(cells):
            raise ValueError('duplicate coordinate')
        self.seed = sum(1 << i for i in cells)
        self.cells = cells
        self.full = (1 << (n * n)) - 1
        self.lines = [0] * (6 * n - 2)
        self.inc = []
        for i in range(n*n):
            r, c = divmod(i, n)
            ls = (r, n+c, 3*n-1+r-c, 4*n-1+r+c)
            self.inc.append(ls)
            for l in ls:
                self.lines[l] |= 1 << i
        self.attack = [self.lines[a]|self.lines[b]|self.lines[c]|self.lines[d] for a,b,c,d in self.inc]
        counts = [(self.seed & line).bit_count() for line in self.lines]
        if max(counts) > 2:
            raise ValueError('invalid seed contains triple')
        self.twos = [j for j, a in enumerate(counts) if a == 2]
        blocked = self.seed
        for l in self.twos:
            blocked |= self.lines[l]
        if blocked != self.full:
            raise ValueError('nonmaximal seed')

    def enumerate(self, removed_count):
        """Returns counters including exact number of maximal repairs in this shell."""
        counts = Counter(subsets=0, search_nodes=0, solutions=0)
        first = None

        def visit(occupied, free, candidates, left):
            nonlocal first
            counts['search_nodes'] += 1
            if not left:
                if not free:
                    counts['solutions'] += 1
                    if first is None:
                        first = occupied
                return
            if candidates.bit_count() < left:
                return
            # A currently addable square must itself be chosen or be blocked by
            # at least one later queen in its row, column or either diagonal.
            # Choose the addable square with fewest prospective neighbors.
            choice = candidates
            best = candidates.bit_count()
            for hole in indices(free):
                domain = candidates & self.attack[hole]
                size = domain.bit_count()
                if not size:
                    return
                if size < best:
                    best, choice = size, domain
            for i in indices(choice):
                b = 1 << i
                candidates ^= b
                new_free = free ^ b
                for l in self.inc[i]:
                    if self.lines[l] & occupied:
                        new_free &= ~self.lines[l]
                visit(occupied | b, new_free, candidates & new_free, left - 1)

        for removed in combinations(self.cells, removed_count):
            counts['subsets'] += 1
            rm_mask = sum(1 << i for i in removed)
            occupied = self.seed ^ rm_mask
            blocked = occupied
            for l in self.twos:
                if not (self.lines[l] & rm_mask):
                    # Only deleted seed queens can undo a saturated seed line.
                    blocked |= self.lines[l]
            free = self.full ^ blocked
            visit(occupied, free, free & ~self.seed, removed_count - 1)
        assert counts['subsets'] == math.comb(len(self.cells), removed_count)
        return counts, first


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('witness', type=Path)
    p.add_argument('removals', type=int, nargs='+')
    a = p.parse_args()
    data = json.loads(a.witness.read_text())
    tree = Repair(data['n'], data['queens'])
    for d in a.removals:
        if not 1 <= d <= len(tree.cells):
            p.error('radius must lie in [1, seed size]')
        start = time.monotonic()
        counts, first = tree.enumerate(d)
        result = dict(n=tree.n, base=len(tree.cells), removed=d, added=d-1, **counts)
        if first is not None:
            result['queens'] = [list(divmod(i, tree.n)) for i in indices(first)]
        result['wall_s'] = round(time.monotonic() - start, 4)
        print(json.dumps(result), flush=True)
