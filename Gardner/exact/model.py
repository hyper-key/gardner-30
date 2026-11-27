#!/usr/bin/env python3
"""Standalone SMT-LIB model generator and deterministic Z3 driver (no bindings)."""
import argparse
import collections
import re
import subprocess


def lines(n):
    groups = collections.defaultdict(list)
    for r in range(n):
        for c in range(n):
            for kind, index in enumerate((r, c, r - c, r + c)):
                groups[kind, index].append(r * n + c)
    return list(groups.values())


def cardinality(symbol, k, variables):
    # Simplification is needed for empty vectors and out-of-range bounds.
    if symbol == 'at-least':
        if k <= 0:
            return 'true'
        if k > len(variables):
            return 'false'
    else:
        if k < 0:
            return 'false'
        if k >= len(variables):
            return 'true'
    return f"((_ {symbol} {k}) {' '.join(variables)})"


def model(n, size=None, timeout_ms=10000, seed=0):
    if n < 1 or timeout_ms <= 0:
        raise ValueError('positive board size and timeout required')
    queens = [f'q{i}' for i in range(n * n)]
    qs = [f'(set-option :timeout {timeout_ms})',
          f'(set-option :sat.random_seed {seed})', f'(set-option :smt.random_seed {seed})']
    qs += [f'(declare-fun {q} () Bool)' for q in queens]
    coverage = [[q] for q in queens]
    for j, squares in enumerate(lines(n)):
        variables = [queens[i] for i in squares]
        saturated = f's{j}'
        qs.extend([f"(assert {cardinality('at-most', 2, variables)})",
                   f"(define-fun {saturated} () Bool {cardinality('at-least', 2, variables)})"])
        for i in squares:
            coverage[i].append(saturated)
    qs += [f"(assert (or {' '.join(terms)}))" for terms in coverage]
    if size is not None:
        qs += [f"(assert {cardinality(op, size, queens)})" for op in ('at-most', 'at-least')]
    return '\n'.join(qs) + '\n'


class Solver:
    def __init__(self, n, size=None, timeout_ms=10000, seed=0):
        self.n = n
        self.p = subprocess.Popen(['z3', '-in', '-smt2'], stdin=subprocess.PIPE,
                                  stdout=subprocess.PIPE, text=True, bufsize=1)
        self.send(model(n, size, timeout_ms, seed))

    def send(self, cmd):
        self.p.stdin.write(cmd + '\n')
        self.p.stdin.flush()

    def query(self, cmd):
        self.send(cmd)
        out = self.p.stdout.readline()
        if not out:
            raise RuntimeError('unexpected solver EOF')
        while out.count('(') > out.count(')'):
            extra = self.p.stdout.readline()
            if not extra:
                raise RuntimeError('unexpected solver EOF in S-expression')
            out += extra
        if '(error' in out:
            raise RuntimeError(out)
        return out.strip()

    def witness(self):
        names = ' '.join(f'q{i}' for i in range(self.n ** 2))
        out = self.query(f'(get-value ({names}))')
        pairs = re.findall(r'\(q(\d+) (true|false)\)', out)
        if sorted(int(i) for i, _ in pairs) != list(range(self.n ** 2)):
            raise RuntimeError('incomplete or duplicate square assignment')
        return sum(1 << int(i) for i, value in pairs if value == 'true')

    def exclude(self, mask):
        literals = [f'(not q{i})' if mask >> i & 1 else f'q{i}' for i in range(self.n ** 2)]
        self.send(f"(assert (or {' '.join(literals)}))")

    def close(self):
        self.send('(exit)')
        if self.p.wait() != 0:
            raise RuntimeError('z3 failed')


def coords(n, mask):
    return [list(divmod(i, n)) for i in range(n ** 2) if mask >> i & 1]


if __name__ == '__main__':
    import json
    import time
    ap = argparse.ArgumentParser()
    ap.add_argument('n', type=int)
    ap.add_argument('--size', type=int)
    ap.add_argument('--timeout-ms', type=int, default=10000)
    ap.add_argument('--seed', type=int, default=0)
    ap.add_argument('--emit', action='store_true')
    args = ap.parse_args()
    if args.emit:
        print(model(args.n, args.size, args.timeout_ms, args.seed), end='')
        print('(check-sat)')
    else:
        t = time.monotonic()
        s = Solver(args.n, args.size, args.timeout_ms, args.seed)
        status = s.query('(check-sat)')
        result = dict(n=args.n, size=args.size, timeout_ms=args.timeout_ms, seed=args.seed, status=status)
        if status == 'sat':
            result['queens'] = coords(args.n, s.witness())
        elif status == 'unknown':
            result['reason'] = s.query('(get-info :reason-unknown)')
        s.close()
        result['wall_s'] = round(time.monotonic() - t, 3)
        print(json.dumps(result))
