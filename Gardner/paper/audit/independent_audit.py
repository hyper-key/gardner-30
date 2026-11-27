#!/usr/bin/env python3
"""Standalone Gardner audit; imports no repository proof/search code.

Usage: python3 independent_audit.py /path/to/extracted-supplement
Checks the literal witness, coefficient arithmetic, and every local certificate.
Domain completeness additionally needs the written reductions and generators.
"""
from collections import Counter, defaultdict
from functools import lru_cache
from itertools import combinations_with_replacement, product
from math import comb
from pathlib import Path
import gzip
import json
from hashlib import sha256
import sys


def coefficient(counts):
    a, b, d, s = counts
    return sum((-1) ** (d-i) * comb(d, i) * comb(s, 29-a-i)
               for i in range(d+1) if 0 <= 29-a-i <= s)


def witness(root):
    data = json.loads((root / 'Gardner/construction/witness31.json').read_text())
    assert type(data['n']) is int and data['n'] == 30
    q = data['queens']
    assert len(q) == 31
    assert all(len(p) == 2 and all(type(x) is int and 0 <= x < 30 for x in p) for p in q)
    occupied = set(map(tuple, q))
    assert len(occupied) == 31
    def legal(points):
        return all(max(Counter(p[k] for p in
            ((r, c, r-c, r+c) for r, c in points)).values(), default=0) <= 2
            for k in range(4))
    assert legal(occupied)
    addable = [p for p in product(range(30), repeat=2)
               if p not in occupied and legal(occupied | {p})]
    assert not addable
    counts = [Counter(p[k] for p in ((r,c,r-c,r+c) for r,c in occupied))
              for k in range(4)]
    return {'queens': 31, 'literal_insertions_checked': 869,
            'saturated_by_family': [sum(v == 2 for v in c.values()) for c in counts],
            'addable': addable}


def local_case(header, reason, proof):
    e, u, v, off_r, off_c = header
    assert 14 <= e <= 29 and 0 <= off_r < 30-e and 0 <= off_c < 30-e
    assert u & 1 and v & 1 and u < 1 << e and v < 1 << e
    assert u.bit_count() == v.bit_count() == 14
    rows = {off_r+i for i in range(e) if u >> i & 1} | {off_r+e}
    cols = {off_c+i for i in range(e) if v >> i & 1} | {off_c+e}
    active_r, active_c = set(range(30))-rows, set(range(30))-cols
    edges = {(r-c, r+c) for r in rows for c in cols}
    assert len(edges) == 225
    support = (Counter(r-c for r in active_r for c in active_c),
               Counter(r+c for r in active_r for c in active_c))
    forced = ({d for d,s in edges if support[1][s] < 2},
              {s for d,s in edges if support[0][d] < 2})
    stats = Counter({reason: 1})

    def check_matching(matching, d, s):
        matching = list(map(tuple, matching))
        assert len(matching)+len(d)+len(s) > 30
        assert len({a for a,b in matching}) == len({b for a,b in matching}) == len(matching)
        assert all(p in edges and p[0] not in d and p[1] not in s for p in matching)

    if reason == 'uncoverable':
        d,s = proof
        assert (d,s) in edges and support[0][d] < 2 and support[1][s] < 2
    elif reason == 'forced_lane_capacity':
        d,s = map(set, proof)
        assert d <= forced[0] and s <= forced[1] and max(len(d), len(s)) > 15
    elif reason == 'matching':
        check_matching(proof, set(), set())
    elif reason == 'matching_after_forcing':
        d,s,m = proof
        d,s = set(d),set(s)
        assert d <= forced[0] and s <= forced[1]
        check_matching(m,d,s)
    else:
        assert reason == 'survives'
        first = (2*(sum(active_r)-sum(active_c)), 2*(sum(active_r)+sum(active_c)))
        second = 4*sum(x*x for axis in (active_r,active_c) for x in axis)

        @lru_cache(None)
        def moments(family, required):
            # Meet in the middle: independently build two bounded multisets,
            # join on the first moment, then check combined multiplicities.
            left = 30-2*len(required)
            assert 0 <= left <= 6
            needed = first[family]-2*sum(required)
            base = 2*sum(k*k for k in required)
            options = sorted(k for k in support[family] if k not in required)
            singleton = sum(1 << i for i,k in enumerate(options) if support[family][k] == 1)

            def halves(length):
                grouped = defaultdict(list)
                for indices in combinations_with_replacement(range(len(options)), length):
                    counts = Counter(indices)
                    if any(n > min(2, support[family][options[i]]) for i,n in counts.items()):
                        continue
                    used = sum(1 << i for i in counts)
                    twice = sum(1 << i for i,n in counts.items() if n == 2)
                    vals = [options[i] for i in indices]
                    grouped[sum(vals)].append((sum(k*k for k in vals),used,twice))
                return grouped

            a, b = halves(left//2), halves(left-left//2)
            out = set()
            for total, partials in a.items():
                for x, used_x, twice_x in partials:
                    for y, used_y, twice_y in b.get(needed-total, ()):
                        if twice_x & used_y or twice_y & used_x or used_x & used_y & singleton:
                            continue
                        out.add(base+x+y)
            return out

        def tree(node, d, s):
            if node == 'Q':
                assert max(len(d),len(s)) > 15
                stats['quota_leaves'] += 1
            elif node == 'M':
                assert all(a in d or b in s for a,b in edges)
                a, b = moments(0,tuple(sorted(d))), moments(1,tuple(sorted(s)))
                assert not any(second-x in b for x in a)
                stats['moment_leaves'] += 1
            else:
                family,key,yes,no = node
                assert family in (0,1)
                neighbors = {p[1-family] for p in edges
                             if p[family] == key and p[0] not in d and p[1] not in s}
                assert neighbors
                if family == 0:
                    tree(yes,d | {key},s)
                    tree(no,d,s | neighbors)
                else:
                    tree(yes,d,s | {key})
                    tree(no,d | neighbors,s)
        tree(proof,*forced)
    return stats, rows, cols


def certificates(root, stem, expected):
    directory = root / 'Gardner/exact'
    headers = [tuple(map(int, line.split()))
               for line in (directory / (stem+'_full.txt')).read_text().splitlines()]
    with gzip.open(directory / (stem+'_certs.json.gz'), 'rt') as f:
        proofs = json.load(f)
    assert len(headers) == len(proofs) == len(set(headers)) == expected
    stats = Counter()
    seen = set()
    for header, (reason, proof) in zip(headers, proofs, strict=True):
        local, rows, cols = local_case(header,reason,proof)
        def h(unused):
            active = [2*i-29 for i in range(30) if i not in unused]
            return 21*sum(active)**2-5*sum(i*i for i in active)
        assert sum(rows) == sum(cols) if stem == 'frame29' else h(rows) == h(cols)
        identity = (tuple(sorted(rows)),tuple(sorted(cols)))
        assert identity not in seen
        seen.add(identity)
        stats.update(local)
    return dict(stats)


def main():
    root = Path(sys.argv[1]).resolve()
    if not __debug__:
        raise SystemExit("Run the audit without Python optimization.")
    # The standalone archive has no .git directory. Pin its five audit inputs
    # to the original audited commit by content hash.
    inputs = {
        'Gardner/construction/witness31.json': 'a6fef7fdc272192e4ec8f332c92b17d6f40f80a8665c0cdc9093c60b7a37cae7',
        'Gardner/exact/frame29_full.txt': '99c7e001c6f39c0a018e796eb9fa025cfbea285018a78d77af1438906713209a',
        'Gardner/exact/frame29_certs.json.gz': 'f780aded7f133c15a1618929a583c8602cc2ca4e3985945d9a698d408c24974e',
        'Gardner/exact/frame30eq_full.txt': '1111ef1f05a85f30c15ac8a8d8add7beaafdaeaf917b10d2eb54765d8cd5fde5',
        'Gardner/exact/frame30eq_certs.json.gz': '6da42a0ece23db5eeeb511d2d7daa983e2b8a23598177527568140f8f242272d',
    }
    for name, expected in inputs.items():
        if sha256((root / name).read_bytes()).hexdigest() != expected:
            raise SystemExit(f"Audit input differs from revision 974663a: {name}")
    print("Verified five audit input hashes for 974663a", flush=True)
    print('witness',json.dumps(witness(root),sort_keys=True),flush=True)
    table = []
    for i,j in combinations_with_replacement(range(4),2):
        counts = [15]*4
        counts[i] -= 1
        counts[j] -= 1
        table.append(coefficient(counts))
    assert table == [-6435,0,-3432,-3432,6435,-3432,3432,0,-3432,0]
    for q in range(30):
        for isolated in range(q+1):
            bound = (q-isolated)//2
            assert bound <= 14 and 58-4*bound >= isolated
    for isolated in range(1,31):
        bound = (30-isolated)//2
        assert bound <= 14 and 58-4*bound >= isolated
    print('coefficient_table',table,'isolated-slot inequalities PASS',flush=True)
    print('frame29',json.dumps(certificates(root,'frame29',9016),sort_keys=True),flush=True)
    print('frame30eq',json.dumps(certificates(root,'frame30eq',11691),sort_keys=True),flush=True)
    print('PASS independent witness, coefficient arithmetic, and all 20707 local certificates.',flush=True)


if __name__ == '__main__':
    main()
