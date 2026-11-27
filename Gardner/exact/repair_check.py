from collections import Counter
from oracle import placements
from repair import Repair, indices

for n in range(1, 5):
    good = placements(n)
    shells = 0
    answers = 0
    for s in sorted(good):
        sampler = Repair(n, [divmod(i, n) for i in indices(s)])
        target = {q for q in good if q.bit_count() + 1 == s.bit_count()}
        expected = Counter((s & ~q).bit_count() for q in target)
        for d in range(1, s.bit_count()+1):
            counts, first = sampler.enumerate(d)
            assert counts['solutions'] == expected[d], (n,s,d,counts,expected)
            if counts['solutions']:
                assert first in target and (s & ~first).bit_count() == d
            shells += 1
            answers += counts['solutions']
    print(f'n={n} seeds={len(good)} shells={shells} directed_target_pairs={answers}')
