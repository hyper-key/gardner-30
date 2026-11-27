import json
import re
import subprocess
from model import coords, model
from oracle import placements


def run(text):
    proc = subprocess.run(['z3', '-in', '-smt2'], input=text+'\n(check-sat)\n',
                          capture_output=True, text=True, check=True)
    assert proc.stdout.strip() in ('sat', 'unsat'), proc.stdout
    return proc.stdout.strip()


def pin(n, m):
    return ''.join(f'(assert {"q"+str(i) if (m>>i)&1 else "(not q"+str(i)+")"})\n'
                   for i in range(n*n))


def test(name, n, mask, modified, expected):
    normal = run(model(n) + pin(n, mask))
    changed = run(modified + pin(n, mask))
    assert (normal, changed) == expected, (normal, changed)
    print(json.dumps(dict(mutation=name, n=n, queens=coords(n, mask), original=normal, mutated=changed)))


# Saturation is >=2 on a legal board. A diagonal pair is blocked on its own
# three-square line but leaves several other empty squares legally addable.
n = 3
q = (1 << 0) | (1 << 4)
test('saturated means >=1', n, q, model(n).replace('(_ at-least 2)', '(_ at-least 1)'),
     ('unsat', 'sat'))
test('drop maximality assertions', n, 0,
     '\n'.join(row for row in model(n).splitlines() if not row.startswith('(assert (or q')),
     ('unsat', 'sat'))

# Remove just the at-most-two constraint on the main diagonal, then obtain
# a model containing all three diagonal queens to exhibit the discrepancy.
d = '(assert ((_ at-most 2) q0 q4 q8))'
assert model(n).count(d) == 1
weaker = model(n).replace(d, '')
diag = (1<<0) | (1<<4) | (1<<8)
m = next(m for m in range(512) if m & diag == diag and run(weaker + pin(3, m)) == 'sat')
test('omit main-diagonal capacity', n, m, weaker, ('unsat', 'sat'))

# Existential search only picks an independently legal maximal board with an
# isolated queen. Confirm the altered and original formulas at that exact board.
n = 4
stronger = re.sub(r'\(assert \(or q\d+ ', '(assert (or ', model(n))
def has_isolated(m):
    qs = coords(n,m)
    return any(all((r,c)==(u,v) or (r!=u and c!=v and abs(r-u)!=abs(c-v))
                   for u,v in qs) for r,c in qs)
m = next(m for m in sorted(placements(n)) if has_isolated(m))
test('require saturated line even at occupied square', n, m, stronger, ('sat','unsat'))
