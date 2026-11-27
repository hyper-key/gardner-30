"""Independent seven-case table; derive all required keys by visiting target cells."""
from itertools import product

def row(e):
    o = 17-e
    diffs = {d for d in range(-14,15) if abs(d) < (o if d%2 else e)}
    sums = {i+j-13 for i,j in product(range(15), repeat=2) if abs(i-j) in (e,o)}
    assert len(diffs) == 15 and len(sums) == 13 and sum(sums) == 13
    return 2240-2*sum(v*v for v in diffs)-2*sum(v*v for v in sums)

if __name__ == '__main__':
    actual = [row(e) for e in range(2,15,2)]
    assert actual == [-1062,170,954,1290,1178,618,-390]
    print(actual)
