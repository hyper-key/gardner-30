"""Emit explicit Lean certificate constants; the kernel rechecks their content."""
import argparse
import json
from collections import Counter
from pathlib import Path

def emit(data):
    n = data["n"]
    queens = [tuple(p) for p in data["queens"]]
    counts = [
        Counter(q[i] for q in queens)
        for i in range(2)
    ] + [
        Counter(r + c for r, c in queens),
        Counter(r + n - 1 - c for r, c in queens),
    ]
    def fmt_queens():
        return ', '.join(f'({r},{c})' for r, c in queens)
    def fmt_lines():
        return ', '.join(
            f'(.{d},{k})' for d, hist in zip(['row', 'col', 'sum', 'diff'], counts)
            for k, v in sorted(hist.items()) if v == 2
        )
    return f'''import GardnerDefs
namespace Gardner

def witness : List Square := [{fmt_queens()}]

def witnessLines : List (Dir × Nat) := [{fmt_lines()}]

end Gardner
'''
if __name__ == '__main__':
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('json', type=Path)
    args = ap.parse_args()
    print(emit(json.loads(args.json.read_text())), end='')
