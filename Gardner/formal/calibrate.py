"""Time the certificate pipeline on the seeded 56-queen greedy baseline."""
import random
import subprocess
import tempfile
import time
from collections import Counter
from itertools import product
from pathlib import Path

from cert_data import emit

ROOT = Path(__file__).resolve().parents[2]
n = 30
rng = random.Random(1)
board = list(product(range(n), repeat=2))
rng.shuffle(board)
counts = [Counter() for _ in range(4)]
queens = []
for r, c in board:
    keys = (r, c, r+c, r-c)
    if all(hist[k] < 2 for hist, k in zip(counts, keys)):
        queens.append((r, c))
        for hist, k in zip(counts, keys):
            hist[k] += 1
assert len(queens) == 56

with tempfile.TemporaryDirectory() as temp:
    path = Path(temp) / 'Calibration.lean'
    # Use the same proof helper as the actual certificate. The scratch module
    # has its own witness and does not import any real-board certificate data.
    data = emit({'n': n, 'queens': queens})
    proof = (ROOT / 'GardnerSolution.lean').read_text().split('namespace Gardner\n', 1)[1]
    proof = proof.split('theorem upper31', 1)[0] + '''theorem calibration : Good 30 witness := by
  apply good_of_lines (ls := witnessLines) <;> decide
end Gardner
'''
    path.write_text(data + '\nnamespace Gardner\n' + proof)
    started = time.monotonic()
    subprocess.run(['lake', 'env', 'lean', str(path)], cwd=ROOT, check=True)
    print(f'seed=1 count={len(queens)} elapsed={time.monotonic()-started:.2f}s')
