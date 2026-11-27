"""Independent SMT cross-checks of the solved six-vertex fixture only."""
from pathlib import Path
import subprocess

LOGS = Path(__file__).parent / "logs"
LOGS.mkdir(exist_ok=True)
PRELUDE = """(set-logic QF_LIA)
(define-fun abs ((v Int)) Int (ite (< v 0) (- v) v))
(define-fun dist ((x Int) (y Int)) Int
  (ite (< (abs (- x y)) (- 6 (abs (- x y))))
       (abs (- x y)) (- 6 (abs (- x y)))))
"""
PRELUDE += "\n".join(f"(declare-const x{i} Int)" for i in range(6)) + "\n"
PRELUDE += "\n".join(f"(assert (and (<= 0 x{i}) (< x{i} 6)))" for i in range(6)) + "\n"
VALID = "(assert (distinct x0 x1 x2 x3 x4 x5))\n"
TARGET = [3, 2, 1, 2, 1]


def fixed(path):
    return "\n".join(f"(assert (= x{i} {v}))" for i, v in enumerate(path)) + "\n"


def distances(target):
    return "\n".join(f"(assert (= (dist x{i} x{i+1}) {d}))" for i, d in enumerate(target)) + "\n"


def check(name, body, expected):
    text = PRELUDE + body + "(check-sat)\n"
    (LOGS / f"z3-{name}.smt2").write_text(text)
    run = subprocess.run(["z3", "-in"], input=text, text=True, capture_output=True, check=True)
    (LOGS / f"z3-{name}.txt").write_text(run.stdout + run.stderr)
    assert run.stdout.strip() == expected, (name, run.stdout, run.stderr)
    print(f"{name}: {expected}")


check("known-witness", VALID + fixed([0, 3, 1, 2, 4, 5]) + distances(TARGET), "sat")
check("target-profile-exists", VALID + distances(TARGET), "sat")
check("repeated-rejected", VALID + fixed([0, 3, 1, 2, 0, 1]) + distances(TARGET), "unsat")
check("wraparound", "(assert (not (= (dist 0 5) 1)))\n", "unsat")
check("all-two-impossible", VALID + distances([2] * 5), "unsat")
histogram = ""
for length, count in ((1, 2), (2, 2), (3, 1)):
    terms = [f"(ite (= (dist x{i} x{(i+1)%6}) {length}) 1 0)" for i in range(6)]
    histogram += f"(assert (= (+ {' '.join(terms)}) {count}))\n"
check("closing-edge-rejected", VALID + fixed([0, 3, 1, 2, 4, 5]) + histogram, "unsat")
