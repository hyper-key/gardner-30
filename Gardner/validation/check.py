"""Independent witness audit: pairs, cross products, and explicit addable squares."""
import argparse
import itertools
import json
from pathlib import Path


def audit(data):
    if not isinstance(data, dict) or type(data.get("n")) is not int or data["n"] < 1:
        raise ValueError("n must be a positive integer")
    n = data["n"]
    points = data.get("queens")
    if not isinstance(points, list):
        raise ValueError("queens must be an array")
    queens = []
    for p in points:
        if not isinstance(p, (list, tuple)) or len(p) != 2 or any(type(x) is not int for x in p):
            raise ValueError("expected two integer coordinates")
        if not all(0 <= x < n for x in p):
            raise ValueError("out-of-board queen")
        queens.append(tuple(p))
    occupied = set(queens)
    if len(queens) != len(occupied):
        raise ValueError("duplicate queen")
    pairs = []
    for (r, c), (s, t) in itertools.combinations(queens, 2):
        dr, dc = s-r, t-c
        if dr == 0 or dc == 0 or abs(dr) == abs(dc):
            pairs.append((r, c, dr, dc))

    def on_line(p, line):
        r, c, dr, dc = line
        return (p[0]-r)*dc == (p[1]-c)*dr

    for line in pairs:
        collinear = [p for p in queens if on_line(p, line)]
        if len(collinear) > 2:
            raise ValueError(f"triple on queen line: {collinear}")
    addable = [p for p in itertools.product(range(n), repeat=2)
               if p not in occupied and not any(on_line(p, line) for line in pairs)]
    return {"n": n, "count": len(queens), "empty": n*n-len(queens),
            "saturated_lines": len(pairs), "addable": addable, "maximal": not addable}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("file", type=Path)
    parser.add_argument("--expect", type=int)
    args = parser.parse_args()
    try:
        result = audit(json.loads(args.file.read_text()))
    except ValueError as err:
        parser.exit(1, f"{err}\n")
    print(json.dumps(result))
    raise SystemExit(int(not result["maximal"] or
                         (args.expect is not None and result["count"] != args.expect)))
