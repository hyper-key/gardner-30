#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
scratch=$(mktemp -d)
logs="$PWD/Gardner/formal/logs"
mkdir -p "$logs"
cp -a Benchmark/. "$scratch"
sha256sum -c Benchmark/fixed.sha256 > "$logs/six-hashes.txt"
python3 "$scratch/six_point_reference.py" > "$logs/six-python.txt"
python3 "$scratch/z3_reference.py" > "$logs/six-z3.txt"
lake build SixPointChallenge SixPointSolution SixPointIncomplete SixPointWeakened > "$logs/six-build.txt" 2>&1
lake env lean Feedback.lean > "$logs/six-feedback.txt" 2>&1
lake env lean Benchmark/Axioms.lean > "$logs/six-axioms.txt" 2>&1
for case in correct incomplete weakened; do
    config=Benchmark/comparator.json
    if [[ $case != correct ]]; then config="Benchmark/comparator-$case.json"; fi
    rc=0
    lake comparator --config "$config" --paranoid > "$logs/six-$case.txt" 2>&1 || rc=$?
    if [[ $case == correct ]]; then
        [[ $rc == 0 ]]
        grep -q 'Your solution is okay!' "$logs/six-$case.txt"
    else
        [[ $rc == 1 ]]
        if [[ $case == incomplete ]]; then grep -qi 'sorryAx' "$logs/six-$case.txt"; else grep -qi 'do not match' "$logs/six-$case.txt"; fi
    fi
    echo "$case $rc"
done
sha256sum -c Benchmark/fixed.sha256
