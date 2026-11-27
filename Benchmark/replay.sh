#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p Benchmark/logs

expect_rc() {
  local label="$1" expected="$2" result
  shift 2
  printf 'RUN %s:' "$label"
  printf ' %q' "$@"
  printf '\n'
  set +e
  "$@" > "Benchmark/logs/$label.txt" 2>&1
  result=$?
  set -e
  printf 'EXIT %s (expected %s)\n' "$result" "$expected"
  if [[ "$result" != "$expected" ]]; then
    cat "Benchmark/logs/$label.txt"
    return 1
  fi
}

sha256sum -c Benchmark/fixed.sha256
expect_rc python-reference 0 python3 Benchmark/six_point_reference.py
expect_rc z3-reference 0 python3 Benchmark/z3_reference.py
expect_rc build 0 lake build SixPointChallenge SixPointSolution SixPointIncomplete SixPointWeakened
expect_rc feedback-repaired-cli 0 lake env lean Feedback.lean
expect_rc axioms 0 lake env lean Benchmark/Axioms.lean
expect_rc comparator-correct 0 lake comparator --config Benchmark/comparator.json --paranoid
expect_rc comparator-incomplete 1 lake comparator --config Benchmark/comparator-incomplete.json --paranoid
expect_rc comparator-weakened 1 lake comparator --config Benchmark/comparator-weakened.json --paranoid
sha256sum -c Benchmark/fixed.sha256
echo 'PASS: known-answer suite, repaired proof, comparator controls, fixed source hashes.'
