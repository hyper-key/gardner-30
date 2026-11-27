#!/usr/bin/env bash
# Replay decisive evidence and calibrated checks from a prepared proofs checkout.
set -euo pipefail
cd "$(dirname "$0")/.."
export PYTHONHASHSEED=0
if [[ -n "${PYTHONOPTIMIZE:-}" ]]; then
    echo 'Run with Python assertions enabled.' >&2
    exit 2
fi
tmp=$(mktemp -d)
if [[ -z "${CXX:-}" ]]; then
    if command -v g++ >/dev/null; then
        CXX=g++
    else
        CXX=/nix/store/0592hadxldzhhd3ppc6nskslzd39fwlz-gcc-wrapper-15.3.0/bin/g++
    fi
fi
export CXX

python3 Gardner/validation/controls.py
for n in 10 12 18 26 31; do
    python3 Gardner/validation/check.py "Gardner/construction/witness$n.json" --expect "$n"
done
python3 Gardner/exact/projected.py
python3 Gardner/exact/mutations.py
python3 Gardner/structure/cover_coefficients.py
python3 Gardner/structure/tail_table.py

bash Gardner/exact/replay_frames.sh
bash Gardner/construction/replay_frame_audits.sh
"$CXX" -O3 -std=c++20 Gardner/structure/unequal_axes.cpp -o "$tmp/unequal"
"$tmp/unequal" > "$tmp/unequal.pairs" 2> "$tmp/unequal.counts"
cmp "$tmp/unequal.counts" Gardner/records/unequal_counts.txt
test ! -s "$tmp/unequal.pairs"
bash Gardner/construction/replay_modular.sh

bash Gardner/formal/benchmark.sh
bash Gardner/formal/replay.sh
lake env lean Gardner/exact/Marginal.lean
bash Gardner/exact/replay_local_lean.sh
echo 'PASS: witness, bounds, domain coverage and finite rejection certificates.'
