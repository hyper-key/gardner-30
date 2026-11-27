#!/usr/bin/env bash
# Run from the pinned development box. No modifications made to saved evidence.
set -euo pipefail
cd "$(dirname "$0")"
t=$(mktemp -d "${TMPDIR:-/tmp}/gardner-frames.XXXXXXXX")
compiler=${CXX:-/nix/store/0592hadxldzhhd3ppc6nskslzd39fwlz-gcc-wrapper-15.3.0/bin/g++}
for src in frame29_axes frame30eq_axes; do
    "$compiler" -std=c++20 -O3 -march=native "$src.cpp" -o "$t/$src"
done
timeout 60 "$t/frame29_axes" full > "$t/29.txt" 2> "$t/29.log"
timeout 60 "$t/frame30eq_axes" > "$t/30.txt" 2> "$t/30.log"
cmp frame29_full.txt "$t/29.txt"
cmp frame30eq_full.txt "$t/30.txt"
python3 check_frame29.py
python3 check_frame30eq.py
echo "Verified both generators, all listed local certificates, and corruption controls. Replay temp: $t"
