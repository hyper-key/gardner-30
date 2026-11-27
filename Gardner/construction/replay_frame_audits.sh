#!/usr/bin/env bash
set -euo pipefail
src=$(cd "$(dirname "$0")" && pwd)
tmpdir=$(mktemp -d)
cp "$src"/{audit_frame29.cpp,audit_full_frame.py,frame_controls.py} "$tmpdir/"
cd "$tmpdir"
compiler=${CXX:-g++}
if ! command -v "$compiler" >/dev/null; then
    compiler=/nix/store/0592hadxldzhhd3ppc6nskslzd39fwlz-gcc-wrapper-15.3.0/bin/g++
fi
"$compiler" -O3 -std=c++20 -mpopcnt -Wall -Wextra audit_frame29.cpp -o audit
./audit 30 14 shapes >shapes.txt
./audit >pairs29.txt
cmp "$src/../exact/frame29_full.txt" pairs29.txt
sha256sum shapes.txt pairs29.txt
python3 frame_controls.py ./audit
python3 audit_full_frame.py shapes.txt "$src/../exact/frame30eq_full.txt"
echo "Fresh replay written to $tmpdir"
