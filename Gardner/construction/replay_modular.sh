#!/usr/bin/env bash
set -euo pipefail
src=$(cd "$(dirname "$0")" && pwd)
tmpdir=$(mktemp -d)
mkdir "$tmpdir/construction" "$tmpdir/exact"
cp "$src"/{modular_axes.cpp,verify_modular_axes.cpp,modular_perimeter.py,modular_certificate.py,check_modular_certificate.py} "$tmpdir/construction/"
cp "$src/../exact/axis_matching.py" "$tmpdir/exact/"
cd "$tmpdir/construction"
compiler=${CXX:-g++}
if ! command -v "$compiler" >/dev/null; then
    compiler=/nix/store/0592hadxldzhhd3ppc6nskslzd39fwlz-gcc-wrapper-15.3.0/bin/g++
fi
"$compiler" -std=c++20 -O3 -mpopcnt -Wall -Wextra modular_axes.cpp -o gen_axes
"$compiler" -std=c++20 -O3 -Wall -Wextra verify_modular_axes.cpp -o verify_axes
./gen_axes > modular-pairs.txt
./verify_axes > independently-generated.txt
cmp modular-pairs.txt independently-generated.txt
cmp modular-pairs.txt "$src/modular-pairs.txt"
python3 modular_perimeter.py
cmp modular-perimeter.json "$src/modular-perimeter.json"
python3 modular_certificate.py
cmp modular-certificate.json "$src/modular-certificate.json"
python3 check_modular_certificate.py
echo "Fresh replay written to $tmpdir"
