#!/usr/bin/env bash
set -euo pipefail
src=$(cd "$(dirname "$0")" && pwd)
tmpdir=$(mktemp -d)
mkdir "$tmpdir/construction" "$tmpdir/exact"
cp "$src"/*.py "$src"/orbit_repair.cpp "$src"/witness31-initial.json "$tmpdir/construction/"
cp "$src/../exact/axis_matching.py" "$tmpdir/exact/"
cd "$tmpdir/construction"
export PYTHONHASHSEED=0
python3 profiles.py --ms 300 --out witness31.json
for m in 5 9 13; do
    python3 profiles.py --m "$m" --even-only --ms 700 --out "witness$((2*m)).json"
done
python3 transplant.py witness26.json --out transplant-result.json
compiler=${CXX:-g++}
if ! command -v "$compiler" >/dev/null; then
    compiler=/nix/store/0592hadxldzhhd3ppc6nskslzd39fwlz-gcc-wrapper-15.3.0/bin/g++
fi
"$compiler" -std=c++20 -O2 -Wall -Wextra orbit_repair.cpp -o orbit_repair
./orbit_repair 30 30 | tee orbit-30.log
python3 controls.py ./orbit_repair
cmp "$src"/transplant-result.json transplant-result.json
cmp "$src"/orbit-30.log orbit-30.log
python3 periodic.py
python3 check_periodic.py
cmp "$src"/periodic-cert.json.gz periodic-cert.json.gz
echo "Fresh replay written to $tmpdir"
