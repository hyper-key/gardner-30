#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
logs=Gardner/formal/logs
mkdir -p "$logs" .lake/build/lib/lean/Gardner/formal

sha256sum -c Gardner/formal/spec.sha256
python3 Gardner/formal/cert_data.py Gardner/construction/witness31.json | cmp - GardnerData.lean
lake build GardnerChallenge GardnerSolution GardnerIncomplete GardnerWeakened > "$logs/build.txt" 2>&1
lake env lean Gardner/formal/controls.lean > "$logs/controls.txt" 2>&1
lake env lean Gardner/formal/Moment.lean > "$logs/moment.txt" 2>&1
lake env lean -o .lake/build/lib/lean/Gardner/formal/GridFunctional.olean Gardner/formal/GridFunctional.lean > "$logs/grid.txt" 2>&1
lake env lean Gardner/formal/FullMoment.lean >> "$logs/grid.txt" 2>&1
lake env lean -o .lake/build/lib/lean/Gardner/formal/StructureBridge.olean Gardner/formal/StructureBridge.lean > "$logs/bridge.txt" 2>&1
lake env lean Gardner/formal/AffineProducts.lean > "$logs/affine.txt" 2>&1
bash Gardner/formal/Unequal.sh
lake env lean Gardner/formal/Arithmetic.lean > "$logs/arithmetic.txt" 2>&1
lake env lean Gardner/formal/Axioms.lean > "$logs/axioms.txt" 2>&1
# Comparators run in their normal isolated environment. Cap each process group.
for case in solution incomplete weakened; do
    rc=0
    timeout 180 lake comparator --config "Gardner/formal/$case.json" --paranoid > "$logs/$case.txt" 2>&1 || rc=$?
    echo "$case $rc"
    case "$case" in
      solution) [[ $rc == 0 ]] && grep -q 'Your solution is okay!' "$logs/$case.txt" || exit 1 ;;
      incomplete) [[ $rc == 1 ]] && grep -q "Illegal axiom detected: 'sorryAx'" "$logs/$case.txt" || exit 1 ;;
      weakened) [[ $rc == 1 ]] && grep -q 'theorem statement do not match' "$logs/$case.txt" || exit 1 ;;
    esac
done
sha256sum -c Gardner/formal/spec.sha256
bash Gardner/formal/replay_lower.sh
