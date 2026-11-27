#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
logs=Gardner/formal/logs
mkdir -p "$logs"
sha256sum -c Gardner/formal/lower.sha256
lake build Gardner.formal.Perimeter Gardner.formal.PerimeterChallenge > "$logs/perimeter-build.txt" 2>&1
lake env lean Gardner/formal/Perimeter.lean > "$logs/perimeter.txt" 2>&1
lake env lean Gardner/formal/Bounds.lean > "$logs/bounds.txt" 2>&1
timeout 135 lake comparator --config Gardner/formal/lower.json --paranoid > "$logs/lower.txt" 2>&1
grep -q 'Your solution is okay!' "$logs/lower.txt"
sha256sum -c Gardner/formal/lower.sha256
