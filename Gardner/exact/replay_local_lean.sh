#!/usr/bin/env bash
# Assemble a typed Lean native validator and feed it the original certificates.
set -euo pipefail
cd "$(dirname "$0")/../.."
tmp=$(mktemp -d "${TMPDIR:-/tmp}/gardner-local-lean.XXXXXXXX")
lake env lean -c "$tmp/LocalCertificates.c" Gardner/exact/LocalCertificates.lean
lake env leanc -O3 "$tmp/LocalCertificates.c" -o "$tmp/check"
cd Gardner/exact
python3 local_lean_stream.py --sample > "$tmp/sample.jsonl"
python3 local_lean_stream.py --damaged > "$tmp/damaged.jsonl"
python3 local_lean_stream.py > "$tmp/records.jsonl"
sha256sum "$tmp/records.jsonl"
"$tmp/check" "$tmp/sample.jsonl" sample
timeout 115 "$tmp/check" "$tmp/records.jsonl" full frame29_full.txt frame30eq_full.txt
if "$tmp/check" "$tmp/damaged.jsonl" sample > "$tmp/damaged.log" 2>&1; then
    echo 'accepted damaged proof' >&2
    exit 1
fi
rg -F 'quota leaf within quota' "$tmp/damaged.log"
if "$tmp/check" "$tmp/sample.jsonl" full frame29_full.txt frame30eq_full.txt > "$tmp/missing.log" 2>&1; then
    echo 'accepted incomplete collection' >&2
    exit 1
fi
rg -F 'missing records' "$tmp/missing.log"
echo 'PASS damaged proof and incomplete-domain controls rejected.'
