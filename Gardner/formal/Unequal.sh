#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
mkdir -p .lake Gardner/formal/logs
compiler=${CXX:-/nix/store/0592hadxldzhhd3ppc6nskslzd39fwlz-gcc-wrapper-15.3.0/bin/g++}
"$compiler" -std=c++20 -O3 -march=native Gardner/formal/Unequal.cpp -o .lake/unequal
timeout 150 .lake/unequal | tee Gardner/formal/logs/unequal.txt
lake env lean Gardner/formal/Unequal.lean > Gardner/formal/logs/unequal-arithmetic.txt
