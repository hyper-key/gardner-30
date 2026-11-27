#!/usr/bin/env bash
# Replay the kernel-checked intermediate results. This does not prove m3(30)=31.
set -euo pipefail
cd "$(dirname "$0")/../.."
logdir="$PWD/Gardner/kernel/logs"
mkdir -p "$logdir" .lake/build/lib/lean/Gardner/{formal,exact,kernel}

lake build GardnerSolution Gardner.formal.Perimeter > "$logdir/base.log" 2>&1
for module in GridFunctional StructureBridge AffineProducts FullMoment; do
    lake env lean -o ".lake/build/lib/lean/Gardner/formal/$module.olean" \
        "Gardner/formal/$module.lean" > "$logdir/$module.log" 2>&1
done
lake env lean -o .lake/build/lib/lean/Gardner/exact/Marginal.olean \
    Gardner/exact/Marginal.lean > "$logdir/Marginal.log" 2>&1
for module in Saturation ConstantLayer Transpose PairedAxes Frames SecondLayer AxisMoments \
        Reflection Reduction MomentCuts ResidualMoments PairedResiduals MomentData; do
    lake env lean -o ".lake/build/lib/lean/Gardner/kernel/$module.olean" \
        "Gardner/kernel/$module.lean" > "$logdir/$module.log" 2>&1
    echo "kernel checked $module"
done

python3 - <<'PY'
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import os
import subprocess

jobs=max(1,int(os.environ.get('GARDNER_KERNEL_JOBS','2')))
def build(i):
    name=f'MomentContexts{i:02d}'
    log=Path('Gardner/kernel/logs')/(name+'.log')
    with log.open('w') as f:
        run=subprocess.run(['lake','env','lean','-j','1','-o',
            f'.lake/build/lib/lean/Gardner/kernel/{name}.olean',
            f'Gardner/kernel/{name}.lean'],stdout=f,stderr=subprocess.STDOUT)
    return name,run.returncode,log
with ThreadPoolExecutor(max_workers=jobs) as pool:
    results=list(pool.map(build,range(16)))
for name,code,log in results:
    if code: print(log.read_text())
    print(name,'exit',code,flush=True)
if any(code!=0 for _,code,_ in results):
    raise SystemExit(1)
PY
lake env lean -o .lake/build/lib/lean/Gardner/kernel/MomentContexts.olean \
    Gardner/kernel/MomentContexts.lean
lake env lean Gardner/kernel/Axioms.lean | tee "$logdir/Axioms.log"
echo 'PASS kernel-checked structural reductions and all 2032 moment leaves.'
echo 'The global profile exclusion is not yet formalized; no unconditional lower31 theorem is claimed.'
