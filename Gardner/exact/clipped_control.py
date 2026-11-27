"""Compare the positive control with original geometry, axes and marginals."""
from collections import Counter
import json
from pathlib import Path
import sys
from clipped import axes
from clipped_moments import profiles
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'validation'))
from check import audit

src=json.loads(Path('../construction/witness12.json').read_text())
control,*trials=(json.loads(z) for z in Path('clipped_realize.jsonl').read_text().splitlines())
u=[2,3,5,6,8,9]
assert tuple(u) in axes(12,3)[1]
stats,choices=profiles(12,u,u)
queens=control['queens']
found=(tuple(sorted(r-c for r,c in queens)),tuple(sorted(r+c for r,c in queens)))
assert len(choices)==1 and found in choices and queens==src['queens']
result=audit(control)
assert result['maximal'] and result['count']==12
print(json.dumps(dict(known12=result,profile_count=len(choices),known12_matches_source=True,
                      solver_results=Counter(x['status'] for x in trials),
                      solver_wall_total_s=round(sum(x['wall_s'] for x in trials),3))))
