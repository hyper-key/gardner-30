"""Exact marginal obstructions on candidate axis pairs for split (15,15) with equal spans."""
from collections import Counter
from pathlib import Path
from itertools import product
import json
import sys
import time
from axis_matching import pair_test
from clipped_moments import profiles

qs=Counter()
marginal=[]
stage=[]
start=time.process_time()
for line in Path(sys.argv[1]).read_text().splitlines():
    e,mu,mv,t,v=map(int,line.split())
    ur={t+i for i in range(e) if mu>>i&1}|{t+e}
    uc={v+i for i in range(e) if mv>>i&1}|{v+e}
    assert len(ur)==len(uc)==15
    def h(used):
        vals=[2*x-29 for x in used]
        return 21*sum(vals)**2-5*sum(x*x for x in vals)
    assert h(set(range(30))-ur)==h(set(range(30))-uc)
    r=set(range(30))-ur;c=set(range(30))-uc
    quick=pair_test(30,r,c)
    qs['inputs']+=1
    if quick['reason']!='survives':
        qs[quick['reason']]+=1
        continue
    qs['basic_pass']+=1
    stats,options=profiles(30,ur,uc)
    qs['marginal_leaves']+=stats['covers']
    qs['marginal_nodes']+=stats['nodes']
    if options:qs['some_profile']+=1
    opts=[(d,s) for d,s in options if len(set(d))==15 and len(set(s))==15]
    if opts:
        qs['target_profile']+=1
        marginal.append(dict(axis=[e,mu,mv,t,v],profiles=opts))
    stage.append([e,mu,mv,t,v,len(options),len(opts)])
Path('frame30eq_marginals.json').write_text(json.dumps(marginal,separators=(',',':'))+'\n')
Path('frame30eq_stage.json').write_text(json.dumps(stage,separators=(',',':'))+'\n')
print(json.dumps(dict(counts=qs,cpu_s=round(time.process_time()-start,3))))
