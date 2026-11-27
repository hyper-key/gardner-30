"""Direct small-board calibration of both restricted searches; prints source-free 12 example."""
from collections import Counter
from itertools import combinations, product
import json
from pathlib import Path
import subprocess
import sys
from transplant import extend
from profiles import minimal_covers, profile_options

def valid(q):
    for a,b,c in combinations(q,3):
        if (a[0]==b[0]==c[0] or a[1]==b[1]==c[1]
            or a[0]+a[1]==b[0]+b[1]==c[0]+c[1]
            or a[0]-a[1]==b[0]-b[1]==c[0]-c[1]):
            return False
    return True

def holes(n,q):
    return [p for p in product(range(n),repeat=2) if p not in q and valid(q+(p,))]

def full_orbits(n):
    seen=set()
    for i,j in product(range(n),repeat=2):
        if (i,j) not in seen:
            orbit={(r,c) for a,b in ((i,j),(j,i)) for r in (a,n-1-a) for c in (b,n-1-b)}
            seen |= orbit
            yield sorted(orbit)

def main():
    n=5
    for seed in [(),((0,0),),((0,1),(0,4),(2,2),(1,1))]:
        for height in (1,2):
            full=list(product(range(n),repeat=2))
            answers=Counter()
            for extra in combinations([p for p in full if p not in seed],height):
                group=seed+extra
                if valid(group): answers[len(holes(n,group))]+=1
            _,actual,_,_=extend(seed,n,height)
            assert answers==actual
    print('transplant extensions and hole histograms matched direct checks (6 small cases)')
    for n in [6,8,10]:
        cores=[tuple(o) for o in full_orbits(n) if len(o)==4]
        best=min(len(holes(n,core+extra)) for core in cores for extra in
                 combinations(holes(n,core),2) if valid(core+extra))
        result=subprocess.check_output([sys.argv[1],str(n),'6'],text=True)
        reported=int(result.split('best_holes ')[1].split()[0])
        assert reported==best
        print('D4 core and two extras matched direct optimum',n,6,best)
    n=12
    orbs=list(full_orbits(n))
    for q1,q2 in combinations(orbs,2):
        q=tuple(q1+q2)
        if len(q)==12 and valid(q) and not holes(n,q):
            print('D4 known optimum 12 witness reproduced')
            Path('witness12.json').write_text(json.dumps({'n':12,'queens':sorted(q)})+'\n')
            break
    else:
        raise ValueError('missing eightfold example')
    for m in [5,9,13,15]:
        matches=set()
        covers=list(minimal_covers(m))
        for d,s in covers:
            D=profile_options(m,d,10**6,False)
            S=profile_options(m,s,10**6,True)
            for k,dl in D.items():
                for x,y in product(dl,S.get(2*m*(m*m-1)//3-k,[])):
                    matches.add((tuple(sorted(x.elements())),tuple(sorted(y.elements()))))
        print('even-even subgrid side',2*m,'cover count',len(covers),'moment-profile count',len(matches))
    for f in ['witness10.json','witness12.json','witness18.json','witness26.json','witness31-initial.json']:
        d=json.loads(Path(f).read_text())
        n,q=d['n'],tuple(map(tuple,d['queens']))
        assert len(q)==len(set(q)) and valid(q) and not holes(n,q)
        print('direct triple checker accepts',f,len(q))
    for label, w, expected in [
        ('best 26-seed transplant',json.loads(Path('transplant-result.json').read_text())['best'],31),
        ('best D4-core completion', json.loads(Path('orbit-30.log').read_text().splitlines()[1]),32)]:
        q=tuple(map(tuple,w['queens']))
        assert valid(q) and len(holes(w['n'],q))==expected
        print(label,'has',expected,'addable squares')
if __name__=='__main__': main()
