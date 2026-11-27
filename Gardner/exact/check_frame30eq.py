"""Check written certificates, including H, canonical symmetries and quotas."""
from collections import Counter
import gzip
import json
from pathlib import Path
from check_clipped import Case


def h(unused):
    values=[2*i-29 for i in range(30) if i not in unused]
    return 21*sum(values)**2-5*sum(i*i for i in values)


def check(pairs,records):
    assert len(pairs)==len(records)==11691
    seen=set()
    hist=Counter()
    for (e,u,v,i,j),(kind,cert) in zip(pairs,records,strict=True):
        a=tuple(sorted({i} | {i+k for k in range(e+1) if (u|(1<<e))>>k&1}))
        b=tuple(sorted({j} | {j+k for k in range(e+1) if (v|(1<<e))>>k&1}))
        assert len(a)==len(b)==15 and e==max(a)-min(a)==max(b)-min(b)
        assert all(0<=r<30 for r in a+b) and h(a)==h(b)
        def canonical(x):
            return min(x,tuple(29-v for v in reversed(x)))
        identity=tuple(sorted((canonical(a),canonical(b))))
        assert identity not in seen
        seen.add(identity)
        case=Case(30,a,b)
        if kind=='survives':
            hist.update(case.leaves(cert))
        elif kind=='matching_after_forcing':
            ds,ss,edges=cert
            assert len(set(ds))+len(set(ss))+len(edges)>30
            assert set(ds)<=case.forced[0] and set(ss)<=case.forced[1]
            assert all((d,s) in case.holes and d not in ds and s not in ss for d,s in edges)
            assert len({d for d,s in edges})==len({s for d,s in edges})==len(edges)
        else:
            case.check_quick(kind,cert)
        hist[kind]+=1
    return hist


if __name__=='__main__':
    pairs=[tuple(map(int,s.split())) for s in Path('frame30eq_full.txt').read_text().splitlines()]
    with gzip.open('frame30eq_certs.json.gz','rt') as f: records=json.load(f)
    print('PASS all',len(pairs),'supplied equal-span cases',dict(check(pairs,records)))
    try:
        check(pairs,records[:-1])
    except AssertionError:
        print('PASS missing case rejected')
    else:
        raise AssertionError('accepted missing case')
