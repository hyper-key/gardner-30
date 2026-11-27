"""Generate untrusted arithmetic certificates; Lean checks every certificate.

No residual multiplicity assumption is used. Linear/quadratic separators handle
all but three original leaves; those use exhaustive splits on residual values.
"""
from collections import Counter
from functools import lru_cache
from itertools import product
from pathlib import Path
import gzip
import json

ROOT = Path(__file__).resolve().parents[2]
DEST = Path(__file__).resolve().parent
COUNTS = Counter()


def valid_cut(p, c):
    dkeys,skeys,dm,sm,ds,ss,sq = p
    a,bd,cd,bs,cs = c
    return (all(a*k*k+bd*k+cd >= 0 for k in dkeys)
            and all(a*k*k+bs*k+cs >= 0 for k in skeys)
            and a*sq+bd*ds+cd*dm+bs*ss+cs*sm < 0)


def separator(p):
    dkeys,skeys,dm,sm,ds,ss,sq = p
    for f,(keys,m,s) in enumerate(((dkeys,dm,ds),(skeys,sm,ss))):
        candidates = []
        if not keys and m:
            candidates.append((0,-1))
        if not m and s:
            b = -1 if s > 0 else 1
            candidates.append((b,max((-b*k for k in keys),default=0)))
        if keys:
            candidates.extend(((1,-min(keys)),(-1,max(keys))))
        for b,c in candidates:
            cut = (0,b,c,0,0) if f == 0 else (0,0,0,b,c)
            if valid_cut(p,cut):return cut
    lower=[]
    upper=[]
    for keys,m,s in ((dkeys,dm,ds),(skeys,sm,ss)):
        if keys:
            pairs = list(zip(keys,keys[1:])) or [(keys[0],keys[0])]
            a,b = max(pairs,key=lambda t:(t[0]+t[1])*s-t[0]*t[1]*m)
            lower.append((-(a+b),a*b))
            a,b = min(keys),max(keys)
            upper.append((a+b,-a*b))
        else:
            lower.append((0,0));upper.append((0,0))
    for a,bounds in ((1,lower),(-1,upper)):
        cut=(a,*bounds[0],*bounds[1])
        if valid_cut(p,cut):return cut
    return None


@lru_cache(None)
def arithmetic_proof(p):
    cut=separator(p)
    if cut is not None:
        COUNTS['cut_nodes']+=1
        return ('cut',cut)
    dkeys,skeys,dm,sm,ds,ss,sq=p
    choices=[(len(dkeys),0)] if dm else []
    if sm:choices.append((len(skeys),1))
    assert choices, ('compatible terminal state',p)
    _,family=min(choices)
    keys=skeys if family else dkeys
    assert keys
    children=[]
    for k in keys:
        child=(dkeys,skeys,dm,sm-1,ds,ss-k,sq-k*k) if family else (
            dkeys,skeys,dm-1,sm,ds-k,ss,sq-k*k)
        children.append((k,arithmetic_proof(child)))
    COUNTS['split_nodes']+=1
    return ('S' if family else 'D',tuple(children))


def lean_list(xs):return '['+','.join(map(str,xs))+']'


def lean_proof(p):
    if p[0]=='cut':return '.cut ⟨'+','.join(map(str,p[1]))+'⟩'
    result='.cut ⟨0,0,0,0,0⟩'
    for k,child in reversed(p[1]):
        result=f'if k == ({k}:Int) then {lean_proof(child)} else {result}'
    return '(.split'+p[0]+' (fun k => '+result+'))'


def leaves(header, proof):
    e,u,v,off_r,off_c=header
    unused_r={off_r+i for i in range(e) if u>>i&1}|{off_r+e}
    unused_c={off_c+i for i in range(e) if v>>i&1}|{off_c+e}
    active_r=set(range(30))-unused_r
    active_c=set(range(30))-unused_c
    edges={(r-c,r+c) for r,c in product(unused_r,unused_c)}
    support=(Counter(r-c for r,c in product(active_r,active_c)),
             Counter(r+c for r,c in product(active_r,active_c)))
    forced=({d for d,s in edges if support[1][s]<2},
            {s for d,s in edges if support[0][d]<2})
    first=(2*(sum(active_r)-sum(active_c)),2*(sum(active_r)+sum(active_c)))
    square=4*sum(x*x for axis in (active_r,active_c) for x in axis)
    def walk(node,d,s):
        if node=='Q':return
        if node=='M':
            p=(tuple(sorted(k for k in support[0] if k not in d)),
               tuple(sorted(k for k in support[1] if k not in s)),
               30-2*len(d),30-2*len(s),first[0]-2*sum(d),first[1]-2*sum(s),
               square-2*sum(k*k for k in d)-2*sum(k*k for k in s))
            assert p[2]>=0 and p[3]>=0
            yield p,(sorted(d),sorted(s))
            return
        f,k,yes,no=node
        neighbors={p[1-f] for p in edges if p[f]==k and p[0] not in d and p[1] not in s}
        assert neighbors
        if f==0:
            yield from walk(yes,d|{k},s)
            yield from walk(no,d,s|neighbors)
        else:
            yield from walk(yes,d,s|{k})
            yield from walk(no,d|neighbors,s)
    yield from walk(proof,*forced)


def main():
    out=['import Gardner.kernel.MomentCuts','namespace Gardner.Kernel.MomentData',
         'open MomentCuts','set_option maxRecDepth 20000',
         'set_option maxHeartbeats 1000000000']
    metadata=[]
    for family,stem in ((29,'frame29'),(30,'frame30eq')):
        exact=ROOT/'Gardner'/'exact'
        headers=[tuple(map(int,s.split())) for s in (exact/(stem+'_full.txt')).read_text().splitlines()]
        with gzip.open(exact/(stem+'_certs.json.gz'),'rt') as f:records=json.load(f)
        for header,(reason,proof) in zip(headers,records,strict=True):
            if reason!='survives':continue
            for p,required in leaves(header,proof):
                index=len(metadata)
                cert=arithmetic_proof(p)
                if cert[0]!='cut':COUNTS['original_leaves_needing_splits']+=1
                dkeys,skeys,dm,sm,ds,ss,sq=p
                problem=f'⟨{lean_list(dkeys)},{lean_list(skeys)},{dm},{sm},{ds},{ss},{sq}⟩'
                out.extend([f'def problem{index} : Problem := {problem}',
                    f'def proof{index} : Proof := {lean_proof(cert)}',
                    f'theorem checked{index} : check 12 problem{index} proof{index} = true := by decide +kernel',
                    f'theorem excluded{index} (ds ss : List Int) : ¬ Realizes problem{index} ds ss :=',
                    f'  fun model => check_sound 12 problem{index} proof{index} checked{index} ds ss model'])
                metadata.append(dict(index=index,family=family,axis=header,required=required,problem=p))
    assert len(metadata)==2032
    out.extend(['#print axioms excluded0','#print axioms excluded2031','end Gardner.Kernel.MomentData'])
    (DEST/'MomentData.lean').write_text('\n'.join(out)+'\n')
    (DEST/'moment_cuts.json').write_text(json.dumps(metadata,separators=(',',':'))+'\n')
    context_imports=[]
    for start in range(0,len(metadata),128):
        chunk=start//128
        name=f'MomentContexts{chunk:02d}'
        context_imports.append('import Gardner.kernel.'+name)
        lines=['import Gardner.kernel.MomentData','import Gardner.kernel.PairedResiduals',
               'namespace Gardner.Kernel.MomentContexts','open MomentCuts',
               'set_option maxRecDepth 20000','set_option maxHeartbeats 1000000000']
        for item in metadata[start:start+128]:
            n=item['index']
            e,u,v,off_r,off_c=item['axis']
            unused_r={off_r+i for i in range(e) if u>>i&1}|{off_r+e}
            unused_c={off_c+i for i in range(e) if v>>i&1}|{off_c+e}
            rows=sorted(set(range(30))-unused_r)
            cols=sorted(set(range(30))-unused_c)
            d,s=item['required']
            lines.extend([f'def rows{n} : List Int := {lean_list(rows)}',
                f'def cols{n} : List Int := {lean_list(cols)}',
                f'def requiredD{n} : List Int := {lean_list(d)}',
                f'def requiredS{n} : List Int := {lean_list(s)}',
                f'theorem problem{n}_eq : pairedProblem rows{n} cols{n} requiredD{n} requiredS{n} =',
                f'    MomentData.problem{n} := by rfl',
                f'theorem leaf{n} (q : List (Int × Int))',
                f'    (hr : (q.map Prod.fst).Perm (rows{n}++rows{n}))',
                f'    (hc : (q.map Prod.snd).Perm (cols{n}++cols{n}))',
                f'    (hd : ∀ k ∈ requiredD{n}, (Gardner.Marginal.differences q).count k = 2)',
                f'    (hs : ∀ k ∈ requiredS{n}, (Gardner.Marginal.sums q).count k = 2) : False := by',
                f'  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows{n} cols{n} requiredD{n} requiredS{n}',
                f'    (by decide) hr hc (by decide) (by decide) hd hs',
                f'  rw [problem{n}_eq] at model',
                f'  exact MomentData.excluded{n} ds ss model'])
        lines.extend([f'#print axioms leaf{start}','end Gardner.Kernel.MomentContexts'])
        (DEST/(name+'.lean')).write_text('\n'.join(lines)+'\n')
    (DEST/'MomentContexts.lean').write_text('\n'.join(context_imports)+'\n')
    print('generated',len(metadata),'moment certificates',dict(COUNTS))


if __name__=='__main__':main()
